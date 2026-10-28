/-
Case 5（CURL-CVE-2026-86411）: C の意味論の上での P1・P0（PROTOCOL §5）。

- `Case5After.ssl_use_after` / `Case5Before.ssl_use_before` / `Case5Config.ssl_config_eq`:
  curl の C 関数（clightgen が出した Clight の構文木）が、H5 のモデルの関数と同じ値を返す
- ここでは、それを H5 の定理（`H5.Case5.P1`・`H5.Case5.P0` の反例）と合わせる

外部関数（`Curl_conn_is_ssl`・`Curl_ssl_conn_config_match`）の振る舞いは、仕様を満たすことを仮定する
（`hSsl`・`hCfg`）。仕様は「`conn` について決まった真偽値を返し、メモリを変えない」で、値は任意。
-/
import Case5After
import Case5Before
import Case5Config
import Case5Witness
open CC CC.Sep CC.HProp

set_option maxRecDepth 20000

namespace Case5C

/-- 修正後の2つの関数の戻り値を合わせた再利用の判定は、H5 の `after` と同じ。 -/
theorem after_eq (x : H5.Case5.Input) :
    H5.Case5.after x = (H5.Case5.sslUseA x && H5.Case5.sslConfig x) := rfl

theorem before_eq (x : H5.Case5.Input) :
    H5.Case5.before x = (H5.Case5.sslUseB x && H5.Case5.sslConfig x) := rfl

/-- **P1（C）: 修正後の C 関数は、SSL の設定が一致しない TLS 接続の再利用を認めない。**

    `url_match_ssl_use` と `url_match_ssl_config` は、それぞれ H5 のモデルの `sslUseA`・`sslConfig`
    を返す（前の2つの連言）。接続を再利用するのは両方が真のとき（curl の `url_match_conn`）なので、
    再利用の判定は H5 の `after` に等しく、`inherits` は偽になる（3つ目の連言）。 -/
theorem P1_C (ge : CGenv) (c : Ctx) (ssl cfg : Bool)
    (hcenv : ge.genv_cenv = Case5_after.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true)
    (bSsl bCfg bGpf : Block) (fdSsl fdCfg : FunDef)
    (hsSsl : Genv.findSymbol ge.genv_genv Case5_after._Curl_conn_is_ssl = some bSsl)
    (hsCfg : Genv.findSymbol ge.genv_genv Case5_after._Curl_ssl_conn_config_match = some bCfg)
    (hsGpf : Genv.findSymbol ge.genv_genv Case5_after._get_protocol_family = some bGpf)
    (hfSsl : FuncPtr ge bSsl fdSsl) (hfCfg : FuncPtr ge bCfg fdCfg)
    (hfGpf : FuncPtr ge bGpf (.Internal Case5_after.f_get_protocol_family))
    (htySsl : typeOfFundef fdSsl
      = .Tfunction (sslSpec c ssl).tyargs (sslSpec c ssl).tyres (sslSpec c ssl).cc)
    (htyCfg : typeOfFundef fdCfg
      = .Tfunction (cfgSpec c cfg).tyargs (cfgSpec c cfg).tyres (cfgSpec c cfg).cc)
    (hSsl : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdSsl (sslSpec c ssl) vs)
    (hCfg : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c cfg) vs) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case5_after.f_url_match_ssl_use)
              (useSpecA c ssl cfg) vs)
    ∧ (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case5_after.f_url_match_ssl_config)
              (configSpec c ssl cfg) vs)
    ∧ H5.Case5.inherits (input c ssl cfg)
        (H5.Case5.sslUseA (input c ssl cfg) && H5.Case5.sslConfig (input c ssl cfg)) = false :=
  ⟨ssl_use_after ge c ssl cfg hcenv hpr bSsl bCfg bGpf fdSsl fdCfg hsSsl hsCfg hsGpf hfSsl hfCfg
     hfGpf htySsl htyCfg hSsl hCfg,
   ssl_config_eq ge c ssl cfg hcenv hpr bCfg fdCfg hsCfg hfCfg htyCfg hCfg,
   (after_eq _) ▸ H5.Case5.P1 (input c ssl cfg)⟩

/-- **P0（C）: 修正前の C 関数には、脆弱性が起きる入力がある。**

    具体的なメモリ `mW` の上の値 `cW`（ftp:// の要求、設定の違う FTPS の接続）で、
    `Curl_conn_is_ssl` が真、`Curl_ssl_conn_config_match` が偽を返すとき:
    - 前提 `H cW` を満たすヒープが `mW` の上に実在する（仕様が空虚でない）
    - 修正前の `url_match_ssl_use` と `url_match_ssl_config` は、それぞれ `sslUseB`・`sslConfig` を返す
    - その論理積（再利用の判定）は真で、`inherits` が真になる -/
theorem P0_C :
    ∃ (c : Ctx) (ssl cfg : Bool),
      (∃ hp m, H c hp ∧ Heap.Agrees hp m)
      ∧ permOrder c.pm .Readable = true
      ∧ H5.Case5.inherits (input c ssl cfg)
          (H5.Case5.sslUseB (input c ssl cfg) && H5.Case5.sslConfig (input c ssl cfg)) = true
      ∧ ∀ (ge : CGenv) (bSsl bCfg bGpf : Block) (fdSsl fdCfg : FunDef),
          ge.genv_cenv = Case5_before.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv Case5_before._Curl_conn_is_ssl = some bSsl →
          Genv.findSymbol ge.genv_genv Case5_before._Curl_ssl_conn_config_match = some bCfg →
          Genv.findSymbol ge.genv_genv Case5_before._get_protocol_family = some bGpf →
          FuncPtr ge bSsl fdSsl → FuncPtr ge bCfg fdCfg →
          FuncPtr ge bGpf (.Internal Case5_before.f_get_protocol_family) →
          typeOfFundef fdSsl
            = .Tfunction (sslSpec c ssl).tyargs (sslSpec c ssl).tyres (sslSpec c ssl).cc →
          typeOfFundef fdCfg
            = .Tfunction (cfgSpec c cfg).tyargs (cfgSpec c cfg).tyres (cfgSpec c cfg).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdSsl (sslSpec c ssl) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c cfg) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case5_before.f_url_match_ssl_use)
                    (useSpecB c ssl cfg) vs)
          ∧ (∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
                    (.Internal Case5_before.f_url_match_ssl_config) (configSpec c ssl cfg) vs) := by
  obtain ⟨hp, hH, hag⟩ := H_cW_satisfiable
  refine ⟨cW, true, false, ⟨hp, mW, hH, hag⟩, rfl, ?_, ?_⟩
  · rw [← before_eq, input_cW]
    rfl
  · intro ge bSsl bCfg bGpf fdSsl fdCfg hcenv hsSsl hsCfg hsGpf hfSsl hfCfg hfGpf htySsl htyCfg
      hSsl hCfg
    have hcenv' : ge.genv_cenv = Case5_after.prog.prog_comp_env := hcenv.trans cenv_same
    exact ⟨ssl_use_before ge cW true false hcenv rfl bSsl bGpf fdSsl hsSsl hsGpf hfSsl hfGpf
             htySsl hSsl,
           ssl_config_eq ge cW true false hcenv' rfl bCfg fdCfg hsCfg hfCfg htyCfg hCfg⟩

end Case5C

/-! ## 依存する公理（PROTOCOL §5: Lean の標準の3つと、Certora/clean が宣言する公理、自分で置いた公理だけ） -/
#print axioms Case5C.P1_C
#print axioms Case5C.P0_C
#print axioms Case5C.ssl_use_after
#print axioms Case5C.ssl_use_before
#print axioms Case5C.ssl_config_eq
#print axioms Case5C.H_cW_satisfiable
