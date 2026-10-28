/-
Case 2: `url_attach_existing` の証明の部品。

- 構造体のレイアウト（`match` は 48 バイトのローカル変数）
- `Mloc`: `match` の所有を、書き込むフィールドごとの区画に分けたもの
- 外部関数の仕様（`memset` は C の標準どおり、`Curl_cpool_find` は前提に「want のビットの値」を要求する）
-/
import Case2Common
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr bitOf)

set_option maxRecDepth 20000

namespace Case2C

/-! ## レイアウト -/

theorem co_scheme2 : prog.prog_comp_env.get _Curl_scheme = some (coOf _Curl_scheme) := rfl
theorem co_auth : prog.prog_comp_env.get _auth = some (coOf _auth) := rfl
theorem co_ud : prog.prog_comp_env.get _UserDefined = some (coOf _UserDefined) := rfl

theorem sizeof_match : sizeof prog.prog_comp_env (Ty.Tstruct _url_conn_match noattr) = 48 := by
  decide

theorem off_set2 :
    fieldOffset prog.prog_comp_env _set (coOf _Curl_easy).co_members = .OK (0, .Full) := by decide
theorem off_authhost :
    fieldOffset prog.prog_comp_env _authhost (coOf _UrlState).co_members = .OK (8, .Full) := by
  decide
theorem off_want32 :
    fieldOffset prog.prog_comp_env _want (coOf _auth).co_members = .OK (0, .Full) := by decide
theorem off_use_ssl :
    fieldOffset prog.prog_comp_env _use_ssl (coOf _UserDefined).co_members = .OK (0, .Full) := by
  decide
theorem off_scheme2 :
    fieldOffset prog.prog_comp_env _scheme (coOf _connectdata).co_members = .OK (16, .Full) := by
  decide
theorem off_destination :
    fieldOffset prog.prog_comp_env _destination (coOf _connectdata).co_members
      = .OK (24, .Full) := by decide
theorem off_protocol2 :
    fieldOffset prog.prog_comp_env _protocol (coOf _Curl_scheme).co_members = .OK (0, .Full) := by
  decide
theorem off_mdata :
    fieldOffset prog.prog_comp_env _data (coOf _url_conn_match).co_members = .OK (8, .Full) := by
  decide
theorem off_mneedle :
    fieldOffset prog.prog_comp_env _needle (coOf _url_conn_match).co_members = .OK (16, .Full) := by
  decide
theorem off_now :
    fieldOffset prog.prog_comp_env _now (coOf _url_conn_match).co_members = .OK (24, .Full) := by
  decide
theorem off_mm :
    fieldOffset prog.prog_comp_env _may_multiplex (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned 0 1) := by decide
theorem off_reqtls :
    fieldOffset prog.prog_comp_env _require_tls (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned 4 1) := by decide
theorem off_maytls :
    fieldOffset prog.prog_comp_env _may_tls (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned 3 1) := by decide
theorem off_waitpipe :
    fieldOffset prog.prog_comp_env _wait_pipe (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned 5 1) := by decide

/-! ## `match` の所有 -/

def zeroByte : MemVal := .Byte (Integers.Byte.repr 0)

/-- `match` の 48 バイトを、書き込むフィールドごとに分けたもの。
    found(0) ・ data(8) ・ needle(16) ・ now(24, 16 バイト) ・ ビットの単位(40) ・ 詰め物(44, 4 バイト)。 -/
def Mloc (b : Block) (vf vd vn : Val) (nowB : List MemVal) (w : Integers.Int) (pad : List MemVal) :
    HProp :=
  mapsto Mptr .Freeable b 0 vf ∗
  (mapsto Mptr .Freeable b 8 vd ∗
  (mapsto Mptr .Freeable b 16 vn ∗
  (bytesPtsTo b .Freeable 24 nowB ∗
  (mapsto .Mint32 .Freeable b 40 (.Vint w) ∗
   bytesPtsTo b .Freeable 44 pad))))

theorem encode_zero_ptr : encodeVal Mptr (.Vlong (Integers.Int64.repr 0)) = List.replicate 8 zeroByte := by
  decide
theorem encode_zero_32 : encodeVal .Mint32 (.Vint (Integers.Int.repr 0)) = List.replicate 4 zeroByte := by
  decide

/-- **memset の直後**: 48 バイトの 0 は、どのフィールドも 0 の `Mloc` と同じ。 -/
theorem zeros_Mloc (b : Block) :
    bytesPtsTo b .Freeable 0 (List.replicate 48 zeroByte)
      = Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vlong (Integers.Int64.repr 0))
          (.Vlong (Integers.Int64.repr 0)) (List.replicate 16 zeroByte) (Integers.Int.repr 0)
          (List.replicate 4 zeroByte) := by
  unfold Mloc
  rw [mapsto_eq_bytes (by decide), mapsto_eq_bytes (by decide), mapsto_eq_bytes (by decide),
    mapsto_eq_bytes (by decide), encode_zero_ptr, encode_zero_32]
  rw [show List.replicate 48 zeroByte
        = List.replicate 8 zeroByte ++ (List.replicate 8 zeroByte ++ (List.replicate 8 zeroByte
          ++ (List.replicate 16 zeroByte ++ (List.replicate 4 zeroByte
          ++ List.replicate 4 zeroByte)))) from by decide]
  rw [bytesPtsTo_append, bytesPtsTo_append, bytesPtsTo_append, bytesPtsTo_append,
    bytesPtsTo_append]
  simp only [List.length_replicate]
  rw [show (0 : _root_.Int) + ((8 : Nat) : _root_.Int) = 8 from rfl,
    show (8 : _root_.Int) + ((8 : Nat) : _root_.Int) = 16 from rfl,
    show (16 : _root_.Int) + ((8 : Nat) : _root_.Int) = 24 from rfl,
    show (24 : _root_.Int) + ((16 : Nat) : _root_.Int) = 40 from rfl,
    show (40 : _root_.Int) + ((4 : Nat) : _root_.Int) = 44 from rfl]

end Case2C
