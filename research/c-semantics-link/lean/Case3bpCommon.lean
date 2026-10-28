/-
Case 3 のバックポート（research/backport-proof/PROTOCOL.md）: curl 8.14.1 の構造体のレイアウト。

局所変数の所有と解放（`Locs`・`ret_locs` など）は `Case3Common` のものをそのまま使う。
ここでは、8.14.1 の前置き（`case3bp/prelude.h`）で変わった構造体のレイアウトだけを、
生成された composite の環境から `decide` で確かめる。
-/
import GenCase3bpAfter
import GenCase3bpBefore
import Case3Common
open CC CC.Sep CC.HProp

set_option maxRecDepth 20000

namespace Case3bpC

def coOf (id : Ident) : Composite :=
  match Case3bp_after.prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_conn : Case3bp_after.prog.prog_comp_env.get Case3bp_after._tftp_conn
    = some (coOf Case3bp_after._tftp_conn) := rfl
theorem co_easy : Case3bp_after.prog.prog_comp_env.get Case3bp_after._Curl_easy
    = some (coOf Case3bp_after._Curl_easy) := rfl
theorem co_us : Case3bp_after.prog.prog_comp_env.get Case3bp_after._UrlState
    = some (coOf Case3bp_after._UrlState) := rfl

/-- 8.14.1 では `data` が `state`・`error`・`event` の後ろ（16）にある（上流の修正前後では 160）。 -/
theorem off_data : fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._data
    (coOf Case3bp_after._tftp_conn).co_members = .OK (16, .Full) := by decide
/-- `struct Curl_easy` の先頭に `conn` が入るので、`state` は 24（上流では 16）。 -/
theorem off_state : fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._state
    (coOf Case3bp_after._Curl_easy).co_members = .OK (24, .Full) := by decide
theorem off_upload : fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._upload
    (coOf Case3bp_after._UrlState).co_members = .OK (16, .Bits .I32 .Unsigned 1 1) := by decide

/-- バックポートの前と後で、composite の環境は同じ（前置きが同じため）。 -/
theorem cenv_same : Case3bp_before.prog.prog_comp_env = Case3bp_after.prog.prog_comp_env := rfl

theorem co_pkt : Case3bp_after.prog.prog_comp_env.get Case3bp_after._tftp_packet
    = some (coOf Case3bp_after._tftp_packet) := rfl

/-- `struct tftp_conn` のフィールド（名前・オフセット）。8.14.1 には `remote_pinned` が無い。 -/
theorem off_conn :
    fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._event (coOf Case3bp_after._tftp_conn).co_members = .OK (8, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._sockfd (coOf Case3bp_after._tftp_conn).co_members = .OK (24, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._retries (coOf Case3bp_after._tftp_conn).co_members = .OK (28, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._remote_addr (coOf Case3bp_after._tftp_conn).co_members = .OK (48, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._remote_addrlen (coOf Case3bp_after._tftp_conn).co_members = .OK (176, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._rbytes (coOf Case3bp_after._tftp_conn).co_members = .OK (180, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._sbytes (coOf Case3bp_after._tftp_conn).co_members = .OK (184, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._blksize (coOf Case3bp_after._tftp_conn).co_members = .OK (192, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._block (coOf Case3bp_after._tftp_conn).co_members = .OK (200, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._rpacket (coOf Case3bp_after._tftp_conn).co_members = .OK (208, .Full)
    ∧ fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._spacket (coOf Case3bp_after._tftp_conn).co_members = .OK (216, .Full) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem off_pdata : fieldOffset Case3bp_after.prog.prog_comp_env Case3bp_after._data
    (coOf Case3bp_after._tftp_packet).co_members = .OK (0, .Full) := by decide

end Case3bpC
