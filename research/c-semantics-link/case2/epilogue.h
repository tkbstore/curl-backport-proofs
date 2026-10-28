/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それらを参照するだけの大域変数を1つ置く。関数の宣言と本体には触れない。
 * PROTOCOL §4 の「許す変更」に無い変更なので、RESULTS に逸脱として記録する（Case 5 と同じ）。
 */
void *const case2_keep[] = {
  (void *)url_match_auth_nego, (void *)url_attach_existing
};
