/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それらを参照するだけの大域変数を1つ置く。関数の宣言と本体には触れない（Case 5 と同じ逸脱）。
 */
void *const deb2026_8286_keep[] = {
  (void *)url_match_ssl_use, (void *)url_match_ssl_config
};
