/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それを参照するだけの大域変数を1つ置く。関数の宣言と本体には触れない。
 * PROTOCOL §4 の「許す変更」に無い変更（Case 5・2 と同じ逸脱）。
 */
void *const deb2026_1965_keep[] = { (void *)url_match_auth_nego };
