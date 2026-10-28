/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それを参照するだけの大域変数を1つ置く。関数の宣言と本体には触れない。
 * C1 の Case 5 と同じ逸脱（PROTOCOL §4 の「許す変更」に無い）。
 */
bool (*const deb_keep)(const struct proxy_info *, const struct proxy_info *) = DEB_KEEP;
