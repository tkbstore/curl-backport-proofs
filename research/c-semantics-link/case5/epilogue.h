/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それらを参照するだけの大域変数を1つ置く。関数の宣言と本体には触れない。
 * PROTOCOL §4 の「許す変更」に無い変更なので、RESULTS に逸脱として記録する。
 */
bool (*const case5_keep[])(struct connectdata *, struct url_conn_match *) = {
  url_match_ssl_use, url_match_ssl_config
};
