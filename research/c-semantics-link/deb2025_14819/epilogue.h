/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それを参照するだけの大域変数を置く。関数の宣言と本体には触れない。
 * C1 の Case 2・3・5 と同じ逸脱。修正の前後で引数の数が違うので、型は void * にした。
 */
void *const deb2025_14819_keep = (void *)ossl_cached_x509_store_different;
