/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それを参照するだけの大域変数を置く。関数の宣言と本体には触れない（case3/epilogue.h と同じ）。
 */
CURLcode (*const deb2026_3783_keep)(struct Curl_easy *, struct connectdata *,
                                    struct auth *, const char *, const char *,
                                    bool) = output_auth_headers;
