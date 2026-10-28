/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それを参照するだけの大域変数を置く。関数の宣言と本体には触れない。
 * C1 の Case 2・3・5 と同じ逸脱。
 */
CURLcode (*const deb2026_3805_keep)(struct Curl_easy *, struct smb_conn *,
                                    struct smb_request *) = smb_parse_url_path;
