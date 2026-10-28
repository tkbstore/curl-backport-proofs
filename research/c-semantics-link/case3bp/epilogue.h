/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それらを参照するだけの大域変数を置く。関数の宣言と本体には触れない。
 * Case 5・2 と同じ逸脱（RESULTS に記録済みのもの）。
 */
CURLcode (*const case3bp_keep_ev[])(struct tftp_conn *, tftp_event_t) = {
  tftp_tx, tftp_send_first
};
CURLcode (*const case3bp_keep_rp)(struct Curl_easy *, struct tftp_conn *) =
  tftp_receive_packet;
