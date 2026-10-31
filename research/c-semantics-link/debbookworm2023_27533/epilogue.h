/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それを参照するだけの大域変数を置く。関数の宣言と本体には触れない。
 * debbookworm2025_14819/epilogue.h と同じ逸脱。str_is_nonascii は check_telnet_options から呼ばれるので残る。
 */
void *const debbookworm2023_27533_keep = (void *)check_telnet_options;
