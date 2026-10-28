/*
 * CompCert は参照されない static 関数を変換時に消す（cparser/Cleanup.ml）。
 * 対象の関数を残すため、それを参照するだけの大域変数を置く。関数の宣言と本体には触れない（case3/epilogue.h と同じ）。
 * 戻り値の型は版で違う（上流は bool、8.14.1 は int）。
 */
#ifdef SIDE_U
bool (*const deb2026_8924_keep)(struct Curl_easy *, const struct Cookie *, const char *) =
  is_public_suffix;
#else
int (*const deb2026_8924_keep)(struct Curl_easy *, struct Cookie *, const char *) = is_public_suffix;
#endif
