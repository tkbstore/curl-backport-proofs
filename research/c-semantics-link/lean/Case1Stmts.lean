/-
Case 1: `Curl_pp_readresp`（修正後）の本体から切り出したループの文。
cut.py が GenCase1After.lean から括弧の対応で機械的に切り出したもの。手で編集しない。
使う側では、本体の該当部分と定義の上で一致する（`exact` が展開して照合する）。
-/
import GenCase1After
open CC
open Case1_after

namespace Case1C

def tailStmt : Stmt :=
(Stmt.Ssequence
                                          (Stmt.Scall (some _t'15)
                                            (Expr.Evar _curlx_dyn_len 
                                            (Ty.Tfunction
                                              [(tptr (Ty.Tstruct _dynbuf noattr))]
                                              tulong cc_default))
                                            [(Expr.Eaddrof
                                               (Expr.Efield
                                                 (Expr.Ederef
                                                   (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                   (Ty.Tstruct _pingpong noattr))
                                                 _recvbuf
                                                 (Ty.Tstruct _dynbuf noattr))
                                               (tptr (Ty.Tstruct _dynbuf noattr)))])
                                          (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                              (Expr.Etempvar _t'15 tulong)
                                                              (Expr.Etempvar _length tulong)
                                                              tint)
                                            (Stmt.Ssequence
                                              (Stmt.Scall (some _t'14)
                                                (Expr.Evar _curlx_dyn_len 
                                                (Ty.Tfunction
                                                  [(tptr (Ty.Tstruct _dynbuf noattr))]
                                                  tulong cc_default))
                                                [(Expr.Eaddrof
                                                   (Expr.Efield
                                                     (Expr.Ederef
                                                       (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                       (Ty.Tstruct _pingpong noattr))
                                                     _recvbuf
                                                     (Ty.Tstruct _dynbuf noattr))
                                                   (tptr (Ty.Tstruct _dynbuf noattr)))])
                                              (Stmt.Scall none
                                                (Expr.Evar _curlx_dyn_tail 
                                                (Ty.Tfunction
                                                  [(tptr (Ty.Tstruct _dynbuf noattr)),
                                                   tulong] tint cc_default))
                                                [(Expr.Eaddrof
                                                   (Expr.Efield
                                                     (Expr.Ederef
                                                       (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                       (Ty.Tstruct _pingpong noattr))
                                                     _recvbuf
                                                     (Ty.Tstruct _dynbuf noattr))
                                                   (tptr (Ty.Tstruct _dynbuf noattr))),
                                                 (Expr.Ebinop Binop.Osub
                                                   (Expr.Etempvar _t'14 tulong)
                                                   (Expr.Etempvar _length tulong)
                                                   tulong)]))
                                            (Stmt.Scall none
                                              (Expr.Evar _curlx_dyn_reset 
                                              (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _dynbuf noattr))]
                                                tvoid cc_default))
                                              [(Expr.Eaddrof
                                                 (Expr.Efield
                                                   (Expr.Ederef
                                                     (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                     (Ty.Tstruct _pingpong noattr))
                                                   _recvbuf
                                                   (Ty.Tstruct _dynbuf noattr))
                                                 (tptr (Ty.Tstruct _dynbuf noattr)))])))

def eorIf : Stmt :=
(Stmt.Sifthenelse (Expr.Etempvar _t'13 tbool)
                                            (Stmt.Ssequence
                                              (Stmt.Sassign
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                    (Ty.Tstruct _pingpong noattr))
                                                  _nfinal tulong)
                                                (Expr.Etempvar _length tulong))
                                              (Stmt.Ssequence
                                                (Stmt.Ssequence
                                                  (Stmt.Scall (some _t'12)
                                                    (Expr.Evar _curlx_dyn_len 
                                                    (Ty.Tfunction
                                                      [(tptr (Ty.Tstruct _dynbuf noattr))]
                                                      tulong cc_default))
                                                    [(Expr.Eaddrof
                                                       (Expr.Efield
                                                         (Expr.Ederef
                                                           (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                           (Ty.Tstruct _pingpong noattr))
                                                         _recvbuf
                                                         (Ty.Tstruct _dynbuf noattr))
                                                       (tptr (Ty.Tstruct _dynbuf noattr)))])
                                                  (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                                    (Expr.Etempvar _t'12 tulong)
                                                                    (Expr.Etempvar _length tulong)
                                                                    tint)
                                                    (Stmt.Ssequence
                                                      (Stmt.Scall (some _t'11)
                                                        (Expr.Evar _curlx_dyn_len 
                                                        (Ty.Tfunction
                                                          [(tptr (Ty.Tstruct _dynbuf noattr))]
                                                          tulong cc_default))
                                                        [(Expr.Eaddrof
                                                           (Expr.Efield
                                                             (Expr.Ederef
                                                               (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                               (Ty.Tstruct _pingpong noattr))
                                                             _recvbuf
                                                             (Ty.Tstruct _dynbuf noattr))
                                                           (tptr (Ty.Tstruct _dynbuf noattr)))])
                                                      (Stmt.Sassign
                                                        (Expr.Efield
                                                          (Expr.Ederef
                                                            (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                            (Ty.Tstruct _pingpong noattr))
                                                          _overflow tulong)
                                                        (Expr.Ebinop Binop.Osub
                                                          (Expr.Etempvar _t'11 tulong)
                                                          (Expr.Etempvar _length tulong)
                                                          tulong)))
                                                    (Stmt.Sassign
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                          (Ty.Tstruct _pingpong noattr))
                                                        _overflow tulong)
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint))))
                                                (Stmt.Ssequence
                                                  (Stmt.Ssequence
                                                    (Stmt.Sset _t'17
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                          (Ty.Tstruct _pingpong noattr))
                                                        _nread_resp tulong))
                                                    (Stmt.Sassign
                                                      (Expr.Ederef
                                                        (Expr.Etempvar _size (tptr tulong))
                                                        tulong)
                                                      (Expr.Etempvar _t'17 tulong)))
                                                  (Stmt.Ssequence
                                                    (Stmt.Sassign
                                                      (Expr.Efield
                                                        (Expr.Ederef
                                                          (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                          (Ty.Tstruct _pingpong noattr))
                                                        _nread_resp tulong)
                                                      (Expr.Econst_int (Integers.Int.repr 0) tint))
                                                    (Stmt.Ssequence
                                                      (Stmt.Sassign
                                                        (Expr.Evar _gotbytes tulong)
                                                        (Expr.Econst_int (Integers.Int.repr 0) tint))
                                                      Stmt.Sbreak)))))
                                            Stmt.Sskip)

def nlIf : Stmt :=
(Stmt.Sifthenelse (Expr.Etempvar _nl (tptr tschar))
                            (Stmt.Ssequence
                              (Stmt.Sset _length
                                (Expr.Ebinop Binop.Oadd
                                  (Expr.Ebinop Binop.Osub
                                    (Expr.Etempvar _nl (tptr tschar))
                                    (Expr.Etempvar _line (tptr tschar))
                                    tlong)
                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                  tlong))
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Scall (some _t'9)
                                    (Expr.Evar _memchr (Ty.Tfunction
                                                         [(tptr tvoid), tint,
                                                          tulong]
                                                         (tptr tvoid)
                                                         cc_default))
                                    [(Expr.Etempvar _line (tptr tschar)),
                                     (Expr.Econst_int (Integers.Int.repr 0) tint),
                                     (Expr.Etempvar _length tulong)])
                                  (Stmt.Sifthenelse (Expr.Etempvar _t'9 (tptr tvoid))
                                    (Stmt.Ssequence
                                      (Stmt.Scall none
                                        (Expr.Evar _Curl_failf (Ty.Tfunction
                                                                 [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                                  (tptr tschar)]
                                                                 tvoid
                                                                 { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                         (Expr.Evar ___stringlit_2 (tarray tschar 33))])
                                      (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 8) tint))))
                                    Stmt.Sskip))
                                (Stmt.Ssequence
                                  (Stmt.Scall none
                                    (Expr.Evar _Curl_debug (Ty.Tfunction
                                                             [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                              tint,
                                                              (tptr tschar),
                                                              tulong] tvoid
                                                             cc_default))
                                    [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                     (Expr.Econst_int (Integers.Int.repr 1) tint),
                                     (Expr.Etempvar _line (tptr tschar)),
                                     (Expr.Etempvar _length tulong)])
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Scall (some _t'10)
                                        (Expr.Evar _Curl_client_write 
                                        (Ty.Tfunction
                                          [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                           tint, (tptr tschar), tulong] tint
                                          cc_default))
                                        [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                         (Expr.Ebinop Binop.Oshl
                                           (Expr.Econst_int (Integers.Int.repr 1) tint)
                                           (Expr.Econst_int (Integers.Int.repr 1) tint)
                                           tint),
                                         (Expr.Etempvar _line (tptr tschar)),
                                         (Expr.Etempvar _length tulong)])
                                      (Stmt.Sset _result
                                        (Expr.Etempvar _t'10 tint)))
                                    (Stmt.Ssequence
                                      (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                        (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                                        Stmt.Sskip)
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'18
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                  (Ty.Tstruct _pingpong noattr))
                                                _endofresp
                                                (tptr (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                         (tptr (Ty.Tstruct _connectdata noattr)),
                                                         (tptr tschar),
                                                         tulong, (tptr tint)]
                                                        tbool cc_default))))
                                            (Stmt.Scall (some _t'13)
                                              (Expr.Etempvar _t'18 (tptr 
                                              (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                 (tptr (Ty.Tstruct _connectdata noattr)),
                                                 (tptr tschar), tulong,
                                                 (tptr tint)] tbool
                                                cc_default)))
                                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                               (Expr.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr))),
                                               (Expr.Etempvar _line (tptr tschar)),
                                               (Expr.Etempvar _length tulong),
                                               (Expr.Etempvar _code (tptr tint))]))
                                          eorIf)
                                        tailStmt))))))
                            (Stmt.Ssequence
                              (Stmt.Sassign
                                (Expr.Efield
                                  (Expr.Ederef
                                    (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                    (Ty.Tstruct _pingpong noattr)) _overflow
                                  tulong)
                                (Expr.Econst_int (Integers.Int.repr 0) tint))
                              Stmt.Sbreak))

def innerBody : Stmt :=
(Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'6)
                            (Expr.Evar _curlx_dyn_ptr (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _dynbuf noattr))]
                                                        (tptr tschar)
                                                        cc_default))
                            [(Expr.Eaddrof
                               (Expr.Efield
                                 (Expr.Ederef
                                   (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                   (Ty.Tstruct _pingpong noattr)) _recvbuf
                                 (Ty.Tstruct _dynbuf noattr))
                               (tptr (Ty.Tstruct _dynbuf noattr)))])
                          (Stmt.Sset _line
                            (Expr.Etempvar _t'6 (tptr tschar))))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Scall (some _t'7)
                                (Expr.Evar _curlx_dyn_len (Ty.Tfunction
                                                            [(tptr (Ty.Tstruct _dynbuf noattr))]
                                                            tulong
                                                            cc_default))
                                [(Expr.Eaddrof
                                   (Expr.Efield
                                     (Expr.Ederef
                                       (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                       (Ty.Tstruct _pingpong noattr))
                                     _recvbuf (Ty.Tstruct _dynbuf noattr))
                                   (tptr (Ty.Tstruct _dynbuf noattr)))])
                              (Stmt.Scall (some _t'8)
                                (Expr.Evar _memchr (Ty.Tfunction
                                                     [(tptr tvoid), tint,
                                                      tulong] (tptr tvoid)
                                                     cc_default))
                                [(Expr.Etempvar _line (tptr tschar)),
                                 (Expr.Econst_int (Integers.Int.repr 10) tint),
                                 (Expr.Etempvar _t'7 tulong)]))
                            (Stmt.Sset _nl (Expr.Etempvar _t'8 (tptr tvoid))))
                          nlIf))

def nfinIf : Stmt :=
(Stmt.Sifthenelse (Expr.Etempvar _t'27 tulong)
                      (Stmt.Ssequence
                        (Stmt.Ssequence
                          (Stmt.Scall (some _t'1)
                            (Expr.Evar _curlx_dyn_len (Ty.Tfunction
                                                        [(tptr (Ty.Tstruct _dynbuf noattr))]
                                                        tulong cc_default))
                            [(Expr.Eaddrof
                               (Expr.Efield
                                 (Expr.Ederef
                                   (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                   (Ty.Tstruct _pingpong noattr)) _recvbuf
                                 (Ty.Tstruct _dynbuf noattr))
                               (tptr (Ty.Tstruct _dynbuf noattr)))])
                          (Stmt.Sset _full (Expr.Etempvar _t'1 tulong)))
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Sset _t'28
                              (Expr.Efield
                                (Expr.Ederef
                                  (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                  (Ty.Tstruct _pingpong noattr)) _nfinal
                                tulong))
                            (Stmt.Scall none
                              (Expr.Evar _curlx_dyn_tail (Ty.Tfunction
                                                           [(tptr (Ty.Tstruct _dynbuf noattr)),
                                                            tulong] tint
                                                           cc_default))
                              [(Expr.Eaddrof
                                 (Expr.Efield
                                   (Expr.Ederef
                                     (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                     (Ty.Tstruct _pingpong noattr)) _recvbuf
                                   (Ty.Tstruct _dynbuf noattr))
                                 (tptr (Ty.Tstruct _dynbuf noattr))),
                               (Expr.Ebinop Binop.Osub
                                 (Expr.Etempvar _full tulong)
                                 (Expr.Etempvar _t'28 tulong) tulong)]))
                          (Stmt.Sassign
                            (Expr.Efield
                              (Expr.Ederef
                                (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                (Ty.Tstruct _pingpong noattr)) _nfinal
                              tulong)
                            (Expr.Econst_int (Integers.Int.repr 0) tint))))
                      Stmt.Sskip)

def gotChk : Stmt :=
(Stmt.Ssequence
                                    (Stmt.Sset _t'25
                                      (Expr.Evar _gotbytes tulong))
                                    (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                        (Expr.Etempvar _t'25 tulong)
                                                        tint)
                                      (Stmt.Ssequence
                                        (Stmt.Ssequence
                                          (Stmt.Scall (some _t'4)
                                            (Expr.Evar ___errno_location 
                                            (Ty.Tfunction [] (tptr tint)
                                              cc_default)) [])
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'26
                                              (Expr.Ederef
                                                (Expr.Etempvar _t'4 (tptr tint))
                                                tint))
                                            (Stmt.Scall none
                                              (Expr.Evar _Curl_failf 
                                              (Ty.Tfunction
                                                [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                 (tptr tschar)] tvoid
                                                { cc_vararg := (some 2), cc_unproto := false, cc_structret := false }))
                                              [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                               (Expr.Evar ___stringlit_1 (tarray tschar 36)),
                                               (Expr.Etempvar _t'26 tint)])))
                                        (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 56) tint))))
                                      Stmt.Sskip))

def hbcUpd : Stmt :=
(Stmt.Ssequence
                                          (Stmt.Sset _t'22
                                            (Expr.Efield
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                  (Ty.Tstruct _Curl_easy noattr))
                                                _req
                                                (Ty.Tstruct _SingleRequest noattr))
                                              _headerbytecount tuint))
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'23
                                              (Expr.Evar _gotbytes tulong))
                                            (Stmt.Sassign
                                              (Expr.Efield
                                                (Expr.Efield
                                                  (Expr.Ederef
                                                    (Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr)))
                                                    (Ty.Tstruct _Curl_easy noattr))
                                                  _req
                                                  (Ty.Tstruct _SingleRequest noattr))
                                                _headerbytecount tuint)
                                              (Expr.Ebinop Binop.Oadd
                                                (Expr.Etempvar _t'22 tuint)
                                                (Expr.Ecast
                                                  (Expr.Etempvar _t'23 tulong)
                                                  tuint) tuint))))

def nrUpd : Stmt :=
(Stmt.Ssequence
                                          (Stmt.Sset _t'20
                                            (Expr.Efield
                                              (Expr.Ederef
                                                (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                (Ty.Tstruct _pingpong noattr))
                                              _nread_resp tulong))
                                          (Stmt.Ssequence
                                            (Stmt.Sset _t'21
                                              (Expr.Evar _gotbytes tulong))
                                            (Stmt.Sassign
                                              (Expr.Efield
                                                (Expr.Ederef
                                                  (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                  (Ty.Tstruct _pingpong noattr))
                                                _nread_resp tulong)
                                              (Expr.Ebinop Binop.Oadd
                                                (Expr.Etempvar _t'20 tulong)
                                                (Expr.Etempvar _t'21 tulong)
                                                tulong))))

def readStmt : Stmt :=
(Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Scall (some _t'3)
                                (Expr.Evar _pingpong_read (Ty.Tfunction
                                                            [(tptr (Ty.Tstruct _Curl_easy noattr)),
                                                             tschar,
                                                             (tptr tschar),
                                                             tulong,
                                                             (tptr tulong)]
                                                            tint cc_default))
                                [(Expr.Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))),
                                 (Expr.Etempvar _sockindex tschar),
                                 (Expr.Evar _buffer (tarray tschar 900)),
                                 (Expr.Esizeof (tarray tschar 900) tulong),
                                 (Expr.Eaddrof (Expr.Evar _gotbytes tulong)
                                   (tptr tulong))])
                              (Stmt.Sset _result (Expr.Etempvar _t'3 tint)))
                            (Stmt.Ssequence
                              (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                                  (Expr.Etempvar _result tint)
                                                  (Expr.Econst_int (Integers.Int.repr 81) tint)
                                                  tint)
                                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                Stmt.Sskip)
                              (Stmt.Ssequence
                                (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                  (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                                  Stmt.Sskip)
                                (Stmt.Ssequence
                                  gotChk
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'24
                                          (Expr.Evar _gotbytes tulong))
                                        (Stmt.Scall (some _t'5)
                                          (Expr.Evar _curlx_dyn_addn 
                                          (Ty.Tfunction
                                            [(tptr (Ty.Tstruct _dynbuf noattr)),
                                             (tptr tvoid), tulong] tint
                                            cc_default))
                                          [(Expr.Eaddrof
                                             (Expr.Efield
                                               (Expr.Ederef
                                                 (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                                                 (Ty.Tstruct _pingpong noattr))
                                               _recvbuf
                                               (Ty.Tstruct _dynbuf noattr))
                                             (tptr (Ty.Tstruct _dynbuf noattr))),
                                           (Expr.Evar _buffer (tarray tschar 900)),
                                           (Expr.Etempvar _t'24 tulong)]))
                                      (Stmt.Sset _result
                                        (Expr.Etempvar _t'5 tint)))
                                    (Stmt.Ssequence
                                      (Stmt.Sifthenelse (Expr.Etempvar _result tint)
                                        (Stmt.Sreturn (some (Expr.Etempvar _result tint)))
                                        Stmt.Sskip)
                                      (Stmt.Ssequence
                                        hbcUpd
                                        nrUpd)))))))

def ovfIf : Stmt :=
(Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                          (Expr.Etempvar _t'19 tulong) tint)
                        (Stmt.Ssequence
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Sset _t'2 (Expr.Etempvar _maxloops tint))
                              (Stmt.Sset _maxloops
                                (Expr.Ebinop Binop.Osub
                                  (Expr.Etempvar _t'2 tint)
                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                  tint)))
                            (Stmt.Sifthenelse (Expr.Eunop Unop.Onotbool
                                                (Expr.Etempvar _t'2 tint)
                                                tint)
                              (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))
                              Stmt.Sskip))
                          readStmt)
                        Stmt.Sskip)

def outerBody : Stmt :=
(Stmt.Ssequence
                (Stmt.Sassign (Expr.Evar _gotbytes tulong)
                  (Expr.Econst_int (Integers.Int.repr 0) tint))
                (Stmt.Ssequence
                  (Stmt.Ssequence
                    (Stmt.Sset _t'27
                      (Expr.Efield
                        (Expr.Ederef
                          (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                          (Ty.Tstruct _pingpong noattr)) _nfinal tulong))
                    nfinIf)
                  (Stmt.Ssequence
                    (Stmt.Ssequence
                      (Stmt.Sset _t'19
                        (Expr.Efield
                          (Expr.Ederef
                            (Expr.Etempvar _pp (tptr (Ty.Tstruct _pingpong noattr)))
                            (Ty.Tstruct _pingpong noattr)) _overflow tulong))
                      ovfIf)
                    (Stmt.Sloop innerBody Stmt.Sskip))))

def outerCond : Stmt :=
(Stmt.Ssequence
                (Stmt.Sset _t'16 (Expr.Evar _gotbytes tulong))
                (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                    (Expr.Etempvar _t'16 tulong)
                                    (Expr.Esizeof (tarray tschar 900) tulong)
                                    tint)
                  Stmt.Sskip
                  Stmt.Sbreak))

end Case1C
