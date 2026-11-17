(* c8f_defs.ml (vortex-chain C8f, Claude Opus 5.5, 2026-11-15): the two C8f definitions, text identical to c8f.spec. *)
let va1_film_bytes_s = new_definition
 `va1_film_bytes_s (m0:int64->byte) (m:int64->byte) <=>
    !a. a < 4194304 /\ ~(16288 <= a /\ a < 16384) /\ ~(1966080 <= a /\ a < 2039808)
        ==> read (bytes8 (word a)) m = read (bytes8 (word a)) m0`;;
let va1_clk = new_definition
 `va1_clk (a0:int32) (a1:int32) (a2:int32) (sg:num->int32) =
    va1_put 278528 208896
      (\w. if w < 2048 then word 251658 else if w < 4096 then va1_rbinit_b (va1_ptbl a0 a1 a2 (sg 66)) (w - 2048)
           else if w < 10240 then word 0 else if w < 12288 then va1_zpseed_b (\k. sg (64 + k)) (w - 10240) else word 0)
     (va1_put 12288 262144 (va1_ptbl a0 a1 a2 (sg 66))
      (va1_put 6 24 (\k. if k = 0 then a0 else if k = 1 then a1 else if k = 2 then a2 else va1_phdr a0 a1 a2 (k - 3))
       (va1_put 3 2 (\k. if k = 0 then sg 2 else word 0) sg)))`;;
