let va1_pnrm = new_definition
 `va1_pnrm (a0:int32) (a1:int32) (a2:int32) =
    (wfun 159 (wfbin 160 (wfbin 160 (wfbin 162 (wfcvt 183 a0) (wfcvt 183 a0)) (wfbin 162 (wfcvt 183 a1) (wfcvt 183 a1))) (wfbin 162 (wfcvt 183 a2) (wfcvt 183 a2)))):int64`;;
let va1_pu0 = new_definition
 `va1_pu0 (a0:int32) (a1:int32) (a2:int32) =
    (wfbin 163 (wfcvt 183 a0) (va1_pnrm a0 a1 a2)):int64`;;
let va1_pu1 = new_definition
 `va1_pu1 (a0:int32) (a1:int32) (a2:int32) =
    (wfbin 163 (wfcvt 183 a1) (va1_pnrm a0 a1 a2)):int64`;;
let va1_pu2 = new_definition
 `va1_pu2 (a0:int32) (a1:int32) (a2:int32) =
    (wfbin 163 (wfcvt 183 a2) (va1_pnrm a0 a1 a2)):int64`;;
let va1_pe1x = new_definition
 `va1_pe1x (a0:int32) (a1:int32) (a2:int32) =
    (va1_f34e1x (va1_pu0 a0 a1 a2) (va1_pu1 a0 a1 a2) (va1_pu2 a0 a1 a2)):int64`;;
let va1_pe1y = new_definition
 `va1_pe1y (a0:int32) (a1:int32) (a2:int32) =
    (va1_f34e1y (va1_pu0 a0 a1 a2) (va1_pu1 a0 a1 a2) (va1_pu2 a0 a1 a2)):int64`;;
let va1_pe1z = new_definition
 `va1_pe1z (a0:int32) (a1:int32) (a2:int32) =
    (va1_f34e1z (va1_pu0 a0 a1 a2) (va1_pu1 a0 a1 a2) (va1_pu2 a0 a1 a2)):int64`;;
let va1_pe2x = new_definition
 `va1_pe2x (a0:int32) (a1:int32) (a2:int32) =
    (va1_f34e2x (va1_pu0 a0 a1 a2) (va1_pu1 a0 a1 a2) (va1_pu2 a0 a1 a2)):int64`;;
let va1_pe2y = new_definition
 `va1_pe2y (a0:int32) (a1:int32) (a2:int32) =
    (va1_f34e2y (va1_pu0 a0 a1 a2) (va1_pu1 a0 a1 a2) (va1_pu2 a0 a1 a2)):int64`;;
let va1_pe2z = new_definition
 `va1_pe2z (a0:int32) (a1:int32) (a2:int32) =
    (va1_f34e2z (va1_pu0 a0 a1 a2) (va1_pu1 a0 a1 a2) (va1_pu2 a0 a1 a2)):int64`;;
let va1_pw = new_definition
 `va1_pw (w:int32) =
    (wfcvt 184 (word_udiv (word_add w (word 4294942995)) (word 977)):int64)`;;
let va1_pg12 = new_definition
 `va1_pg12 (w:int32) =
    (va1_f32v (wfbin 162 (va1_pw w) (word 4606281698874543309)) (word 1)):int64`;;
let va1_pg13 = new_definition
 `va1_pg13 (w:int32) =
    (va1_f32v (wfbin 162 (va1_pw w) (word 4606281698874543309)) (word 0)):int64`;;
let va1_pg14 = new_definition
 `va1_pg14 (w:int32) =
    (va1_f32v (wfbin 162 (va1_pw w) (word 4600877379321698714)) (word 1)):int64`;;
let va1_pg15 = new_definition
 `va1_pg15 (w:int32) =
    (va1_f32v (wfbin 162 (va1_pw w) (word 4600877379321698714)) (word 0)):int64`;;
let va1_pcnt = new_definition
 `va1_pcnt (n:num) =
    (ITER n (\x. wfbin 160 x (word 4607182418800017408)) (word 0)):int64`;;
let va1_prt = new_definition
 `va1_prt (k:num) =
    (wfbin 162 (wfbin 162 (va1_pcnt k) (word 4618760256179416344)) (word 4557642822898941952)):int64`;;
let va1_prs = new_definition
 `va1_prs (k:num) =
    (va1_f32v (va1_prt k) (word 1)):int64`;;
let va1_prc = new_definition
 `va1_prc (k:num) =
    (va1_f32v (va1_prt k) (word 0)):int64`;;
let va1_pr24 = new_definition
 `va1_pr24 (a0:int32) (a1:int32) (a2:int32) (k:num) =
    (wfbin 160 (wfbin 162 (va1_pe1z a0 a1 a2) (va1_prs k)) (wfbin 162 (va1_pe2z a0 a1 a2) (va1_prc k))):int64`;;
let va1_pr25 = new_definition
 `va1_pr25 (a0:int32) (a1:int32) (a2:int32) (k:num) =
    (wfbin 160 (wfbin 162 (va1_pe1y a0 a1 a2) (va1_prs k)) (wfbin 162 (va1_pe2y a0 a1 a2) (va1_prc k))):int64`;;
let va1_pr26 = new_definition
 `va1_pr26 (a0:int32) (a1:int32) (a2:int32) (k:num) =
    (wfbin 160 (wfbin 162 (va1_pe1x a0 a1 a2) (va1_prs k)) (wfbin 162 (va1_pe2x a0 a1 a2) (va1_prc k))):int64`;;
let va1_pct = new_definition
 `va1_pct (i:num) =
    (wfbin 162 (va1_pcnt i) (word 4584664420663164928)):int64`;;
let va1_pcs = new_definition
 `va1_pcs (i:num) =
    (va1_f32v (va1_pct i) (word 1)):int64`;;
let va1_pcc = new_definition
 `va1_pcc (i:num) =
    (va1_f32v (va1_pct i) (word 0)):int64`;;
let va1_pc28 = new_definition
 `va1_pc28 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 160 (wfbin 162 (va1_pu2 a0 a1 a2) (va1_pcs i)) (wfbin 162 (va1_pr24 a0 a1 a2 k) (va1_pcc i))):int64`;;
let va1_pc29 = new_definition
 `va1_pc29 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 160 (wfbin 162 (va1_pu0 a0 a1 a2) (va1_pcs i)) (wfbin 162 (va1_pr26 a0 a1 a2 k) (va1_pcc i))):int64`;;
let va1_pc30 = new_definition
 `va1_pc30 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 160 (wfbin 162 (va1_pu1 a0 a1 a2) (va1_pcs i)) (wfbin 162 (va1_pr25 a0 a1 a2 k) (va1_pcc i))):int64`;;
let va1_pcl = new_definition
 `va1_pcl (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (if wfrel 99 (va1_pc30 a0 a1 a2 w k i) (word 13830554455654793216) then word 13830554455654793216 else if wfrel 100 (va1_pc30 a0 a1 a2 w k i) (word 4607182418800017408) then word 4607182418800017408 else va1_pc30 a0 a1 a2 w k i):int64`;;
let va1_pch = new_definition
 `va1_pch (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfun 159 (wfbin 160 (wfbin 162 (va1_pc29 a0 a1 a2 w k i) (va1_pc29 a0 a1 a2 w k i)) (wfbin 162 (va1_pc28 a0 a1 a2 w k i) (va1_pc28 a0 a1 a2 w k i)))):int64`;;
let va1_pc31 = new_definition
 `va1_pc31 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (if wfrel 100 (va1_pch a0 a1 a2 w k i) (word 118622047889322841) then wfbin 163 (va1_pc28 a0 a1 a2 w k i) (va1_pch a0 a1 a2 w k i) else word 4607182418800017408):int64`;;
let va1_pc7 = new_definition
 `va1_pc7 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (if wfrel 100 (va1_pch a0 a1 a2 w k i) (word 118622047889322841) then wfbin 163 (va1_pc29 a0 a1 a2 w k i) (va1_pch a0 a1 a2 w k i) else word 0):int64`;;
let va1_pd6 = new_definition
 `va1_pd6 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 160 (wfbin 162 (va1_pch a0 a1 a2 w k i) (word 4617315517961601024)) (wfbin 161 (wfbin 162 (va1_pch a0 a1 a2 w k i) (wfbin 162 (va1_pch a0 a1 a2 w k i) (wfbin 162 (va1_pch a0 a1 a2 w k i) (wfbin 162 (va1_pch a0 a1 a2 w k i) (wfbin 162 (va1_pch a0 a1 a2 w k i) (word 4625196817309499392)))))) (wfbin 162 (va1_pch a0 a1 a2 w k i) (wfbin 162 (va1_pch a0 a1 a2 w k i) (wfbin 162 (va1_pch a0 a1 a2 w k i) (word 4626322717216342016)))))):int64`;;
let va1_pd28 = new_definition
 `va1_pd28 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 162 (wfbin 160 (va1_pc7 a0 a1 a2 w k i) (va1_pc7 a0 a1 a2 w k i)) (va1_pc31 a0 a1 a2 w k i)):int64`;;
let va1_pd29 = new_definition
 `va1_pd29 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 160 (wfbin 162 (va1_pcl a0 a1 a2 w k i) (word 4617315517961601024)) (wfbin 161 (wfbin 162 (va1_pcl a0 a1 a2 w k i) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (word 4625196817309499392)))))) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (word 4626322717216342016)))))):int64`;;
let va1_pd30 = new_definition
 `va1_pd30 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 161 (wfbin 162 (va1_pc31 a0 a1 a2 w k i) (va1_pc31 a0 a1 a2 w k i)) (wfbin 162 (va1_pc7 a0 a1 a2 w k i) (va1_pc7 a0 a1 a2 w k i))):int64`;;
let va1_pd5 = new_definition
 `va1_pd5 (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 160 (wfbin 162 (wfbin 160 (wfbin 162 (va1_pc28 a0 a1 a2 w k i) (word 4602678819172646912)) (wfbin 160 (wfbin 162 (va1_pc30 a0 a1 a2 w k i) (word 4605380978949069210)) (wfbin 162 (va1_pc29 a0 a1 a2 w k i) (word 4599075939470750515)))) (word 4633641066610819072)) (wfbin 160 (wfbin 162 (wfbin 160 (wfbin 162 (va1_pg14 w) (wfbin 160 (wfbin 162 (va1_pd6 a0 a1 a2 w k i) (va1_pd28 a0 a1 a2 w k i)) (wfbin 162 (va1_pd29 a0 a1 a2 w k i) (va1_pd30 a0 a1 a2 w k i)))) (wfbin 162 (va1_pg15 w) (wfbin 161 (wfbin 162 (va1_pd6 a0 a1 a2 w k i) (va1_pd30 a0 a1 a2 w k i)) (wfbin 162 (va1_pd29 a0 a1 a2 w k i) (va1_pd28 a0 a1 a2 w k i))))) (word 4635329916471083008)) (wfbin 160 (wfbin 162 (wfbin 162 (wfbin 161 (word 4607182418800017408) (wfbin 162 (va1_pcl a0 a1 a2 w k i) (wfbin 160 (va1_pcl a0 a1 a2 w k i) (va1_pcl a0 a1 a2 w k i)))) (wfbin 160 (wfbin 162 (va1_pg12 w) (wfbin 161 (wfbin 162 (va1_pc7 a0 a1 a2 w k i) (word 4613937818241073152)) (wfbin 162 (va1_pc7 a0 a1 a2 w k i) (wfbin 162 (va1_pc7 a0 a1 a2 w k i) (wfbin 162 (va1_pc7 a0 a1 a2 w k i) (word 4616189618054758400)))))) (wfbin 162 (va1_pg13 w) (wfbin 161 (wfbin 162 (va1_pc31 a0 a1 a2 w k i) (wfbin 162 (va1_pc31 a0 a1 a2 w k i) (wfbin 162 (va1_pc31 a0 a1 a2 w k i) (word 4616189618054758400)))) (wfbin 162 (va1_pc31 a0 a1 a2 w k i) (word 4613937818241073152)))))) (word 4640185359819341824)) (word 4646096334330265600)))):int64`;;
let va1_pd5b = new_definition
 `va1_pd5b (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfbin 162 (wfbin 162 (wfun 159 (wfbin 163 (word 4646096334330265600) (if wfrel 99 (va1_pd5 a0 a1 a2 w k i) (word 4639129828656676864) then word 4639129828656676864 else va1_pd5 a0 a1 a2 w k i))) (word 4582901240866501059)) (word 4715268809856909312)):int64`;;
let va1_pcp = new_definition
 `va1_pcp (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfun 156 (wfbin 160 (va1_pd5b a0 a1 a2 w k i) (word 4602678819172646912))):int64`;;
let va1_pcn = new_definition
 `va1_pcn (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (wfun 156 (wfbin 161 (word 4602678819172646912) (va1_pd5b a0 a1 a2 w k i))):int64`;;
let va1_pcell = new_definition
 `va1_pcell (a0:int32) (a1:int32) (a2:int32) (w:int32) (k:num) (i:num) =
    (if wfrel 102 (va1_pd5b a0 a1 a2 w k i) (word 0)
    then (if wfrel 99 (word_and (va1_pcp a0 a1 a2 w k i) (word 9223372036854775807)) (word 4890909195324358656)
          then (word_zx (wfcvt 176 (va1_pcp a0 a1 a2 w k i):int64):int32)
          else (word_zx (word 9223372036854775808:int64):int32))
    else word_sub (word 0)
          (word_zx (if wfrel 99 (word_and (va1_pcn a0 a1 a2 w k i) (word 9223372036854775807)) (word 4890909195324358656)
                    then (wfcvt 176 (va1_pcn a0 a1 a2 w k i):int64) else word 9223372036854775808):int32)):int32`;;
let va1_ptbl = new_definition
 `va1_ptbl (a0:int32) (a1:int32) (a2:int32) (w:int32) (j:num) =
    (va1_pcell a0 a1 a2 w (j DIV 128) (j MOD 128)):int32`;;
