#!/usr/bin/env python3
"""Generate the statement strings and the specs of the Vortex Echo v1 model-level proof leaves:
  ve_generic_stmts.ml / ve_generic.spec          theorems of ve_generic.ml
  ve_mutant_stmts.ml  / ve_unbirth_mutant.spec   the un-birth mutant control (ve_unbirth_mutant.ml)
Each <leaf>_stmts.ml holds OCaml strings ve_spec_<THM> that the leaf parses, so proof and spec state one text.
Each spec = header + theorem blocks + definition pins (every new_definition of the defs files the leaf loads,
text copied verbatim) + allow lines (every define'd constant of those files; their CLAUSES theorems pin them).
Usage: gen_ve_spec.py [--check]"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

KERN = 'fr kj dj kc dc kd dd bf fv i0'
KERN_B = 'fr kj dj kc dc kd dd fv'

GEN_THMS = [
    # 1. Fredkin pair step, generic in the kick f
    ('FREDKIN_STEP_INVERSE', '!f s. ve_fredkin_bwd f (ve_fredkin_fwd f s) = s'),
    ('FREDKIN_STEP_FWD_BWD', '!f s. ve_fredkin_fwd f (ve_fredkin_bwd f s) = s'),
    ('VE_FREDKIN_FWDN_CLAUSES',
     '(!f s. ve_fredkin_fwdn f 0 s = s) /\\\n'
     '   (!f n s. ve_fredkin_fwdn f (SUC n) s = ve_fredkin_fwd (f n) (ve_fredkin_fwdn f n s))'),
    ('VE_FREDKIN_BWDN_CLAUSES',
     '(!f s. ve_fredkin_bwdn f 0 s = s) /\\\n'
     '   (!f n s. ve_fredkin_bwdn f (SUC n) s = ve_fredkin_bwdn f n (ve_fredkin_bwd (f n) s))'),
    ('FREDKIN_STEPS_INVERSE', '!f n s. ve_fredkin_bwdn f n (ve_fredkin_fwdn f n s) = s'),
    ('FREDKIN_STEPS_FWD_BWD', '!f n s. ve_fredkin_fwdn f n (ve_fredkin_bwdn f n s) = s'),
    # 2. kick-drift, generic in K and D
    ('KICK_DRIFT_INVERSE', '!K D s. ve_kd_bwd K D (ve_kd_fwd K D s) = s'),
    ('KICK_DRIFT_FWD_BWD', '!K D s. ve_kd_fwd K D (ve_kd_bwd K D s) = s'),
    ('VE_KD_FWDN_CLAUSES',
     '(!K D s. ve_kd_fwdn K D 0 s = s) /\\\n'
     '   (!K D n s. ve_kd_fwdn K D (SUC n) s = ve_kd_fwd (K n) (D n) (ve_kd_fwdn K D n s))'),
    ('VE_KD_BWDN_CLAUSES',
     '(!K D s. ve_kd_bwdn K D 0 s = s) /\\\n'
     '   (!K D n s. ve_kd_bwdn K D (SUC n) s = ve_kd_bwdn K D n (ve_kd_bwd (K n) (D n) s))'),
    ('KICK_DRIFT_STEPS_INVERSE', '!K D n s. ve_kd_bwdn K D n (ve_kd_fwdn K D n s) = s'),
    ('KICK_DRIFT_STEPS_FWD_BWD', '!K D n s. ve_kd_fwdn K D n (ve_kd_bwdn K D n s) = s'),
    # 3. composition
    ('VE_RUN_CLAUSES',
     '(!s:A. ve_run [] s = s) /\\\n'
     '   (!(p:(A->A)#(A->A)#(A->bool)) ps s. ve_run (CONS p ps) s = ve_run ps (FST p s)) /\\\n'
     '   (!s:A. ve_unrun [] s = s) /\\\n'
     '   (!(p:(A->A)#(A->A)#(A->bool)) ps s. ve_unrun (CONS p ps) s = FST (SND p) (ve_unrun ps s)) /\\\n'
     '   (!s:A. ve_runok [] s <=> T) /\\\n'
     '   (!(p:(A->A)#(A->A)#(A->bool)) ps s. ve_runok (CONS p ps) s <=> SND (SND p) s /\\ ve_runok ps (FST p s))'),
    ('VE_COMPOSE_INVERSE',
     '!(ps:((A->A)#(A->A)#(A->bool))list) (s:A).\n'
     '     ALL (\\p. !x. SND (SND p) x ==> FST (SND p) (FST p x) = x) ps /\\ ve_runok ps s\n'
     '     ==> ve_unrun ps (ve_run ps s) = s'),
    # 4. births on the LIFO log
    ('VE_PUSH_CLAUSES',
     '(!t s. ve_push t [] s = s) /\\\n'
     '   (!t b bs s. ve_push t (CONS b bs) s = ve_push t bs (ve_push1 t b s)) /\\\n'
     '   (!tt s. ve_unb tt 0 s = s) /\\\n'
     '   (!tt n s. ve_unb tt (SUC n) s =\n'
     '             if 0 < ve_cnt s /\\ ve_rbirth (ve_slots s (ve_cnt s - 1)) = tt\n'
     '             then ve_unb tt n (ve_pop1 s) else s)'),
    ('VE_PUSH_INVERSE', '!L t s. ve_log_ok t s ==> ve_births_bwd (t + 1) (ve_push t L s) = s'),
    ('LIFO_BIRTHS_INVERSE', '!B t s. ve_log_ok t s ==> ve_births_bwd (t + 1) (ve_births_fwd B t s) = s'),
    ('VE_LOG_OK_PUSH', '!L t s. ve_log_ok t s ==> ve_log_ok (t + 1) (ve_push t L s)'),
    # 5. the whole tick
    ('VE_STEP_CLAUSES',
     '(!%s nc nsw npo s. ve_step_fwdn %s nc nsw npo 0 s = s) /\\\n'
     '   (!%s nc nsw npo n s. ve_step_fwdn %s nc nsw npo (SUC n) s =\n'
     '      ve_step_fwd %s nc nsw npo (ve_step_fwdn %s nc nsw npo n s)) /\\\n'
     '   (!%s nc nsw npo s. ve_step_bwdn %s nc nsw npo 0 s = s) /\\\n'
     '   (!%s nc nsw npo n s. ve_step_bwdn %s nc nsw npo (SUC n) s =\n'
     '      ve_step_bwdn %s nc nsw npo n (ve_step_bwd %s nc nsw npo s))'
     % (KERN, KERN, KERN, KERN, KERN, KERN, KERN_B, KERN_B, KERN_B, KERN_B, KERN_B, KERN_B)),
    ('VE_STEP_INVERSE_MODEL',
     '!%s nc nsw npo s.\n'
     '     ve_step_ok s\n'
     '     ==> ve_step_bwd %s nc nsw npo (ve_step_fwd %s nc nsw npo s) = s' % (KERN, KERN_B, KERN)),
    ('VE_STEP_INVERSE_MODEL_V1',
     '!%s s.\n'
     '     ve_step_ok s\n'
     '     ==> ve_step_bwd %s 4 16 1 (ve_step_fwd %s 4 16 1 s) = s' % (KERN, KERN_B, KERN)),
    ('VE_RUN_OK_STEP_OK', '!s. ve_run_ok s ==> ve_step_ok s'),
    ('VE_RUN_OK_STEP',
     '!%s nc nsw npo s.\n'
     '     ve_run_ok s ==> ve_run_ok (ve_step_fwd %s nc nsw npo s)' % (KERN, KERN)),
    ('VE_RUN_OK_INIT', '!s. ve_t s = 0 /\\ 0 < ve_pt s /\\ ve_pop_zero s ==> ve_run_ok s'),
    ('VE_RUN_INVERSE_MODEL',
     '!%s nc nsw npo n s.\n'
     '     ve_run_ok s\n'
     '     ==> ve_step_bwdn %s nc nsw npo n (ve_step_fwdn %s nc nsw npo n s) = s' % (KERN, KERN_B, KERN)),
]
GEN_DEFS_FILES = ['ve_generic_defs.ml']
GEN_HEADER = ('(* Spec: Vortex Echo v1 (tasks/bubble-echo/vortex), the reversible tick at model level, pure HOL (no bytes); '
              'vectors num -> int32 with word_add / word_sub. (1) Fredkin pair step (a,b) -> (b, a + f b) and its '
              'inverse, one step and n substeps, any f; (2) kick-drift (kick reads q, updates p; drift reads p, '
              'updates q), one and n substeps, any K, D; (3) composition: reversed backward pieces invert the forward '
              'composition when each piece has a left inverse under a precondition that holds along the trajectory; '
              '(4) droplet births on a LIFO log: pushing a tick\'s births (birth tick t + 1, parent loses dz/deta, '
              'droplet words written) then popping every record born at t + 1 restores the state, under the named '
              'premise ve_log_ok t (records born <= t, log clean above the count); (5) the whole tick (rim Fredkin, '
              'jiggle kick-drift, nc corrugation kick-drift substeps, droplet kick-drift on the active slots, births, '
              'vortex Fredkin substeps: npo on pop ticks, nsw on swirl ticks; puncture at the event-log tick pt) with '
              'kernels as arbitrary functions: backward after forward is the identity under the named premise '
              've_step_ok, and over n ticks under the invariant ve_run_ok, which every forward tick keeps. *)')

MUT_THMS = [
    ('VE_MUT_CLAUSES',
     '(!t s. ve_push t [] s = s) /\\\n'
     '   (!t b bs s. ve_push t (CONS b bs) s = ve_push t bs (ve_push1 t b s)) /\\\n'
     '   (!tt s. ve_unb_mut tt 0 s = s) /\\\n'
     '   (!tt n s. ve_unb_mut tt (SUC n) s =\n'
     '             if 0 < ve_cnt s /\\ ve_rbirth (ve_slots s (ve_cnt s - 1)) = tt\n'
     '             then ve_unb_mut tt n (ve_pop1_mut s) else s)'),
    ('VE_UNBIRTH_MUTANT_REFUTED',
     've_log_ok 0 ve_bzero /\\\n'
     '   ~(ve_births_bwd_mut 1 (ve_births_fwd (\\s. [0,word 0,word 1,(\\j. word 0)]) 0 ve_bzero) = ve_bzero)'),
]
MUT_DEFS_FILES = ['ve_generic_defs.ml', 've_mutant_defs.ml']
MUT_HEADER = ('(* Spec: Vortex Echo v1 semantic control at model level: the mutant un-birth ve_pop1_mut, which gives '
              'the parent back its height dz but forgets the stored rate deta (the Phase 1 mutant=1 control), does '
              'not invert the births. Witness: the zero births state ve_bzero (which satisfies the premise ve_log_ok 0) '
              'and one birth at tick 0 from bead 0 with dz = 0, deta = 1; the mutant backward at tick 1 leaves the '
              'rate of bead 0 at -1. Read with LIFO_BIRTHS_INVERSE (ve_generic.spec), where the shipped un-birth '
              'restores every such state. *)')


# ---- the vortex Fredkin export pair on ve_core.wasm (72fe0ba2) ----
VLOCS = '; '.join('wlocal %d' % i for i in range(30))
LLOCS = 'wlocal 0; wlocal 2; wlocal 3; wlocal 4; wlocal 6; wlocal 8; wlocal 14; wlocal 20'
VA_R = '(!m. m < 3 * N ==> read (wmem :> bytes32 (word (1114112 + 4 * m))) s = %s)'
VB_R = '(!m. m < 3 * N ==> read (wmem :> bytes32 (word (1122304 + 4 * m))) s = %s)'
VD_R = '(!m. m < 3 * N ==> read (wmem :> bytes32 (word (1974272 + 4 * m))) s = %s)'


def loop_stmt(mc, newa, newb):
    return ('!N (va:num->int32) (vb:num->int32) (vd:num->int32).\n'
            '     1 <= N /\\ N <= 640\n'
            '     ==> ensures wasm\n'
            '          (\\s. read wcode s = %s /\\ read wpc s = word 1305 /\\\n'
            '               read wstatus s = WRunning /\\ read wstack s = [] /\\\n'
            '               read wlabels s = [] /\\ read warity s = 0 /\\\n'
            '               read wmemsize s = 2097152 /\\\n'
            '               read (wmem :> bytes32 (word 16644)) s = word N /\\\n'
            '               %s /\\\n               %s /\\\n               %s)\n'
            '          (\\s. read wstatus s = WDone /\\ read wstack s = [] /\\\n'
            '               %s /\\\n               %s)\n'
            '          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,\n'
            '           MAYCHANGE [wstatus] ,,\n'
            '           MAYCHANGE [%s] ,,\n'
            '           MAYCHANGE [wmem :> bytes(word 1114112,16384)])'
            % (mc, VA_R % 'va m', VB_R % 'vb m', VD_R % 'vd m', VA_R % newa, VB_R % newb, LLOCS))


def whole_stmt(mc, a0, b0, newa, newb):
    return ('!VK. ve_vk_ok VK\n'
            '     ==> !N (mdl:num->int32) (va:num->int32) (vb:num->int32).\n'
            '          mdl 1 = word N /\\ 1 <= N /\\ N <= 640\n'
            '          ==> ensures wasm\n'
            '               (\\s. read wcode s = %s /\\ read wpc s = word 21 /\\\n'
            '                    read wstatus s = WRunning /\\ read wstack s = [] /\\\n'
            '                    read wlabels s = [] /\\ read warity s = 0 /\\\n'
            '                    read wmemsize s = 2097152 /\\\n'
            '                    (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\\\n'
            '                    %s /\\\n                    %s)\n'
            '               (\\s. read wstatus s = WDone /\\ read wstack s = [] /\\\n'
            '                    %s /\\\n                    %s)\n'
            '               (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,\n'
            '                MAYCHANGE [wstatus] ,,\n'
            '                MAYCHANGE [%s] ,,\n'
            '                MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,\n'
            '                MAYCHANGE [wmem :> bytes(word 1966080,73728)])'
            % (mc, VA_R % a0, VB_R % b0, VA_R % newa, VB_R % newb, VLOCS))


VORT_THMS = [
    ('VE_VORT_APPLY_LOOP_CORRECT', loop_stmt('ve_vort_apply_mc', 'vb m', 'word_add (vd m) (va m)')),
    ('VE_VORT_UNAPPLY_LOOP_CORRECT', loop_stmt('ve_vort_unapply_mc', 'word_sub (vb m) (vd m)', 'va m')),
    ('VE_VORT_APPLY_CORRECT', whole_stmt('ve_vort_apply_mc', 'va m', 'vb m', 'vb m', 'word_add (va m) (VK mdl vb m)')),
    ('VE_VORT_UNAPPLY_CORRECT', whole_stmt('ve_vort_unapply_mc', 'va m', 'vb m', 'word_sub (vb m) (VK mdl va m)', 'va m')),
    ('VE_VORT_APPLY_FREDKIN', whole_stmt('ve_vort_apply_mc', 'va m', 'vb m',
        'FST (ve_fredkin_fwd (VK mdl) (va,vb)) m', 'SND (ve_fredkin_fwd (VK mdl) (va,vb)) m')),
    ('VE_VORT_UNAPPLY_FREDKIN', whole_stmt('ve_vort_unapply_mc', 'va m', 'vb m',
        'FST (ve_fredkin_bwd (VK mdl) (va,vb)) m', 'SND (ve_fredkin_bwd (VK mdl) (va,vb)) m')),
    ('VE_VORT_INVERSE', whole_stmt('ve_vort_unapply_mc', 'vb m', 'word_add (va m) (VK mdl vb m)', 'va m', 'vb m')),
    ('VE_FREDKIN_FWDN_CLAUSES', dict(GEN_THMS)['VE_FREDKIN_FWDN_CLAUSES']),
    ('VE_FREDKIN_BWDN_CLAUSES', dict(GEN_THMS)['VE_FREDKIN_BWDN_CLAUSES']),
    ('VE_VORT_STEPS_INVERSE',
     '!(VK:(num->int32)->(num->int32)->num->int32) mdl n s.\n'
     '     ve_fredkin_bwdn (\\i. VK mdl) n (ve_fredkin_fwdn (\\i. VK mdl) n s) = s'),
]
VORT_DEFS_FILES = ['ve_generic_defs.ml', 've_vort_defs.ml']
VORT_CODES = ['ve_vort_apply_mc', 've_vort_unapply_mc']
VORT_HEADER = ('(* Spec: Vortex Echo v1, the vortex Fredkin export pair ve_vort_apply / ve_vort_unapply on the exact bytes '
               'of vortex/core/ve_core.wasm (sha256 72fe0ba2). (1) The Fredkin loop of each body, from pc 1305 to the end, '
               'unconditionally: apply VA\' = VB, VB\' = VD + VA; unapply VA\' = VB - VD, VB\' = VA, for m < 3N (N = 1..640 '
               'from model word 1), writing only those two regions and its locals. (2) The whole exports under the NAMED '
               'premise ve_vk_ok VK (the field phase, pc 21..1305 of both bodies (pc 21 = wasm_entry, the first instruction after the local declarations; corrected from pc 3 as merged in PR #72), leaves VD = VK(model, source) with the '
               'same VK for both, source VB resp. VA, writing only locals and scratch; discharged in ve_vk.spec by VE_VK_OK): apply is the '
               'Fredkin step (VA, VB) -> (VB, VA + VK(mdl, VB)) of ve_fredkin_fwd, unapply is ve_fredkin_bwd, and unapply '
               'on the state apply leaves restores VA and VB (VE_VORT_INVERSE, an instance of FREDKIN_STEP_INVERSE); '
               'VE_VORT_STEPS_INVERSE: n substeps with this VK (FREDKIN_STEPS_INVERSE). *)')

TICK_STMT = ('!(t:int32). ensures wasm\n'
             '      (\\s. read wcode s = %s /\\ read wpc s = word 1 /\\\n'
             '           read wstatus s = WRunning /\\ read wstack s = [] /\\\n'
             '           read wlabels s = [] /\\ read warity s = 0 /\\ read wmemsize s = 2097152 /\\\n'
             '           read (wmem :> bytes32 (word 16392)) s = %s)\n'
             '      (\\s. read wstatus s = WDone /\\ read wstack s = [] /\\\n'
             '           read (wmem :> bytes32 (word 16392)) s = %s)\n'
             '      (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,\n'
             '       MAYCHANGE [wstatus] ,, MAYCHANGE [wmem :> bytes(word 16392,4)])')
TICK_THMS = [
    ('VE_TICK_INC_CORRECT', TICK_STMT % ('ve_tick_inc_mc', 't', 'word_add t (word 1)')),
    ('VE_TICK_DEC_CORRECT', TICK_STMT % ('ve_tick_dec_mc', 't', 'word_sub t (word 1)')),
    ('VE_TICK_INVERSE', TICK_STMT % ('ve_tick_dec_mc', 'word_add t (word 1)', 't')),
]
TICK_CODES = ['ve_tick_inc_mc', 've_tick_dec_mc']
TICK_HEADER = ('(* Spec: Vortex Echo v1, the header tick pair ve_tick_inc / ve_tick_dec on the exact bytes of '
               'vortex/core/ve_core.wasm (sha256 72fe0ba2): header word 2 (byte 16392) := T + 1 resp. T - 1 (mod 2^32), '
               'no other memory written; dec on the word inc leaves restores T. *)')


def vk_whole_stmt(mc, a0, b0, newa, newb):
    return ('!N (mdl:num->int32) (va:num->int32) (vb:num->int32).\n'
            '     mdl 1 = word N /\\ 1 <= N /\\ N <= 640\n'
            '     ==> ensures wasm\n'
            '          (\\s. read wcode s = %s /\\ read wpc s = word 21 /\\\n'
            '               read wstatus s = WRunning /\\ read wstack s = [] /\\\n'
            '               read wlabels s = [] /\\ read warity s = 0 /\\\n'
            '               read wmemsize s = 2097152 /\\\n'
            '               (!k. k < 1024 ==> read (wmem :> bytes32 (word (16640 + 4 * k))) s = mdl k) /\\\n'
            '               %s /\\\n               %s)\n'
            '          (\\s. read wstatus s = WDone /\\ read wstack s = [] /\\\n'
            '               %s /\\\n               %s)\n'
            '          (MAYCHANGE [wpc] ,, MAYCHANGE [wstack] ,, MAYCHANGE [wlabels] ,,\n'
            '           MAYCHANGE [wstatus] ,,\n'
            '           MAYCHANGE [%s] ,,\n'
            '           MAYCHANGE [wmem :> bytes(word 1114112,16384)] ,,\n'
            '           MAYCHANGE [wmem :> bytes(word 1966080,73728)])'
            % (mc, VA_R % a0, VB_R % b0, VA_R % newa, VB_R % newb, VLOCS))


ZBS = ('((\\m. word 0),(\\m. word 0),(\\m. word 0),(\\m. word 0),0,(\\i. ve_zrec))\n'
       '   :(num->int32)#(num->int32)#(num->int32)#(num->int32)#num#(num->num#int32#int32#num#(num->int32))')
VK_THMS = [
    ('VE_VK_OK', 've_vk_ok ve_vk'),
    ('VE_VK_OK_SAT', '?VK. ve_vk_ok VK'),
    ('VE_VORT_APPLY_CORRECT_VK', vk_whole_stmt('ve_vort_apply_mc', 'va m', 'vb m', 'vb m', 'word_add (va m) (ve_vk mdl vb m)')),
    ('VE_VORT_UNAPPLY_CORRECT_VK', vk_whole_stmt('ve_vort_unapply_mc', 'va m', 'vb m', 'word_sub (vb m) (ve_vk mdl va m)', 'va m')),
    ('VE_VORT_INVERSE_VK', vk_whole_stmt('ve_vort_unapply_mc', 'vb m', 'word_add (va m) (ve_vk mdl vb m)', 'va m', 'vb m')),
    ('VE_FREDKIN_FWDN_CLAUSES', dict(GEN_THMS)['VE_FREDKIN_FWDN_CLAUSES']),
    ('VE_FREDKIN_BWDN_CLAUSES', dict(GEN_THMS)['VE_FREDKIN_BWDN_CLAUSES']),
    ('VE_VORT_STEPS_INVERSE_VK',
     '!(mdl:num->int32) n s.\n     ve_fredkin_bwdn (\\i. ve_vk mdl) n (ve_fredkin_fwdn (\\i. ve_vk mdl) n s) = s'),
    ('VE_ISQ_CLAUSES',
     '(!x. ve_isq 0 x = x) /\\ (!k x. ve_isq (SUC k) x = ve_isq_step (ve_isq k x))'),
    ('VE_VK_RS_CLAUSES',
     '(!X C i c. ve_vk_rs X C i 0 c = word 0) /\\\n'
     '   (!X C i k c. ve_vk_rs X C i (SUC k) c = word_add (ve_vk_ti X C i (i + 1 + k) c) (ve_vk_rs X C i k c))'),
    ('VE_VK_ACC_CLAUSES',
     '(!X C n j c. ve_vk_acc X C n 0 j c = word 0) /\\\n'
     '   (!X C n i j c. ve_vk_acc X C n (SUC i) j c =\n'
     '      if j = i then word_add (ve_vk_acc X C n i j c) (ve_vk_rs X C i (n - 1 - i) c)\n'
     '      else if i < j then ve_vk_upd X C i j c (ve_vk_acc X C n i j c)\n'
     '      else ve_vk_acc X C n i j c)'),
    ('VE_LOG_OK_SAT', 've_log_ok 0 (' + ZBS + ')'),
    ('VE_RUN_OK_SAT', '?s. ve_run_ok s /\\ ve_step_ok s'),
]
VK_DEFS_FILES = ['ve_generic_defs.ml', 've_vort_defs.ml', 've_vk_defs.ml']
VK_HEADER = ('(* Spec: Vortex Echo v1, the field phase of the vortex export pair on the exact bytes of '
             'vortex/core/ve_core.wasm (sha256 72fe0ba2). VE_VK_OK: the named premise ve_vk_ok of ve_vort.spec holds '
             'for the explicit field function ve_vk (ve_vk_defs.ml, defined from the code: normalisation by the 32-step '
             'integer square root and div_s, the regularised Biot-Savart pair sums in wrapping i64 in the compiled order, '
             'rounding (acc + 2^35) >>s 36); both prefixes pc 21..1305 (from the first instruction) reach pc 1305 without '
             'trap, VD = ve_vk(model, source), model / VA / VB unchanged, only locals and scratch written. VE_VK_OK_SAT: '
             'the premise is satisfiable. The whole exports from pc 21 without premise: apply is the Fredkin step with '
             'kick ve_vk, unapply its inverse, unapply after apply restores VA and VB (VE_VORT_INVERSE_VK), n substeps '
             '(VE_VORT_STEPS_INVERSE_VK). Witnesses for the model-level premises: VE_LOG_OK_SAT (ve_log_ok at tick 0 '
             'with the empty log), VE_RUN_OK_SAT (a state with ve_run_ok and ve_step_ok). *)')

PC3_THMS = [('VE_VK_OK_PC3_UNSAT', '!(VK:(num->int32)->(num->int32)->num->int32). ~(ve_vk_ok_pc3 VK)')]
PC3_DEFS_FILES = ['ve_vk_pc3_defs.ml']
PC3_HEADER = ('(* Spec: Vortex Echo v1 control on the exact bytes of vortex/core/ve_core.wasm (sha256 72fe0ba2): the named '
              'premise ve_vk_ok as merged in PR #72 (here ve_vk_ok_pc3, text verbatim apart from the name) starts both '
              'prefixes at pc 3, inside the local declarations (byte 3 decodes as nop, byte 4 as i64.mul, which has no '
              'operands on the empty stack), so no state satisfying its precondition reaches pc 1305: the premise is '
              'unsatisfiable and the conditional theorems stated under it were vacuous. *)')


def ocaml_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'


def defs(files):
    pins, allows = [], []
    for f in files:
        src = open(os.path.join(HERE, f)).read()
        for m in re.finditer(r'let (\w+) = (new_definition|define)\s*\n?\s*`(.*?)`;;', src, re.S):
            (pins if m.group(2) == 'new_definition' else allows).append((m.group(1), m.group(3)))
    return pins, allows


def leaf(thms, files, header, codes=()):
    stmts = ['(* GENERATED by vortex/proofs/gen_ve_spec.py; do not edit. *)']
    for n, t in thms:
        stmts.append('let ve_spec_%s = %s;;' % (n, ocaml_str(t)))
    pins, allows = defs(files)
    spec = [header]
    for n, t in thms:
        spec.append('theorem %s\n `%s`;;' % (n, t))
    for n, t in pins:
        spec.append('definition %s\n `%s`;;' % (n, t))
    if codes:
        import gen_ve_code
        bs = gen_ve_code.bodies()
        for c in codes:
            spec.append('definition %s\n `%s:byte list = [%s]`;;' % (c, c, '; '.join('word 0x%02x' % b for b in bs[c])))
    spec.append('(* define\'d recursive helpers: their meaning is pinned by the CLAUSES theorems above *)')
    for n, _ in allows:
        spec.append('allow %s;;' % n)
    return '\n'.join(stmts) + '\n', '\n'.join(spec) + '\n'


def gen():
    out = {}
    out['ve_generic_stmts.ml'], out['ve_generic.spec'] = leaf(GEN_THMS, GEN_DEFS_FILES, GEN_HEADER)
    if os.path.exists(os.path.join(HERE, 've_vort_defs.ml')):
        out['ve_vort_stmts.ml'], out['ve_vort.spec'] = leaf(VORT_THMS, VORT_DEFS_FILES, VORT_HEADER, VORT_CODES)
    out['ve_tick_stmts.ml'], out['ve_tick.spec'] = leaf(TICK_THMS, [], TICK_HEADER, TICK_CODES)
    if os.path.exists(os.path.join(HERE, 've_vk_defs.ml')):
        out['ve_vk_stmts.ml'], out['ve_vk.spec'] = leaf(VK_THMS, VK_DEFS_FILES, VK_HEADER, VORT_CODES)
    if os.path.exists(os.path.join(HERE, 've_vk_pc3_defs.ml')):
        out['ve_vk_pc3_stmts.ml'], out['ve_vk_pc3.spec'] = leaf(PC3_THMS, PC3_DEFS_FILES, PC3_HEADER, VORT_CODES)
    if os.path.exists(os.path.join(HERE, 've_mutant_defs.ml')):
        out['ve_mutant_stmts.ml'], out['ve_unbirth_mutant.spec'] = leaf(MUT_THMS, MUT_DEFS_FILES, MUT_HEADER)
    return out


if __name__ == '__main__':
    outs = gen()
    if '--check' in sys.argv:
        bad = [f for f, t in outs.items()
               if not os.path.exists(os.path.join(HERE, f)) or open(os.path.join(HERE, f)).read() != t]
        print('DIFFERS: ' + ' '.join(bad) if bad else 'OK')
        sys.exit(1 if bad else 0)
    for f, t in outs.items():
        open(os.path.join(HERE, f), 'w').write(t)
        print('wrote', f)
