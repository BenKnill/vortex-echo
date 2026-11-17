(* ========================================================================= *)
(* Vortex Echo v1: the droplet kick-drift on the record layout of           *)
(* vortex/core/ve_core.wasm (SPEC.md 2 and 3). Droplet record i is words    *)
(* 12 i .. 12 i + 11 of DI (byte 0x120000 + 48 i): px py pz vx vy vz, birth, *)
(* kind << 16 | parent, dz, deta, 0, 0. d m is DI word m.                   *)
(*                                                                           *)
(* ve_drec_fwd d (ve_drop_apply): vy := vy - 1; px += vx; py += vy (the     *)
(* kicked vy); pz += vz.                                                     *)
(* ve_drec_bwd d (ve_drop_unapply): px -= vx; vy += 1; py -= vy (the vy it  *)
(* finds, i.e. the kicked one); pz -= vz.                                    *)
(* Every other word is unchanged.                                            *)
(* ========================================================================= *)

let ve_drec_fwd = new_definition
 `ve_drec_fwd (d:num->int32) (m:num) =
    if m MOD 12 = 4 then word_sub (d m) (word 1)
    else if m MOD 12 = 1 then word_add (d m) (word_sub (d (m + 3)) (word 1))
    else if m MOD 12 = 0 \/ m MOD 12 = 2 then word_add (d m) (d (m + 3))
    else d m`;;

let ve_drec_bwd = new_definition
 `ve_drec_bwd (d:num->int32) (m:num) =
    if m MOD 12 = 4 then word_add (d m) (word 1)
    else if m MOD 12 = 0 \/ m MOD 12 = 1 \/ m MOD 12 = 2 then word_sub (d m) (d (m + 3))
    else d m`;;
