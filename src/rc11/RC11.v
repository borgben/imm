(******************************************************************************)
(** * Definition of the RC11 memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.

Set Implicit Arguments.

Module RC11 (Val : ValueSig) (Ev : Events Val).

Module Import ImmS := imm_s Val Ev.
Module Import SHb := ImmS.SHbModel.
Module Import Eco := ImmS.Eco.
Module Import Ex := ImmS.Ex.
Import Ev.

Section RC11.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'fr'" := (fr G).
Notation "'eco'" := (Eco.eco G).
Notation "'hb'" := (SHb.hb G).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).


(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition rc11_consistent :=
  ⟪ Comp : Ex.complete G ⟫ /\
  ⟪ Coh : SHb.coherence G ⟫ /\
  ⟪ Cat  : Ex.rmw_atomicity G ⟫ /\
  ⟪ Csc : acyclic (ImmS.psc_f G ∪ ImmS.psc_base G) ⟫ /\
  ⟪ Csbrf : acyclic (sb ∪ rf) ⟫.

End RC11.

End RC11.
