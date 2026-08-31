(******************************************************************************)
(** * C11 is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob imm_s_ppo.
Require Import imm_s_hb.
Require Import imm_s C11.

Set Implicit Arguments.

Module C11Toimm_s (Val : ValueSig) (Ev : Events Val).

Module Import C := C11 Val Ev.
Module Import ImmS := C.ImmS.
Module Import SHb := ImmS.SHbModel.
Module Import Ppo := ImmS.Ppo.
Module Import Bob := ImmS.Bob.
Module Import Eco := ImmS.Eco.
Module Import Ex := ImmS.Ex.
Import Ev.

Section C11_TO_IMM_S.

Variable G : execution.

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)

Lemma s_imm_consistentimplies_c11_consistent (WF: Wf G) sc
      (IPC : ImmS.imm_psc_consistent G sc) :
  C.c11_consistent G.
Proof using.
  cdes IPC. cdes IC. red. splits; auto.
Qed.

End C11_TO_IMM_S.

End C11Toimm_s.
