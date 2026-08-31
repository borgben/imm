(******************************************************************************)

(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_hb.
Require Import imm_s_hb.

Set Implicit Arguments.

Module imm_s_hb_hbWithSHb
    (Val : ValueSig)
    (Ev : Events Val)
    (SHbM : imm_s_hbSig Val Ev).

Module Import SHb := SHbM.
Module Import Hb := SHb.Hb.
Module Import Bob := Hb.Bob.
Module Import Eco := Bob.Eco.
Module Import Ex := Eco.Ex.

Section SHbHbDefs.

Variable G : execution.

Notation "'E'" := (Ex.acts_set G).
Notation "'sb'" := (Ex.sb G).
Notation "'rf'" := (Ex.rf G).
Notation "'co'" := (Ex.co G).
Notation "'rmw'" := (Ex.rmw G).
Notation "'data'" := (Ex.data G).
Notation "'addr'" := (Ex.addr G).
Notation "'ctrl'" := (Ex.ctrl G).
Notation "'rmw_dep'" := (Ex.rmw_dep G).

Notation "'fr'" := (Ex.fr G).
Notation "'eco'" := (Eco.eco G).
Notation "'coe'" := (Ex.coe G).
Notation "'coi'" := (Ex.coi G).
Notation "'deps'" := (Ex.deps G).
Notation "'rfi'" := (Ex.rfi G).
Notation "'rfe'" := (Ex.rfe G).

Notation "'detour'" := (Ex.detour G).

Notation "'rs'" := (Hb.rs G).
Notation "'release'" := (Hb.release G).
Notation "'sw'" := (Hb.sw G).
Notation "'hb'" := (Hb.hb G).


Notation "'s_rs'" := (SHb.rs G).
Notation "'s_release'" := (SHb.release G).
Notation "'s_sw'" := (SHb.sw G).
Notation "'s_hb'" := (SHb.hb G).


Notation "'lab'" := (Ex.lab G).
Notation "'loc'" := (Ev.loc lab).
Notation "'val'" := (Ev.val lab).
Notation "'mod'" := (Ev.mod lab).
Notation "'same_loc'" := (Ev.same_loc lab).

Notation "'R'" := (fun a => is_true (Ev.is_r lab a)).
Notation "'W'" := (fun a => is_true (Ev.is_w lab a)).
Notation "'F'" := (fun a => is_true (Ev.is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (Ev.R_ex lab a)).
Notation "'W_ex'" := (Ex.W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (Ev.is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (Ev.is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (Ev.is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (Ev.is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (Ev.is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (Ev.is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (Ev.is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (Ev.is_sc lab a)).

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)
Lemma s_rs_in_rs : s_rs ⊆ rs.
Proof using.
unfold SHb.rs, Hb.rs.
hahn_frame.
rewrite rtE at 1; relsf.
apply inclusion_union_l.
rewrite rtE at 1; relsf.
basic_solver.
unionR right.
arewrite_id ⦗W⦘; rels.
arewrite (rf ⨾ rmw ⊆ (sb ∩ same_loc)^? ⨾ rf ⨾ rmw) at 1 by basic_solver 12.
rewrite ct_begin.
generalize (@sb_same_loc_trans G); ins; rewrite !seqA; relsf.
generalize (ct_begin ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)).
basic_solver 40.
Qed.

Lemma s_release_in_release : s_release ⊆ release.
Proof using.
unfold SHb.release, Hb.release.
by rewrite s_rs_in_rs.
Qed.

Lemma s_sw_in_sw : s_sw ⊆ sw.
Proof using.
unfold SHb.sw, Hb.sw.
rewrite s_release_in_release.
rewrite (rfi_union_rfe).
basic_solver 21.
Qed.

Lemma s_hb_in_hb : s_hb ⊆ hb.
Proof using.
unfold SHb.hb, Hb.hb.
by rewrite s_sw_in_sw.
Qed.

(******************************************************************************)
(** Properties **  *)
(******************************************************************************)

Lemma coherence_implies_s_coherence (WF: Wf G) (COMP: complete G) :
  Hb.coherence G -> SHb.coherence G.
Proof using.
unfold SHb.coherence.
unfolder; ins; desf.
eapply Hb.hb_irr; eauto.
eapply s_hb_in_hb; edone.
unfold Hb.coherence in *; unfolder in *.
eapply H; eexists; split; eauto.
eapply s_hb_in_hb; edone.
Qed.

End SHbHbDefs.

End imm_s_hb_hbWithSHb.

Module imm_s_hb_hb (Val : ValueSig) (Ev : Events Val).
  Module BaseSHb := imm_s_hb Val Ev.
  Include imm_s_hb_hbWithSHb Val Ev BaseSHb.
End imm_s_hb_hb.
