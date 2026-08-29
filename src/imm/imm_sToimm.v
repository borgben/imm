(******************************************************************************)
(** * S_IMM is weaker than IMM   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm_s_hb.
Require Import imm.
Require Import imm_s.
Require Import imm_s_hb_hb.

Set Implicit Arguments.

Module imm_sToimm (Val : ValueSig) (Ev : Events Val).

Module Import ImmS := imm_s Val Ev.
Module SHb := ImmS.SHbModel.
Module Import Imm := SHb.Imm.
Module RHb := Imm.Hb.
Module Import Ppo := Imm.Ppo.
Module Import SPpo := ImmS.Ppo.
Module Import Bob := Imm.Bob.
Module Import Eco := Imm.Eco.
Module Import Ex := ImmS.Ex.
Import Ev.

Section S_IMM_TO_IMM.

Variable G : execution.
Hypothesis WF : Wf G.
Hypothesis FINDOM : set_finite (Ex.acts_set G).

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

Notation "'rs'" := (RHb.rs G).
Notation "'release'" := (RHb.release G).
Notation "'sw'" := (RHb.sw G).
Notation "'hb'" := (RHb.hb G).
Notation "'psc'" := (Imm.psc G).

Notation "'s_rs'" := (SHb.rs G).
Notation "'s_release'" := (SHb.release G).
Notation "'s_sw'" := (SHb.sw G).
Notation "'s_hb'" := (SHb.hb G).

Notation "'ar_int'" := (Ppo.ar_int G).
Notation "'s_ar_int'" := (SPpo.ar_int G).
Notation "'ppo'" := (Ppo.ppo G).
Notation "'s_ppo'" := (SPpo.ppo G).
Notation "'bob'" := (Bob.bob G).

Notation "'ar'" := (Imm.ar G).
Notation "'s_ar'" := (ImmS.ar G).

Notation "'lab'" := (Ex.lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (R_ex lab).
Notation "'W_ex'" := (Ex.W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Lemma s_rs_in_rs : s_rs ⊆ rs.
Proof using.
  unfold SHb.rs, RHb.rs.
  hahn_frame. rewrite rtE at 1; relsf.
  apply inclusion_union_l; [rewrite rtE at 1; relsf; basic_solver|].
  unionR right. arewrite_id ⦗W⦘; rels.
  arewrite (rf ⨾ rmw ⊆ (sb ∩ same_loc)^? ⨾ rf ⨾ rmw) at 1 by basic_solver 12.
  rewrite ct_begin. generalize (@sb_same_loc_trans G); ins; rewrite !seqA; relsf.
  generalize (ct_begin ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)); basic_solver 40.
Qed.

Lemma s_release_in_release : s_release ⊆ release.
Proof using. unfold SHb.release, RHb.release. by rewrite s_rs_in_rs. Qed.

Lemma s_sw_in_sw : s_sw ⊆ sw.
Proof using.
  unfold SHb.sw, RHb.sw. rewrite s_release_in_release, rfi_union_rfe.
  basic_solver 21.
Qed.

Lemma s_hb_in_hb : s_hb ⊆ hb.
Proof using. unfold SHb.hb, RHb.hb. by rewrite s_sw_in_sw. Qed.

Lemma coherence_implies_s_coherence (COMP : complete G) :
  RHb.coherence G -> SHb.coherence G.
Proof using WF.
  unfold SHb.coherence. unfolder; ins; desf.
  eapply RHb.hb_irr; eauto. eapply s_hb_in_hb; edone.
  unfold RHb.coherence in *; unfolder in *.
  eapply H; eexists; split; eauto. eapply s_hb_in_hb; edone.
Qed.

Lemma s_psc_in_psc : ⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘ ⊆ psc.
Proof using. unfold Imm.psc. by rewrite s_hb_in_hb. Qed.

Lemma s_ppo_in_ppo : s_ppo ⊆ ppo.
Proof using WF.
  unfold SPpo.ppo, Ppo.ppo.
  assert (rmw ∪ (rmw_dep ⨾ sb^? ∪ ⦗R_ex⦘ ⨾ sb) ⊆
          (rmw ⨾ sb^? ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺) as AA.
  2: { rewrite !unionA. rewrite AA.
       rewrite <- !unionA. rewrite ct_of_union_ct_r. by rewrite <- !unionA. }
  unionL.
  2: { rewrite crE, seq_union_r, seq_id_r. unionL.
       { rewrite <- ct_step. basic_solver. }
       rewrite <- ct_unit. rewrite <- ct_step.
       rewrite (dom_r (wf_rmw_depD WF)) at 1. basic_solver 10. }
  all: rewrite <- ct_step; unionR left; basic_solver 10.
Qed.

Lemma s_ar_int_in_ar_int : ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘.
Proof using WF. unfold SPpo.ar_int, Ppo.ar_int. by rewrite s_ppo_in_ppo. Qed.

Lemma acyc_ext_implies_s_acyc_ext_helper (AC : Imm.acyc_ext G) :
  ImmS.acyc_ext G (⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
Proof using WF.
  unfold ImmS.acyc_ext, Imm.acyc_ext in *.
  unfold ImmS.ar.
  apply s_acyc_ext_psc_helper; auto.
  unfold ImmS.psc.
  rewrite s_psc_in_psc.
  rewrite s_ar_int_in_ar_int.
  arewrite (sb^? ⨾ psc ⨾ sb^? ⊆ ar⁺).
  { rewrite Imm.wf_pscD. rewrite !seqA.
    arewrite (sb^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ bob^?).
    { unfold Bob.bob, Bob.fwbob. mode_solver 10. }
    arewrite (⦗F ∩₁ Sc⦘ ⨾ sb^?⊆ bob^?).
    { unfold Bob.bob, Bob.fwbob. mode_solver 10. }
    arewrite (bob ⊆ ar).
    { unfold Imm.ar, Ppo.ar_int. basic_solver 10. }
    arewrite (psc ⊆ ar).
    rewrite ct_step with (r:=ar) at 2. by rewrite ct_cr, cr_ct. }
  arewrite (rfe ⊆ ar).
  arewrite (ar_int ⊆ ar).
  arewrite (⦗R⦘ ⨾ ar⁺ ⨾ ⦗W⦘ ⊆ ar⁺) by basic_solver.
  rewrite ct_step with (r:=ar) at 2. sin_rewrite !unionK.
  red. by rewrite ct_of_ct.
Qed.

Lemma acyc_ext_implies_s_acyc_ext (AC : Imm.acyc_ext G) :
  exists sc, ImmS.wf_sc G sc /\ ImmS.acyc_ext G sc /\ ImmS.coh_sc G sc.
Proof using WF FINDOM.
  apply ImmS.s_acyc_ext_helper; auto.
    by apply acyc_ext_implies_s_acyc_ext_helper.
Qed.

Lemma imm_consistentimplies_s_imm_consistent (AC : Imm.acyc_ext G) :
  Imm.imm_consistent G -> exists sc, ImmS.imm_consistent G sc.
Proof using WF FINDOM.
  unfold ImmS.imm_consistent, Imm.imm_consistent.
  ins; desf.
  edestruct acyc_ext_implies_s_acyc_ext as [sc]; auto. desf.
  exists sc; splits; eauto 10 using coherence_implies_s_coherence.
Qed.

Lemma imm_consistentimplies_s_imm_psc_consistent
      (IC : Imm.imm_consistent G) :
  exists sc, ImmS.imm_psc_consistent G sc.
Proof using WF FINDOM.
  edestruct imm_consistentimplies_s_imm_consistent as [sc]; eauto.
  { apply IC. }
  exists sc. red. splits; auto.
  unfold ImmS.psc_f, ImmS.psc_base, ImmS.scb.
  rewrite s_hb_in_hb.
  apply IC.
Qed.

Lemma imm_consistentimplies_s_imm_psc_consistent_with_fsupp
      (NOSC : E ∩₁ F ∩₁ Sc ⊆₁ ∅)
      (FSUPPSB : fsupp sb) (* NEXT TODO: remove the restriction *)
      (FSUPPRF : fsupp rf) (* NEXT TODO: remove the restriction *)
      (FSUPP : fsupp ar⁺)
      (IC : Imm.imm_consistent G) :
    ⟪ CONS : ImmS.imm_psc_consistent G ∅₂ ⟫ /\
    ⟪ FSUPP : fsupp (s_ar ∅₂)⁺ ⟫.
Proof using WF.
  assert (transitive sb) as TSB by apply sb_trans.
  splits.
  2: { unfold ImmS.ar. rewrite union_false_l.
       rewrite ct_unionE.
       assert (fsupp s_ar_int⁺) as AA.
       { rewrite SPpo.ar_int_in_sb; auto.
         rewrite ct_of_trans; auto. }
       apply fsupp_union; auto.
       apply fsupp_seq.
       { now apply fsupp_ct_rt. }
       rewrite (wf_rfeD WF), !seqA.
       rewrite ct_rotl, !seqA.
       repeat (apply fsupp_seq); try apply fsupp_eqv.
       3: { rewrite SPpo.ar_int_in_sb; auto.
            rewrite rt_of_trans; auto.
            now apply fsupp_cr. }
       2: now rewrite rfe_in_rf.
       arewrite (⦗R⦘ ⨾ s_ar_int＊ ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘).
       { rewrite rtE. clear. type_solver. }
       rewrite s_ar_int_in_ar_int.
       arewrite (rfe ⊆ ar).
       arewrite (ar_int ⊆ ar).
       arewrite_id ⦗R⦘. arewrite_id ⦗W⦘.
       rewrite seq_id_l, seq_id_r.
       arewrite (ar ⊆ ar⁺) at 1.
       rewrite ct_ct. rewrite rt_of_ct.
       rewrite <- cr_of_ct. now apply fsupp_cr. }
  red. splits.
  2: { unfold ImmS.psc_f, ImmS.psc_base, ImmS.scb.
       rewrite s_hb_in_hb.
       apply IC. }
  red. splits; try apply IC.
  { constructor; rewrite ?NOSC.
    all: basic_solver. }
  { red. basic_solver. }
  { cdes IC. apply coherence_implies_s_coherence; auto. }
  red. unfold ImmS.ar.
  arewrite (∅₂ ⊆ ⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
  apply acyc_ext_implies_s_acyc_ext_helper. apply IC.
Qed.

End S_IMM_TO_IMM.

End imm_sToimm.
