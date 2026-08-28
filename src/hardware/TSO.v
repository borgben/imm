(******************************************************************************)
(** * Definition of the x86-TSO memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import FinThreads. 
Require Import FairExecution.

Set Implicit Arguments.

Module TSO
    (Val : ValueSig)
    (Ev : Events Val).

Module Import Eco := Execution_eco Val Ev.
Module Import Ex := Eco.Ex.

Section TSODefs.

Variable G : execution.

Notation "'E'" := (Ex.acts_set G).
Notation "'lab'" := (Ex.lab G).
Notation "'sb'" := (Ex.sb G).
Notation "'rf'" := (Ex.rf G).
Notation "'co'" := (Ex.co G).
Notation "'rmw'" := (Ex.rmw G).
Notation "'data'" := (Ex.data G).
Notation "'addr'" := (Ex.addr G).
Notation "'ctrl'" := (Ex.ctrl G).
Notation "'deps'" := (Ex.deps G).
Notation "'fre'" := (Ex.fre G).
Notation "'rfe'" := (Ex.rfe G).
Notation "'coe'" := (Ex.coe G).
Notation "'rfi'" := (Ex.rfi G).
Notation "'fri'" := (Ex.fri G).
Notation "'fr'" := (Ex.fr G).
Notation "'eco'" := (Eco.eco G).

Notation "'R'" := (fun a => is_true (Ev.is_r lab a)).
Notation "'W'" := (fun a => is_true (Ev.is_w lab a)).
Notation "'F'" := (fun a => is_true (Ev.is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'MFENCE'" := (F ∩₁ (fun a => is_true (Ev.is_sc lab a))).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition ppo := (⦗RW⦘ ⨾ sb ⨾ ⦗RW⦘) \ (fun x y => W x /\ R y).

Definition fence := ⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘.

Definition implied_fence := ⦗W⦘ ⨾ sb ⨾ ⦗dom_rel rmw⦘ ∪ ⦗codom_rel rmw⦘ ⨾ sb ⨾ ⦗R⦘.

Definition hb := ppo ∪ fence ∪ implied_fence ∪ rfe ∪ co ∪ fr.

(******************************************************************************)
(** ** Consistency *)
(******************************************************************************)

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.
Implicit Type SC_PER_LOC : Eco.sc_per_loc G.

Definition TSOConsistent :=
  ⟪ WF : Wf G ⟫ /\
  ⟪ COMP : complete G ⟫ /\
  ⟪ SC_PER_LOC: Eco.sc_per_loc G ⟫ /\
  ⟪ ATOMICITY : rmw_atomicity G ⟫ /\
  ⟪ GHB : acyclic hb ⟫.

Implicit Type CON : TSOConsistent.

Lemma CON_WF CON : Wf G.
Proof using. apply CON. Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_ppoE WF: ppo ≡ ⦗E⦘ ⨾ ppo ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold ppo.
rewrite (@wf_sbE G) at 1.
basic_solver 42.
Qed.

Lemma wf_fenceE WF: fence ≡ ⦗E⦘ ⨾ fence ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold fence.
rewrite (@wf_sbE G) at 1 2.
basic_solver 42.
Qed.

Lemma wf_implied_fenceE WF: implied_fence ≡ ⦗E⦘ ⨾ implied_fence ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold implied_fence.
rewrite (@wf_sbE G) at 1 2.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains *)
(******************************************************************************)

Lemma wf_hbD WF : hb ≡ ⦗RW⦘ ⨾ hb ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
apply dom_helper_3.
unfold hb.
unfold ppo, fence, implied_fence.
rewrite (wf_rmwD WF) at 1 2.
rewrite (wf_rfeD WF) at 1.
rewrite (wf_coD WF) at 1.
rewrite (wf_frD WF) at 1.
generalize (Ev.R_ex_in_R lab).
basic_solver 42.
Qed.


Lemma wf_ct_hbD WF : hb⁺ ≡ ⦗RW⦘ ⨾ hb⁺ ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
apply dom_helper_3.
rewrite (wf_hbD WF).
rewrite inclusion_ct_seq_eqv_l.
rewrite inclusion_ct_seq_eqv_r.
basic_solver.
Qed.

(******************************************************************************)
(** ** Properties  *)
(******************************************************************************)

Lemma ppo_alt : ppo ≡ 
  ⦗R⦘ ⨾ sb ⨾ ⦗RW⦘ ∪ ⦗W⦘ ⨾ sb ⨾ ⦗W⦘.
Proof using.
unfold ppo.
split.
by apply inclusion_minus_l; basic_solver 12.
by unfolder; ins; desf; splits; eauto 10; intro; type_solver.
Qed.

Lemma ppo_in_sb : ppo ⊆ sb. 
Proof using.
unfold ppo; basic_solver.
Qed.

Lemma rel_union_minus_alt {A: Type} (r r': relation A):
  r ≡ r ∩ r' ∪ r \ r'.
Proof using.
  split; [| basic_solver].
  red. intros x y Rxy.
  destruct (classic (r' x y)); basic_solver. 
Qed.

Lemma TSO_sb_rf_acyclic WF (TSO: TSOConsistent):
  acyclic (sb ∪ rf). 
Proof using. 
  rewrite rfi_union_rfe, <- unionA.
  rewrite union_absorb_r with (r := rfi); [| unfold "rfi"; basic_solver].  
  apply acyclic_utt. 
  { by apply sb_trans. }
  { apply transitiveI. rewrite wf_rfeD; auto. type_solver. }
  splits. 
  { by apply sb_irr. }
  { rewrite rfe_in_rf. by apply rf_irr. }
  rewrite wf_rfeD; [| done]. do 2 rewrite <- seqA. rewrite acyclic_rotl.
  cdes TSO. red. red in GHB. eapply irreflexive_mori; [| by apply GHB]. 
  red. rewrite <- (ct_of_ct hb). apply clos_trans_mori.
  rewrite <- ct_unit. rewrite <- seqA. apply seq_mori; [| unfold hb; basic_solver].
  rewrite <- ct_step. repeat apply inclusion_union_r1_search. 
  unfold ppo. unfolder. ins. desc. splits; vauto. intros [? ?]. type_solver.  
Qed.


End TSODefs.

End TSO.
