Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm. 
Require Import imm_s. 
Require Import FairExecution.
From hahn Require Import Hahn.
Require Import FinExecution.


Module ImmFair (Val: ValueSig) (Ev:Events Val).
Module Import ImmS := imm_s Val Ev.
Module Imm := ImmS.SHbModel.Imm.
Module Import Ex := ImmS.Ex.
Module Import FairEx := ImmS.Eco.Fair.
Module Import FinEx := FairEx.Fin.


Definition imm_fair (G : Imm.Ex.execution) :=
  fsupp (⦗set_compl Ev.is_init⦘ ⨾ (Imm.ar G)⁺).
Definition imm_s_fair G sc := fsupp (⦗set_compl Ev.is_init⦘ ⨾ (ImmS.ar G sc)⁺).


Section ImmFairProperties.

  Variable G: execution.  
  Variables sc : relation Ev.actid.
  Hypothesis WF: Wf G.
  Hypothesis WFSC: ImmS.wf_sc G sc.
  Hypothesis COM: complete G. 
  Hypothesis FAIR: mem_fair G. 

  Notation "'E'" := (Ex.acts_set G).
  Notation "'R'" := (fun x => is_true (Ev.is_r (Ex.lab G) x)).
  Notation "'W'" := (fun x => is_true (Ev.is_w (Ex.lab G) x)).
  Notation "'F'" := (fun x => is_true (Ev.is_f (Ex.lab G) x)).
  
  Lemma fsupp_rf_sb_loc:
    fsupp (Ex.rf G ⨾ Ex.sb G ∩ Ev.same_loc (Ex.lab G)).
  Proof using WF FAIR. 
    apply fsupp_seq; auto using fsupp_rf, fsupp_sb_loc.
  Qed.

  Lemma fsupp_rf_sb_loc_ct (SCpL: ImmS.Eco.sc_per_loc G):
    fsupp (Ex.rf G ⨾ Ex.sb G ∩ Ev.same_loc (Ex.lab G))⁺.
  Proof using FAIR WF.
    eapply fsupp_mori with
      (x := (Ex.co G)^* ⨾ Ex.rf G ⨾ Ex.sb G ∩ Ev.same_loc (Ex.lab G)).
    2: { apply fsupp_seq; [| by apply fsupp_rf_sb_loc].
         apply fsupp_ct_rt. rewrite ct_of_trans; [| by apply WF].
         apply FAIR. }
    red.
    rewrite ctEE. apply inclusion_bunion_l. intros i _. induction i.
    { simpl. apply seq_mori; basic_solver. }
    rewrite pow_S_end. rewrite IHi.
    arewrite (Ex.rf G ≡ ⦗W⦘ ⨾ Ex.rf G) at 2.
    { rewrite wf_rfD; basic_solver. }
    hahn_frame.
    etransitivity; [| apply inclusion_t_rt]. rewrite ct_end. hahn_frame_l.
    apply ImmS.Eco.rf_sb_loc_w_in_co; auto.
  Qed.

  Lemma clos_trans_domb_begin {A: Type} (r: relation A) (s: A -> Prop)
        (DOMB_S: domb r s):
    ⦗s⦘ ⨾ r⁺ ≡ (⦗s⦘ ⨾ r)⁺.
  Proof using.
    split; [| by apply inclusion_ct_seq_eqv_l].    
    erewrite domb_rewrite with (r := r) at 1; eauto.
    rewrite ct_rotl. rewrite <- seqA. seq_rewrite <- ct_begin. 
    rewrite inclusion_seq_eqv_r. basic_solver.
  Qed. 

  Lemma wf_ar_rf_ppo_loc_ct_inf_helper (r_ar r_ppo: relation Ev.actid)
        (R_RFPPO_AC: acyclic (r_ar ∪ Ex.rf G ⨾ r_ppo ∩ Ev.same_loc (Ex.lab G)))
        (R_RFPPO_NI: (r_ar ∪ Ex.rf G ⨾ r_ppo ∩ Ev.same_loc (Ex.lab G)) ⨾ ⦗Ev.is_init⦘ ≡ ∅₂)
        (FSUPPr: fsupp (⦗set_compl Ev.is_init⦘ ⨾ r_ar⁺))
        (R_PPO_SB: r_ppo ⊆ Ex.sb G)
        (R_RFPPO_CLOS: r_ar ⨾ (Ex.rf G ⨾ r_ppo ∩ Ev.same_loc (Ex.lab G))⁺ ⊆ r_ar⁺)
        (SCpL: ImmS.Eco.sc_per_loc G):
    well_founded (⦗set_compl Ev.is_init⦘ ⨾
      (r_ar ∪ Ex.rf G ;; r_ppo ∩ Ev.same_loc (Ex.lab G))⁺).
  Proof using WF FAIR COM. 
    apply fsupp_well_founded.
    3: { generalize transitive_ct. basic_solver. }
    2: { eapply irreflexive_mori; [| by apply R_RFPPO_AC]; eauto.
         red. basic_solver. } 

    rewrite clos_trans_domb_begin.
    2: { generalize R_RFPPO_NI. basic_solver 10.
         Unshelve. all: by eauto. }

    rewrite seq_union_r.
    eapply fsupp_mori.
    { red. eapply clos_trans_mori, union_mori; [reflexivity| ].
      apply inclusion_seq_eqv_l. }
      
    rewrite ct_unionE. apply fsupp_union.
    { rewrite R_PPO_SB. by apply fsupp_rf_sb_loc_ct. }
    apply fsupp_seq.
    { apply fsupp_ct_rt.
      rewrite R_PPO_SB. by apply fsupp_rf_sb_loc_ct. }

    eapply fsupp_mori; [| by apply FSUPPr].
    red. rewrite rtE, seq_union_r, seq_id_r.
    rewrite seqA, R_RFPPO_CLOS; auto.
    etransitivity.
    2: { rewrite <- ct_of_ct. reflexivity. }
    etransitivity.
    2: { apply inclusion_ct_seq_eqv_l. } 
    apply clos_trans_mori.
    unionL; hahn_frame_l; try reflexivity.
    rewrite <- ct_step. reflexivity.
  Qed.

  Lemma imm_s_fair_fsupp_sc (IMM_FAIR: imm_s_fair G sc):
    fsupp sc. 
  Proof using WF WFSC. 
    eapply fsupp_mori; [| by apply IMM_FAIR].
    red. rewrite <- ct_step. unfold ImmS.ar. do 2 rewrite <- inclusion_union_r1.
    apply doma_helper. inversion WFSC. rewrite wf_scD.
    red. intros ? ? ?%seq_eqv_lr.
    eapply Ex.read_or_fence_is_not_init; eauto. type_solver. 
    exact WFSC.
  Qed. 
End ImmFairProperties.

Lemma fin_exec_imm_s_fair G sc (WF: Ex.Wf G) (WFSC: ImmS.wf_sc G sc)
      (FIN: FinEx.fin_exec G):
  imm_s_fair G sc. 
Proof using. 
  red. red in FIN.
  eapply fsupp_mori.
  2: { eapply fsupp_cross with (s' := set_full); eauto. }
  red. rewrite ct_begin, ImmS.wf_arE; auto. basic_solver.  
Qed. 

Lemma fin_exec_imm_fair G (WF: Imm.Ex.Wf G)
      (FIN: Imm.Eco.Fair.Fin.fin_exec G):
  imm_fair G. 
Proof using. 
  red. red in FIN.
  eapply fsupp_mori.
  2: { eapply fsupp_cross with (s' := set_full); eauto. }
  red. rewrite ct_begin, Imm.wf_arE; auto. basic_solver.  
Qed. 

End ImmFair.
