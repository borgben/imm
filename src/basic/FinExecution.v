Require Import Lia.
Require Import Classical Peano_dec ClassicalEpsilon.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt. 
Require Import Events.
Require Import Execution.

Module FinExecution
    (Val : ValueSig)
    (Ev : Events Val).

Module Import Ex := Execution Val Ev.

Notation "'Tid_' t" := (fun x => Ev.tid x = t) (at level 1).

Definition fin_exec (G: execution) :=
  set_finite (Ex.acts_set G \₁ Ev.is_init).

Definition fin_exec_full (G: execution) :=
  set_finite (Ex.acts_set G).

Lemma fin_exec_full_equiv (G: execution):
  fin_exec_full G <->
  fin_exec G /\ set_finite (Ex.acts_set G ∩₁ Ev.is_init).
Proof using.
  unfold fin_exec, fin_exec_full.
  rewrite <- set_finite_union. apply set_finite_more. 
  rewrite set_minusE, set_unionC, <- set_inter_union_r, <- set_full_split.
  basic_solver.
Qed. 

Section FinExecutionDefs.
  Variable G: execution.

  Hypothesis FINDOM: fin_exec_full G.

  Lemma exists_nE thread :
    exists n, ~ Ex.acts_set G (Ev.ThreadEvent thread n).
  Proof using FINDOM.
    set (AA:=FINDOM).
    apply set_finite_exists_bigger with (f:=Ev.ThreadEvent thread) in AA.
    3: { ins. desf. }
    2: { apply Ev.eq_dec_actid. }
    desf.
    exists (1 + n). apply AA. lia.
  Qed.

  Definition acts_list: list Ev.actid :=
    filterP (Ex.acts_set G \₁ Ev.is_init)
            (proj1_sig (@constructive_indefinite_description _ _ FINDOM)).
  Lemma acts_set_findom:
    Ex.acts_set G \₁ Ev.is_init ≡₁ (fun e => In e acts_list).
  Proof using.
    unfold acts_list. destruct constructive_indefinite_description. simpl.
    split; intros e.
    all: rewrite in_filterP_iff; intuition. 
    apply i. apply H.
  Qed.
  Opaque acts_list.
End FinExecutionDefs.

Lemma fin_exec_same_events G G'
      (SAME: Ex.acts_set G ≡₁ Ex.acts_set G') (FIN: fin_exec G):
  fin_exec G'.
Proof using. unfold fin_exec in *. by rewrite <- SAME. Qed.

Lemma tid_is_init_fin_helper (S: Ev.actid -> Prop) thread
      (NT: thread <> Ev.tid_init)
      (FIN: set_finite (S \₁ Ev.is_init)):
  set_finite (S ∩₁ Tid_ thread).
Proof using. 
  rewrite set_split_complete with (s := Ev.is_init).
  apply set_finite_union. split.
  { eapply set_finite_mori; [| by apply set_finite_empty].
    red. unfolder. ins. desc. vauto. by destruct x. }
  eapply set_finite_mori; [| by apply FIN].
  red. basic_solver.
Qed. 

End FinExecution.
