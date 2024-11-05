Require Import Coq.Program.Equality.
Require Import List ZArith.
Require Import Arith.
Require Import Psatz.
Require Import Lia.
Import ListNotations.
Open Scope nat_scope.
Close Scope Z_scope.
Require Import String.
Open Scope string_scope.
Require Import While Tactics.
Require Import WhileSmallStep WhileBigStep.

Lemma star_seq:
  forall s1 env1 env2,
  star s1 env1 Skip env2
  -> forall s2 s3 env3,
  star s2 env2 s3 env3
  -> star (Seq s1 s2) env1 s3 env3.
Proof.
  intros s1 env1 env2 Hstar.
  dependent induction Hstar; simpl; intros.
  - eapply star_step. apply step_seq_skip. apply H.
  - apply IHHstar in H0. eapply star_step. apply step_seq. apply H. apply H0. reflexivity.
Qed.


Theorem bigstep_star:
  forall i env env', bigstep env i env' -> star i env Skip env'.
Proof.
  intros.
  induction H.
  - apply star_refl.
  - eapply star_step. apply step_assign. apply star_refl.
  - eapply star_seq. apply IHbigstep1. apply IHbigstep2.
  - eapply star_step. apply step_if_true. apply H. apply IHbigstep.
  - eapply star_step. apply step_if_false. apply H. apply IHbigstep.
  - eapply star_step. apply step_while_false. apply H. apply star_refl.
  - eapply star_step. apply step_while_true. apply H. eapply star_seq. apply IHbigstep1. apply IHbigstep2. 
Qed.

Lemma step_bigstep:
  forall i env i' env',
    step i env i' env' ->
    forall env'',
      bigstep env' i' env'' ->
      bigstep env i env''.
Proof.
  intros i env i' env' H.
  induction H.
  - intros. inversion H. apply bigstep_assign.
  - intros. apply bigstep_if_true. apply H. apply H0.
  - intros. apply bigstep_if_false. apply H. apply H0.
  - intros. inversion H0. eapply bigstep_while_true. apply H. apply H4. apply H6.
  - intros. inversion H0. eapply bigstep_while_false. rewrite H3 in H. apply H.
  - intros. inversion H0. eapply bigstep_seq. apply IHstep. apply H4. apply H6.
  - intros. eapply bigstep_seq. eapply bigstep_skip. apply H.
Qed.

Theorem star_bigstep:
  forall i env env', star i env Skip env' -> bigstep env i env'.
Proof.
  intros.
  dependent induction H.
  - apply bigstep_skip.
  - eapply step_bigstep in IHstar. apply IHstar. apply H. reflexivity. 
Qed.
