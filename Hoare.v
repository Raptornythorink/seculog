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
Require Import While Tactics WhileBigStep.

(** * 3 - Logique de Hoare  *)

Definition pred := state -> Prop.

Definition valid_hoare_triple (P: pred) (s: stmt) (Q: pred) : Prop :=
  forall env1 env2, P env1 -> bigstep env1 s env2 -> Q env2.

(** ** Question 3.1  *)

Theorem hoare_skip: forall P, valid_hoare_triple P Skip P.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inv H0.
  apply H.
Qed.

(* Règle [SÉQUENCE] dans le sujet *)
Theorem hoare_seq:
  forall P Q R s1 s2,
  valid_hoare_triple P s1 Q
  -> valid_hoare_triple Q s2 R
  -> valid_hoare_triple P (Seq s1 s2) R.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inv H2.
  eapply H0.
  - eapply H.
    + apply H1.
    + apply H6.
  - apply H8. 
Qed.

(* Règle [CONDITION]. *)
Theorem hoare_if:
  forall P Q c s1 s2,
  valid_hoare_triple (fun env => P env /\ eval_condP env c)  s1 Q
  -> valid_hoare_triple (fun env => P env /\ ~ eval_condP env c) s2 Q
  -> valid_hoare_triple P (If c s1 s2) Q.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inv H2.
  - eapply H.
    + split.
      * apply H1.
      * apply H8.
    + apply H9.
  - eapply H0.
    + split.
      * apply H1.
      * apply H8.
    + apply H9.  
Qed.

(* Règle [AFFECTATION]. On utilise [update_env] pour décrire l'effet de P[x <- E]. *)
Theorem hoare_assign:
  forall (P:pred) x e,
  valid_hoare_triple
    (fun env => P (update_state env x (eval_expr env e))) (Assign x e) P.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inv H0.
  apply H.
Qed.

(* Règle [STRENGTHEN]. *)
Theorem hoare_strengthen_pre:
  forall (P P' Q : pred) s,
  valid_hoare_triple P s Q
  -> (forall env, P' env -> P env)
  -> valid_hoare_triple P' s Q.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  eapply H.
  - apply H0.
    apply H1.
  - apply H2.
Qed.

(* Règle [WEAKEN]. *)
Theorem hoare_weaken_post:
  forall (P Q Q' : pred) s,
  valid_hoare_triple P s Q
  -> (forall env, Q env -> Q' env)
  -> valid_hoare_triple P s Q'.
Proof.
  intros.
  unfold valid_hoare_triple.
  unfold valid_hoare_triple in H.
  intros.
  apply H0.
  eapply H in H1.
  - apply H1.
  - apply H2.  
Qed.

(* Règle [WHILE]. *)
Theorem hoare_while:
  forall P c s I,
   valid_hoare_triple (fun env => P env /\ eval_condP env c) s P
   -> valid_hoare_triple
        P (While c I s) (fun env => P env /\ ~ eval_condP env c).
Proof.
  intros P c s inv.
  unfold valid_hoare_triple.
  intros.
  dependent induction H1.
  - split.
    + apply H0.
    + apply H1. 
  - eapply IHbigstep2.
    + eapply H.
    + eapply H.
      * split. apply H0. apply H1.
      * apply H1_. 
    + reflexivity.
Qed.

(** ** Question 3.2  *)
Lemma hoare_while':
  forall (P Q : pred ) c s I,
  valid_hoare_triple (fun env => I env /\ eval_condP env c) s I
  -> (forall env, P env -> I env)
  -> (forall env, I env /\ ~eval_condP env c -> Q env)
  -> valid_hoare_triple P (While c I s) Q.
Proof.
  intros.
  eapply hoare_weaken_post.
  - eapply hoare_strengthen_pre.
    + eapply hoare_while.
      apply H.
    + apply H0.
 - apply H1. 
Qed.

Open Scope Z_scope.

Definition factorielle n :=
  Seq
    (Assign "res" (Const 1))
    (While
      (Lt (Const 0) (Var "n"))
      (fun env => env "res" * Zfact (env "n") = Zfact n)
      (Seq
        (Assign "res" (Mul (Var "res") (Var "n")))
        (Assign "n" (Sub (Var "n") (Const 1)))
      )
    ).

(* Cette preuve devrait passer *)
(*
Lemma fact_correct_first_try:
  forall n, n >= 0 ->
            valid_hoare_triple (fun env => env "n" = n) (factorielle n) (fun env => env "res" = Zfact n).
Proof.
  intros n NPOS. unfold factorielle.
  eapply hoare_strengthen_pre.
  apply hoare_seq with (Q:= fun env => env "res" = 1 /\ env "n" = n). eapply hoare_assign.
  apply hoare_while'.
  - eapply hoare_strengthen_pre. eapply hoare_seq. eapply hoare_assign.
    apply hoare_assign.
    unfold update_state; simpl. intros.
    destruct H. rewrite <- H.
    rewrite <- Z.mul_assoc. f_equal.
    rewrite (Zfact_pos (env "n")). 2: lia. auto.
  - simpl. intros env [A B]; rewrite A, B. lia.
  - simpl. intros env [A B].
    rewrite <- A.
    rewrite Zfact_neg. 2: lia. lia.
  - unfold update_state; simpl. auto.
Qed.
*)

Fixpoint vars_affected (s: stmt) : list var :=
  match s with
  | Skip => []
  | Assign v e => [v]
  | Seq s1 s2 => vars_affected s1 ++ vars_affected s2
  | If c s1 s2 => vars_affected s1 ++ vars_affected s2
  | While c _ s => vars_affected s
  end.

Fixpoint wp (s: stmt) (Q: pred) : pred :=
  match s with
  | Skip         => Q
  | Assign v e   => fun env => Q (update_state env v (eval_expr env e))
  | Seq s1 s2    => wp s1 (wp s2 Q)
  | If c s1 s2   =>
    fun env =>
      (eval_condP env c -> wp s1 Q env) /\ (~ eval_condP env c -> wp s2 Q env)
  | While c II s =>
    fun env =>
      II env
      /\ let vv := vars_affected s in
         forall env',
         (forall x, ~ In x vv -> env x = env' x)
         -> (eval_condP env' c -> II env' -> wp s II env')
            /\ (~ eval_condP env' c -> II env' -> Q env')
  end.

Lemma bigstep_vars_affected:
  forall env1 s env2,
  bigstep env1 s env2
  -> forall x, ~ In x (vars_affected s)
  -> env1 x = env2 x.
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl in H0.
    unfold update_state.
    destruct (var_eq x x0).
    + exfalso.
      apply H0.
      auto.
    + reflexivity.
  - simpl in H0.
    rewrite in_app_iff in H0.
    apply Decidable.not_or in H0.
    destruct H0.
    apply IHbigstep1 in H0.
    apply IHbigstep2 in H2.
    rewrite H2 in H0.
    apply H0.
  - simpl in H0.
    rewrite in_app_iff in H0.
    apply Decidable.not_or in H0.
    destruct H0.
    apply IHbigstep in H0.
    apply H0.
  - simpl in H0.
    rewrite in_app_iff in H0.
    apply Decidable.not_or in H0.
    destruct H0.
    apply IHbigstep in H2.
    apply H2.
  - reflexivity.
  - simpl in H0.
    simpl in IHbigstep2. 
    assert (H0_copy: ~ In x (vars_affected s)).
    { apply H0. }
    apply IHbigstep1 in H0.
    apply IHbigstep2 in H0_copy.
    rewrite H0_copy in H0.
    apply H0.
Qed.

Lemma auto_hoare_while:
  forall
    c (I: pred) s (Q: pred) (IHs : valid_hoare_triple (wp s I) s I) env1 env2
    (Itrue: I env1)
    (CondTrue:
      forall env' : var -> val,
      (forall x : var, ~ In x (vars_affected s) -> env1 x = env' x)
      -> eval_condP env' c -> I env' -> wp s I env'
    )
   (CondFalse:
     forall env' : var -> val,
     (forall x : var, ~ In x (vars_affected s) -> env1 x = env' x)
     -> ~ eval_condP env' c -> I env' -> Q env'
   )
   (Heval : bigstep env1 (While c I s) env2),
    Q env2.
Proof.
  intros c I s Q IHs env1 env2 Itrue CondTrue CondFalse Heval.
  dependent induction Heval.
  - eapply CondFalse.
    + auto.
    + apply H.
    + apply Itrue.
  - clear IHHeval1.
    eapply IHHeval2 with (s0:=s) (I0:=I) (c0:=c); auto.
    + eapply IHs.
      * eapply CondTrue.
        -- tauto.
        -- apply H.
        -- apply Itrue.
      * apply Heval1.
    + intros.
      eapply CondTrue.
      * intros. assert (env x = env' x).
        eapply bigstep_vars_affected.
        -- apply Heval1.
        -- apply H3.
        -- rewrite H4.
           apply H0 in H3.
           apply H3.
      * apply H1.
      * apply H2.
    + intros.
      eapply CondFalse.
      * intros. assert (env x = env' x).
        eapply bigstep_vars_affected.
        -- apply Heval1.
        -- apply H3.
        -- rewrite H4.
           apply H0 in H3.
           apply H3.
      * apply H1.
      * apply H2.
Qed.

Theorem auto_hoare: forall s Q, valid_hoare_triple (wp s Q) s Q.
Proof.
  intros.
  dependent induction s.
  - apply hoare_skip.
  - apply hoare_assign.
  - eapply hoare_seq.
    + apply IHs1.
    + apply IHs2.
  - simpl.
    unfold valid_hoare_triple.
    intros.
    destruct H.
    inversion H0.
    + eapply IHs1.
      * apply H. 
        apply H7.
      * apply H8.
    + eapply IHs2.
      * apply H1.
        apply H7.
      * apply H8.
  - simpl.
    unfold valid_hoare_triple.
    intros.
    destruct H.
    eapply auto_hoare_while.
    + apply IHs.
    + apply H.
    + intros.
      apply H1 in H3.
      apply H3.
      apply H2.
      apply H4.
    + apply H1.
    + apply H0.
Qed.    

Lemma auto_hoare':
  forall (P: pred) s Q,
  (forall env, P env -> wp s Q env)
  -> valid_hoare_triple P s Q.
Proof.
  intros.
  eapply hoare_strengthen_pre.
  - apply auto_hoare.
  - apply H.  
Qed.
