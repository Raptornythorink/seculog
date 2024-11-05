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
Require Import WhileBigStep.
Require Import Lia.

Fixpoint exec_prog (fuel: nat) (env: state) (i: stmt) : option state :=
  match fuel with
  | O => None
  | S fuel' =>
    match i with
    | Skip => Some env
    | Assign v e => Some (update_state env v (eval_expr env e))
    | Seq s1 s2 =>
      match exec_prog fuel' env s1 with
      | Some env' => exec_prog fuel' env' s2
      | None => None
      end
    | If c s1 s2 =>
      if eval_cond env c
      then exec_prog fuel' env s1
      else exec_prog fuel' env s2
    | While c inv s =>
      if (eval_cond env c)
      then match exec_prog fuel' env s with
          | Some env' => exec_prog fuel' env' (While c inv s)
          | None => None
          end
      else Some env
    end
  end.

Definition p1 :=
  Seq
    (Assign "x" (Const 10%Z))
    (Seq
      (Assign "sum" (Const 0%Z))
      (While
        (Not (Eq (Var "x") (Const 0%Z)))
        (fun _ => True)
        (Seq
          (Assign "sum" (Add (Var "sum") (Var "x")))
          (Assign "x" (Sub (Var "x") (Const 1%Z)))
        )
      )
    ).

(* Le calcul suivant devrait retourner [Some 55]. *)
Compute
  option_map (fun env => env "sum")
  (exec_prog 30 (fun _ => 0%Z) p1).

Theorem exec_prog_bigstep:
  forall fuel s i s', exec_prog fuel s i = Some s' -> bigstep s i s'.
Proof.
  intros fuel.
  induction fuel.
  - discriminate.
  - intros. simpl in H. destruct i.
    + inversion H. apply bigstep_skip.
    + inversion H. apply bigstep_assign.
    + destruct (exec_prog fuel s i1) eqn:H1.
      * econstructor.
        ** apply IHfuel. apply H1.
        ** apply IHfuel. apply H.
      * discriminate.
    + destruct (eval_cond s c) eqn:H1.
      * eapply bigstep_if_true.
        ** apply eval_cond_true. apply H1.
        ** apply IHfuel. apply H.
      * eapply bigstep_if_false.
        ** apply eval_cond_false. apply H1.
        ** apply IHfuel. apply H.
    + destruct (eval_cond s c) eqn:H1.
      * destruct (exec_prog fuel s i) eqn:H2.
        ** eapply bigstep_while_true.
          *** apply eval_cond_true. apply H1.
          *** apply IHfuel. apply H2.
          *** apply IHfuel. apply H.
        ** discriminate.
      * inversion H.
        apply bigstep_while_false.
        apply eval_cond_false.
        rewrite <- H2.
        apply H1.
Qed.

Lemma exec_prog_more_fuel:
  forall f s i s',
  exec_prog f s i = Some s'
  -> forall f', f' >= f
  -> exec_prog f' s i = Some s'.
Proof.
  intros fuel.
  induction fuel.
  - intros.
    inversion H.
  - intros.
    simpl in H.
    destruct f'.
    + inversion H0.
    + simpl.
      assert (f' >= fuel).
      lia.
      destruct i.
      * inversion H. reflexivity.
      * inversion H. reflexivity.
      * destruct (exec_prog fuel s i1) eqn:Hi1.
        ** eapply IHfuel in Hi1.
          *** rewrite Hi1.
              eapply IHfuel in H.
              **** rewrite H.
                   reflexivity.
              **** lia.
          *** lia.
        ** discriminate.
      * destruct (eval_cond s c) eqn:Hc.
        ** eapply IHfuel in H.
          *** rewrite H.
              reflexivity.
          *** lia.
        ** eapply IHfuel in H.
          *** rewrite H.
              reflexivity.
          *** lia.
      * destruct (eval_cond s c) eqn:Hc.
        ** destruct (exec_prog fuel s i) eqn:Hi.
           *** eapply IHfuel in Hi.
               **** rewrite Hi.
                    eapply IHfuel in H.
                    ***** rewrite H.
                          reflexivity.
                    ***** lia.
               **** lia.
           *** discriminate.
        ** inversion H.
           reflexivity.
Qed.

Theorem bigstep_exec_prog:
  forall s i s',
  bigstep s i s'
  -> exists fuel, exec_prog fuel s i = Some s'.
Proof.
  intros.
  induction H.
  - exists 1.
    simpl.
    reflexivity.
  - exists 1.
    simpl.
    reflexivity.
  - destruct IHbigstep1 as [fuel1 IH1].
    destruct IHbigstep2 as [fuel2 IH2].
    exists (S (max fuel1 fuel2)).
    simpl.
    rewrite (exec_prog_more_fuel fuel1 env s1 env').
    + rewrite (exec_prog_more_fuel fuel2 env' s2 env'').
      * reflexivity.
      * apply IH2.
      * lia.
    + apply IH1.
    + lia.
  - destruct IHbigstep as [fuel IH].
    exists (S fuel).
    simpl.
    apply eval_cond_true in H.
    rewrite H.
    apply IH.
  - destruct IHbigstep as [fuel IH].
    exists (S fuel).
    simpl.
    apply eval_cond_false in H.
    rewrite H.
    apply IH.
  - exists 1.
    simpl.
    apply eval_cond_false in H.
    rewrite H.
    reflexivity.
  - destruct IHbigstep1 as [fuel1 IH1].
    destruct IHbigstep2 as [fuel2 IH2].
    exists (S (max fuel1 fuel2)).
    simpl.
    apply eval_cond_true in H.
    rewrite H.
    rewrite (exec_prog_more_fuel fuel1 env s env').
    + rewrite (exec_prog_more_fuel fuel2 env' (While c I s) env'').
      * reflexivity.
      * apply IH2.
      * lia.
    + apply IH1.
    + lia.
Qed.
