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

(** ** Sémantique à grands pas du langage While  *)

(** On définit l'évaluation d'une instruction (un *statement* [stmt]) comme un
prédicat inductif. Un prédicat inductif donne la liste des différents cas dans
lesquels ce prédicat est vrai, de la même manière qu'une déclaration de type de
données inductif donne la liste des différentes manières de construire une
valeur de ce type.

Dans notre cas, le prédicat a pour type [state -> stmt -> state -> Prop], ce que
l'on peut lire comme un prédicat ([ -> Prop]) qui dépend de trois paramètres: un
environnement initial, une instruction et un environnement final. Ainsi, on peut
lire [bigstep env s env'] comme "L'exécution de l'instruction [s] dans
l'environnement [env] conduit à l'environnement [env']." *)

(** * Question 1.1  *)

Inductive bigstep : state -> stmt -> state -> Prop :=
| bigstep_skip: forall env, bigstep env Skip env
| bigstep_assign:
  forall env x e,
  bigstep env (Assign x e) (update_state env x (eval_expr env e))
| bigstep_seq:
  forall env s1 env' s2 env'',
  bigstep env s1 env'
  -> bigstep env' s2 env''
  -> bigstep env (Seq s1 s2) env''
| bigstep_if_true:
  forall env c s1 s2 env',
  eval_condP env c
  -> bigstep env s1 env'
  -> bigstep env (If c s1 s2) env'
| bigstep_if_false:
  forall env c s1 s2 env',
  ~ eval_condP env c
  -> bigstep env s2 env'
  -> bigstep env (If c s1 s2) env'
| bigstep_while_false:
  forall env c I s,
  ~ eval_condP env c
  -> bigstep env (While c I s) env
| bigstep_while_true:
  forall env c I s env' env'',
  eval_condP env c
  -> bigstep env s env'
  -> bigstep env' (While c I s) env''
  -> bigstep env (While c I s) env''
.

(** * 2 - Quelques détails sur des tactiques utiles en Coq  *)

Example test_bigstep_seq_assign:
  forall env,
  bigstep
    env
    (Seq (Assign "x" (Const 1)) (Assign "y" (Const 2)))
    (update_state (update_state env "x" 1) "y" 2).
Proof.
  intros env.
  eapply bigstep_seq.
  (* On a ici une variable existentielle [?env2] qui apparaît dans le sous-but
  actuel et dans le second sous-but. *)
  apply bigstep_assign.
  (* L'application de [eval_assign] ci-dessus a "résolu" cette variable
  existentielle et remplacé [env2] dans le second sous-but (le seul qui reste à
  présent) par sa valeur [update_env env "x" 1]. *)
  apply bigstep_assign.
  Restart.                      (* Cette commande recommence la preuve depuis le début: on peut aussi utiliser [constructor] et [econstructor] *)
  intros.
  econstructor.                 (* [constructor] ne fonctionne pas ici, car on
  doit donner l'environnement intermédiaire pour [eval_seq]. [econstructor]
  fonctionne, en revanche.*)
  constructor.
  constructor.
Qed.

Lemma test_bigstep_while:
  forall env,
  env "x" = 2
  -> bigstep
      env
      (While
        (Not (Eq (Var "x") (Const 0)))
        (fun _ => True)
        (Assign "x" (Sub (Var "x") (Const 1)))
      )
      (update_state (update_state env "x" 1) "x" 0).
Proof.
  (* La preuve suivante devrait être correcte *)
  intros env EQ.
  eapply bigstep_while_true.
  - simpl. rewrite EQ. lia.
  - apply bigstep_assign.
  - eapply bigstep_while_true.
    + simpl. rewrite EQ. unfold update_state; simpl. lia.
    + apply bigstep_assign.
    + simpl. rewrite EQ. simpl. apply bigstep_while_false.
      simpl. unfold update_state; simpl. lia.
Qed.
