Require Import List Bool ZArith Psatz String.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Opaque Z.mul.
Require Import Tactics.

(** * Un langage d'expressions *)

(** Le langage Imp est un langage impératif minimaliste. Les valeurs manipulées
dans ce langage sont des entiers [val := Z] et les variables sont
représentées par un identifiant (naturel). *)

Definition var := string.
Definition val := Z.
Definition var_eq := string_dec.

(** ** Les expressions, conditions et instructions *)
(** Les expressions [expr] peuvent être des constantes [Const n], des variables
[Var n], ou bien des opérations binaires ([Add], [Mul], [Sub] sur d'autres
expressions). *)

Inductive binop : Set :=
| Badd
| Bmul
| Bsub.

Inductive expr : Set :=
| Const (n: Z)
| Var (v: var)
| Binop (b: binop) (e1 e2: expr).

Definition envt := var -> val.

(** On définit un environnement par défaut [default_env] qui associe à toute
variable la valeur [0]. *)

Definition default_envt : envt := fun _ => 0.

(** [update_env e x z] crée un nouvel environnement à partir de [e] en associant
la valeur [z] à la variable [x]. *)

Definition update_env (e: envt) (x: var) (z: Z) :=
  fun y => if var_eq x y then z else e y.

Definition lookup_env (e: envt) (x: var) :=
  e x.

Lemma var_eq_true:
  forall {A: Type} (a b: A) v,
    (if var_eq v v then a else b) = a.
Proof.
  intros.
  destruct (var_eq v v); congruence.
Qed.

Lemma var_eq_false:
  forall {A: Type} (a b: A) v v' (neq: v <> v'),
    (if var_eq v v' then a else b) = b.
Proof.
  intros.
  destruct (var_eq v v'); try congruence.
Qed.

Lemma lookup_update_same:
  forall (e: envt) x z,
    lookup_env (update_env e x z) x = z.
Proof.
  unfold lookup_env, update_env. simpl. intros.
  rewrite var_eq_true. auto.
Qed.

Lemma lookup_update_other:
  forall (e: envt) x y z,
    x <> y ->
    lookup_env (update_env e x z) y = lookup_env e y.
Proof.
  unfold lookup_env, update_env. simpl. intros.
  rewrite var_eq_false; auto.
Qed.

Lemma lookup_update_eq:
  forall (e: envt) x y z,
    lookup_env (update_env e x z) y = if var_eq x y then z else lookup_env e y.
Proof.
  intros.
  destr.
  subst. apply lookup_update_same.
  apply lookup_update_other. auto.
Qed.

(** La fonction d'évaluation des expressions [eval_expr] évalue récursivement en
suivant la structure des expressions. *)

Definition eval_binop (b: binop) (z1 z2 : Z) : Z :=
  match b with
  | Badd =>  (z1 + z2)
  | Bmul =>  (z1 * z2)
  | Bsub =>  (z1 - z2)
  end.

Fixpoint eval_expr (env: envt) (e: expr) : Z :=
  match e with
  | Const n => n
  | Var v => lookup_env env v
  | Binop b e1 e2 => eval_binop b (eval_expr env e1) (eval_expr env e2)
  end.

Inductive cond : Set :=
| Eq (e1 e2: expr)
| Lt (e1 e2: expr)
| And (c1 c2: cond)
| Or (c1 c2: cond)
| Not (c: cond).

Fixpoint eval_cond (env: envt) (c: cond) : bool :=
  match c with
  | Eq e1 e2 => Z.eqb (eval_expr env e1) (eval_expr env e2)
  | Lt e1 e2 => Z.ltb (eval_expr env e1) (eval_expr env e2)
  | And c1 c2 => eval_cond env c1 && eval_cond env c2
  | Or c1 c2 => eval_cond env c1 || eval_cond env c2
  | Not c => negb (eval_cond env c)
  end.


(* On étend le type des instructions du langage While avec une instruction
[Output e] qui affiche la valeur de [e]. *)

Inductive stmt  :=
| Skip
| Assign (v: var) (e: expr)
| Seq (s1 s2: stmt)
| If (c: cond) (s1 s2: stmt)
| While (c: cond) (s: stmt)
| Output (e: expr)
.

(* La sémantique à grands pas est adaptée pour inclure une trace de type [list
Z] : la liste des entiers que l'on a affichés durant l'exécution du programme.
 *)

Inductive bigstep : envt -> stmt -> envt -> list Z -> Prop :=
| bigstep_skip: forall e, bigstep e Skip e []
| bigstep_assign: forall x e env, bigstep env (Assign x e) (update_env env x (eval_expr env e)) []
| bigstep_seq: forall env1 env2 env3 i1 i2 t1 t2,
    bigstep env1 i1 env2 t1 ->
    bigstep env2 i2 env3 t2 ->
    bigstep env1 (Seq i1 i2) env3 (t1 ++ t2)
| bigstep_if_true:
    forall env c i1 i2 env' t,
      eval_cond env c = true ->
      bigstep env i1 env' t ->
      bigstep env (If c i1 i2) env' t
| bigstep_if_false:
    forall env c i1 i2 env' t,
      eval_cond env c = false ->
      bigstep env i2 env' t ->
      bigstep env (If c i1 i2) env' t
| bigstep_while_true:
    forall env c i env' env'' t1 t2,
      eval_cond env c = true ->
      bigstep env i env' t1 ->
      bigstep env' (While c i) env'' t2 ->
      bigstep env (While c i) env'' (t1 ++ t2)
| bigstep_while_false:
    forall env c i,
      eval_cond env c = false ->
      bigstep env (While c i) env []
| bigstep_output:
    forall env e,
      bigstep env (Output e) env [eval_expr env e].

