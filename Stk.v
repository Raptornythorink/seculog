Require Import List ZArith.
Require Import Arith.
Require Import Psatz.
Require Import Omega.
Import ListNotations.
Close Scope nat_scope.
Open Scope Z_scope.
Opaque Z.mul.
Require Import While Tactics.

(** * Machine à pile  *)

(** On propose maintenant d'étudier un langage plus _bas-niveau_ : une machine à
pile. Ce langage ne comporte pas d'expressions. On déconstruit les expressions
en instructions plus simples, qui manipulent une pile. *)

(** On définit une interprétation des entiers comme booléens et inversement. Un
entier égal à 0 correspond au booléen [false], toutes les autres valeurs
correspondent au booléen [true]. Dans l'autre sens, on associe l'entier 0 au
booléen [false] et l'entier 1 au booléen [true]. *)

Definition bool_of_Z (n: Z) := if Z.eq_dec n 0 then false else true.
Definition Z_of_bool (b: bool) := if b then 1 else 0.


(** On dispose des opérateurs binaires ([binop]) et unaires ([unop]) suivants.
*)
Inductive binop :=
  Badd                          (* addition *)
| Bsub                          (* soustraction *)
| Bmul                          (* multiplication *)
| Beq                           (* test d'égalité *)
| Blt                           (* test d'infériorité *)
| Band                          (* conjonction *)
| Bor.                          (* disjonction *)

Inductive unop :=
| Unot.         (* négation binaire *)

(** L'évaluation d'une opération binaire sur deux arguments. *)
Definition eval_binop (b: binop) (n1 n2: Z) : Z :=
  match b with
  | Badd => n1 + n2
  | Bsub => n1 - n2
  | Bmul => n1 * n2
  | Beq => Z_of_bool (Z.eqb n1 n2)
  | Blt => Z_of_bool (Z.ltb n1 n2)
  | Band => Z_of_bool (bool_of_Z n1 && bool_of_Z n2)
  | Bor => Z_of_bool (bool_of_Z n1 || bool_of_Z n2)
  end.

(** L'évaluation d'une opération unaire sur un argument. *)
Definition eval_unop (u: unop) (n: Z) : Z :=
  match u with
  | Bnot => Z_of_bool (negb (bool_of_Z n))
  end.

Inductive instr : Set :=
| SJmp (label: nat)             (* saute au label [label] si le sommet de pile
  contient une valeur vraie *)
| SLabel (label: nat)           (* label [label] *)
| SConst (n: Z)                 (* charge la constante [n] sur la pile *)
| SLoad (x: var)                (* charge la valeur de la variable [x] sur la pile *)
| SStore (x: var)               (* écrit la valeur au sommet de la pile dans la variable [x] *)
| SBinop (b: binop)             (* applique l'opération binaire [b] sur les deux arguments au sommet de la pile *)
| SUnop (u: unop)               (* applique l'opération unaire [u] sur l'argument au sommet de la pile *)
| SOutput                       (* affiche l'entier au sommet de la pile *)
| SHalt.                        (* termine l'exécution *)

(** On définit un programme [sprog] comme une liste d'instructions [instr].
L'état [state] d'un programme est une fonction associant à chaque variable une
valeur. La pile [stack] est une liste de valeurs. *)

Definition sprog := list instr.
Definition state := envt.
Definition stack := list val.

(** On définit le type [mstate] qui dénote l'état d'un programme.

L'état [Finished s tr] indique que le programme a terminé correctement avec [s]
l'état final des variables, et [tr] la trace du programme (les entiers qui ont
été affichés).

L'état [MState p1 p2 st s tr] est un état en cours d'exécution, où :
- [p1] contient les instructions du programme *avant* le point de programme
courant (ce qui a déjà été exécuté)
- [p2] contient le programme à partir du point de programme courant (ce que l'on
 doit exécuter)
- [st] est l'état courant des variables
- [s] est la pile courante
- [tr] est la trace courante (ce qui a été affiché jusqu'à maintenant).

On doit garder [p1] (ce qu'on a déjà exécuté) afin de se souvenir du programme
lorsque l'on devra sauter à un label.

 *)
Inductive mstate : Type :=
| Finished (s: state) (tr: list Z)
| MState (p1 p2: list instr) (st: state) (s: stack) (tr: list Z).

(* On cherche un label [lbl] dans un programme [p]. Cette fonction [find_label]
   retourne [Some (p1,p2)] si le label [lbl] est trouvé dans le programme. [p1]
   correspond au morceau de programme avant le label, et [p2] correspond au
   morceau de programme à partir du label (inclus).

   Si le label n'est pas présent dans le programme, la fonction renvoie [None].
 *)

Definition is_label l i : {i = SLabel l} + {i <> SLabel l}.
Proof.
  destruct i; try (right; congruence).
  destruct (Nat.eq_dec label l).
  left; eauto. right; congruence.
Defined.

Fixpoint find_label (p: sprog) (lbl: nat) : option (sprog * sprog) :=
  match p with
  | [] => None
  | i::r => if is_label lbl i
            then Some ([], i::r)
            else
              match find_label r lbl with
              | None => None
              | Some (a, b) => Some (i :: a, b)
              end
  end.

(* On note que la concaténation des sous-programmes renvoyés par [find_label]
est égale au programme original. *)

Lemma find_label_whole_prog:
  forall p l a b,
    find_label p l = Some (a, b) ->
    p = a ++ b.
Proof.
  induction p; simpl; intros; eauto. inv H.
  destr_in H.
  - inv H. reflexivity.
  - repeat destr_in H; inv H.
    apply IHp in Heqo. subst.
    simpl. reflexivity.
Qed.

(** La fonction [exec_instr] ci-dessous effectue un pas d'exécution, où :
- [p1] est le programme déjà exécuté jusqu'à maintenant
- [p2] est le programme qui reste à être exécuté
- [st] est l'état courant des variables
- [s] est la pile courante
- [tr] est la trace courante.

Cette fonction renvoie l'état [mstate] obtenu après un pas d'exécution.
 *)

Definition exec_instr (p1 p2: sprog) (st: state) (s: stack) tr : option mstate :=
  match p2 with
  | [] =>
    (* Plus rien à exécuter, erreur ! *)
    None
  | i :: p2 =>
    match i with
    | (SConst n) => Some (MState (p1 ++ [i]) p2 st (n :: s) tr)
    (** Il s'agit de placer une constante en sommet de pile. La pile [s] devient
    [n :: s] *)
    | (SLoad x) => Some (MState (p1 ++ [i]) p2 st (st x :: s) tr)
    (** similaire au cas précédent  *)
    | (SStore x) =>
      (** Il s'agit d'écrire dans la variable [x] la valeur du sommet de pile.  *)
      match s with
      | v :: r => Some (MState (p1 ++ [i]) p2 (update_env st x v) r tr)
      (** Premier cas: il existe une valeur [v] en sommet de pile : on l'enlève
          de la pile, on met à jour l'état et on incrémente le compteur de
          programme [pc]. *)
      | [] => None (** Second cas : la pile est vide. On renvoie une erreur. *)
      end
    | SLabel lbl =>
      (* Un label : aucun impact sur la sémantique, on passe à l'instruction
      suivante. *)
      Some (MState (p1 ++ [i]) p2 st s tr)
    | SJmp lbl =>
      (** Si le sommet de pile est une condition vraie, on saute au label [lbl].
          Sinon on avance normalement. *)
      match s with
        b :: r =>
        if bool_of_Z b
        then match find_label (p1 ++ i :: p2) lbl with
             | Some (p1, p2) => Some (MState p1 p2 st r tr)
             | None => None
             end
        else Some (MState (p1 ++ [i]) p2 st r tr)
      | _ => None
      end
    | SBinop b =>
      match s with
        e1 :: e2 :: r => Some (MState (p1 ++ [i]) p2 st (eval_binop b e1 e2 :: r) tr)
      (* Opération binaire : on retire deux valeurs du sommet de la pile, on
         calcule le résultat de l'opération, que l'on pousse sur la pile. *)
      | _ => None
      end
    | SUnop u =>
      match s with
        e1 :: r => Some (MState (p1 ++ [i]) p2 st (eval_unop u e1 :: r) tr)
      (* Opération unaire : on retire une valeur du sommet de la pile, on
         calcule le résultat de l'opération, que l'on pousse sur la pile. *)
      | _ => None
      end
    | SOutput =>
      match s with
        e1 :: r => Some (MState (p1 ++ [i]) p2 st r (tr ++ [e1]))
      (* On dépile une valeur, que l'on affiche. *)
      | _ => None
      end
    | SHalt => Some (Finished st tr) (** On a fini l'exécution du programme.  *)
    end

  end.

(** L'évaluation d'un programme est définie par le prédicat [eval_sprog]. On lit
[eval_sprog ms1 ms2] comme suit : en partant de l'état de programme [ms1], on
aboutit en 0, 1 ou plus de pas ([exec_instr]) à l'état [ms2]. Le constructeur
[eval_zero] correspond à 0 pas, et [eval_plus] à 1 ou plusieurs pas. *)

Inductive eval_sprog : mstate -> mstate -> Prop :=
| eval_zero:
    forall ms,
      (* 0 pas *)
      eval_sprog ms ms
| eval_plus:
    forall p1 p2 st s tr ms ms',
      exec_instr p1 p2 st s tr = Some ms ->
      eval_sprog ms ms' ->
      (* 1 pas + 0, 1 ou plusieurs pas *)
      eval_sprog (MState p1 p2 st s tr) ms'.

(* On peut finir en un seul pas. *)
Lemma eval_one:
  forall p1 p2 st s tr ms,
    exec_instr p1 p2 st s tr = Some ms ->
    eval_sprog (MState p1 p2 st s tr) ms.
Proof.
  intros.
  eapply eval_plus. eauto.
  apply eval_zero.
Qed.

(* Transitivité : on peut faire deux fois un nombre quelconque de pas. *)
Lemma eval_trans:
  forall ms1 ms2,
    eval_sprog ms1 ms2 ->
    forall ms3,
      eval_sprog ms2 ms3 ->
      eval_sprog ms1 ms3.
Proof.
  induction 1; simpl; intros; eauto.
  eapply eval_plus; eauto.
Qed.

