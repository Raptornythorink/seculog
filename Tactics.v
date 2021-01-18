Require Import Bool.

Definition proj_sumbool {X Y} (x: {X} + {Y}) := if x then true else false.

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_rewrites:
  forall {E} x y (a b: E),
  (if x && y then a else b) =
  if x then if y then a else b else b.
Proof.
  intros.
  destruct x, y; simpl in *; try congruence.
Qed.


Ltac inv H := inversion H; try subst; clear H.

Ltac destr_term t :=
  match t with
  | context [if ?a then _ else _] => destruct a eqn:?
  | context [match ?a with _ => _ end] => destruct a eqn:?
  | _ => destruct t eqn:?
  end.

Ltac destr :=
  match goal with
  | |- context [if ?a then _ else _] => destr_term a
  | |- context [match ?a with _ => _ end] => destr_term a
  end.

Ltac destr_in H :=
  match type of H with
  | context [if ?a then _ else _] => destr_term a
  | context [match ?a with _ => _ end] => destr_term a
  end.

Ltac trim H :=
  match type of H with
  | ?a -> ?b =>
    let x := fresh in
    assert (x: a); [|specialize (H x); clear x]
  end.

