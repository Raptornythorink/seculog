Require Import Stk While Psatz ZArith List.
Require Import Tactics.
Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.


Definition compile_binop b :=
  match b with
  | Badd => Stk.Badd
  | Bmul => Stk.Bmul
  | Bsub => Stk.Bsub
  end.

Fixpoint compile_expr (e: expr) : list instr :=
   [].

Lemma compile_expr_correct:
  forall e code b st stk tr,
  eval_sprog (MState code (compile_expr e ++ b) st stk tr)
             (MState (code ++ compile_expr e) b st (eval_expr st e :: stk) tr).
Proof.
   Admitted.


Fixpoint compile_cond (c: cond) : list instr :=
   [].

Lemma bool_of_Z_of_bool:
  forall b,
    bool_of_Z (Z_of_bool b) = b.
Proof.
  destruct b; simpl; reflexivity.
Qed.

Lemma compile_cond_correct:
  forall c code b st stk tr,
    eval_sprog (MState code (compile_cond c ++ b) st stk tr)
               (MState (code ++ compile_cond c) b st (Z_of_bool (eval_cond st c) :: stk) tr).
Proof.
   Admitted.



Fixpoint compile_stmt (next_lbl: nat) (i: stmt) : (nat * list instr) :=
  match i with
  | Skip => (next_lbl, [])
  | Assign x e =>
    (next_lbl, compile_expr e ++ [SStore x])
  | If c s1 s2 =>
    let lbl_true := next_lbl in
    let lbl_end := next_lbl + 1 in
    let next_lbl := next_lbl + 2 in
    let (next_lbl, cs2) := compile_stmt next_lbl s2 in
    let (next_lbl, cs1) := compile_stmt next_lbl s1 in
    (next_lbl,
     compile_cond c ++
                  [SJmp lbl_true] ++
                  cs2 ++
                  [SConst 1;
                  SJmp lbl_end;
                  SLabel lbl_true] ++ cs1 ++ [SLabel lbl_end])
         | _ => (next_lbl, [])
  end.

(* Tous les labels de [l] sont strictement inférieurs à [n]. *)
Definition labels_below l n :=
  Forall (fun i =>
            match i with
            | SLabel l => l < n
            | _ => True
            end
         ) l.

(* Tous les labels de [l] sont supérieurs ou égaux à [n]. *)
Definition labels_above l n :=
  Forall (fun i =>
            match i with
            | SLabel l => n <= l
            | _ => True
            end
         ) l.

(* Lemmes de réécriture *)
Lemma labels_below_app:
  forall l1 l2 n,
    labels_below (l1 ++ l2) n <-> (labels_below l1 n) /\ (labels_below l2 n).
Proof.
  intros; unfold labels_below. rewrite Forall_app. tauto.
Qed.

Lemma labels_below_cons:
  forall i r n,
    labels_below (i :: r) n <-> match i with SLabel l => l < n | _ => True end /\ labels_below r n.
Proof.
  split; intros.
  inv H. auto. destruct H; constructor; eauto.
Qed.

Lemma labels_above_app:
  forall l1 l2 n,
    labels_above (l1 ++ l2) n <-> (labels_above l1 n) /\ (labels_above l2 n).
Proof.
  intros; unfold labels_above. rewrite Forall_app. tauto.
Qed.

Lemma labels_above_cons:
  forall i r n,
    labels_above (i :: r) n <-> match i with SLabel l => n <= l | _ => True end /\ labels_above r n.
Proof.
  split; intros.
  inv H. auto. destruct H; constructor; eauto.
Qed.

(* Le code issu de la compilation d'une expression ne devraient pas contenir de
labels, donc tous les labels sont en dessous/au dessus de n'importe quel seuil !
*)
Lemma labels_below_compile_expr:
  forall e n,
    labels_below (compile_expr e) n.
Proof.
(* Décommenter la preuve suivante devrait suffire. *)
(*
 induction e; simpl; intros; repeat constructor; eauto.
  rewrite ! labels_below_app.
  intuition. red. constructor; auto.
*)
 Admitted.

Lemma labels_above_compile_expr:
  forall e n,
    labels_above (compile_expr e) n.
Proof.
(* Décommenter la preuve suivante devrait suffire. *)
(*
  induction e; simpl; intros; repeat constructor; eauto.
  rewrite ! labels_above_app.
  intuition. red. constructor; auto.
*)
 Admitted.

(* Idem pour la compilation des conditions *)
Lemma labels_below_compile_cond:
  forall c n,
    labels_below (compile_cond c) n.
Proof.
(* Décommenter la preuve suivante devrait suffire. *)
(*
  induction c; simpl; intros; eauto;
    repeat (rewrite ? labels_below_app;
            intuition;
            try apply labels_below_compile_expr;
            red; simpl; eauto).
*)
 Admitted.

Lemma labels_above_compile_cond:
  forall c n,
    labels_above (compile_cond c) n.
Proof.
(* Décommenter la preuve suivante devrait suffire. *)
(*
  induction c; simpl; intros; eauto;
    repeat (rewrite ? labels_above_app;
            intuition;
            try apply labels_above_compile_expr;
            red; simpl; eauto).
*)
 Admitted.


(* La preuve suivante dit que si on cherche un label [l] dans [a++b], et que
tous les labels de [a] sont plus petits que [n], et que [l] est plus grand que
[n], alors, on ne risque de trouver ce label que dans [b]. *)
Lemma find_label_below:
  forall n l (LE: n <= l) a,
    labels_below a n ->
    forall b,
      find_label (a++b) l = match find_label b l with
                              None => None
                            | Some (p1, p2) => Some (a++p1, p2)
                            end.
Proof.
  induction 2; simpl; intros; eauto.
  repeat destr; auto.
  rewrite IHForall. clear IHForall.
  destr.
  - subst. lia.
  - destr. destr. reflexivity. auto.
Qed.

(* La preuve suivante dit que si on cherche un label [l] dans [a++b], et que
tous les labels de [a] sont plus grands que [n], et que [l] est plus petit que
[n], alors, on ne risque de trouver ce label que dans [b]. *)
Lemma find_label_above:
  forall n l (LE: l < n) a,
    labels_above a n ->
    forall b,
      find_label (a++b) l = match find_label b l with
                              None => None
                            | Some (p1, p2) => Some (a++p1, p2)
                            end.
Proof.
  induction 2; simpl; intros; eauto.
  repeat destr; auto.
  rewrite IHForall. clear IHForall.
  destr.
  - subst. lia.
  - destr. destr. reflexivity. auto.
Qed.

(* La preuve suivante dit que si on cherche un label [l] dans [a++b], et que
l'on trouve [l] dans [a], alors on n'a plus qu'à concaténer [b] à la liste [p2].
*)
Lemma find_label_prefix:
  forall a b l p1 p2,
      find_label a l = Some (p1, p2) ->
      find_label (a++b) l = Some (p1, p2 ++ b).
Proof.
  induction a; simpl; intros; eauto. inv H.
  destr. inv H. reflexivity.
  repeat destr_in H; inv H.
  eapply IHa in Heqo.
  rewrite Heqo. reflexivity.
Qed.

(* Si les labels sont en dessous de [nl] et que [nl <= nl'], alors les labels
sont en dessous de [nl']. *)
Lemma labels_below_slack:
  forall l nl,
    labels_below l nl ->
    forall nl',
    nl <= nl' ->
    labels_below l nl'.
Proof.
  unfold labels_below. intros.
  eapply Forall_impl; eauto. simpl; intros.
  destr; auto. lia.
Qed.

(* Si les labels sont au dessus de [nl] et que [nl <= nl'], alors les labels
sont au dessus de [nl']. *)
Lemma labels_above_slack:
  forall l nl,
    labels_above l nl ->
    forall nl',
    nl' <= nl ->
    labels_above l nl'.
Proof.
  unfold labels_above. intros.
  eapply Forall_impl; eauto. simpl; intros.
  destr; auto. lia.
Qed.

(* Le lemme suivant spécifie la sémantique des bornes de labels pour [compile_stmt].

Plus précisément, si on a [compile_stmt nl i = (nl', l)], alors :

- la nouvelle borne [nl'] est plus grande ou égale à la précédente
- tous les labels de [l] sont plus petits que la nouvelle borne [nl']
- tous les labels de [l] sont plus grands ou égaux à l'ancienne borne [nl].

 *)
Lemma compile_stmt_bound:
  forall i nl nl' l,
    compile_stmt nl i = (nl', l) ->
    nl <= nl' /\ labels_below l nl' /\ labels_above l nl.
Proof.
(* Décommenter la preuve suivante devrait suffire. *)
(*
  induction i; simpl; intros; eauto; repeat destr_in H; inv H; eauto; repeat split; eauto;
    try repeat (rewrite ? labels_below_app ||
                rewrite ? labels_below_cons ||
                apply labels_below_compile_expr ||
                apply labels_below_compile_cond ||
                rewrite ? labels_above_app ||
                rewrite ? labels_above_cons ||
                apply labels_above_compile_expr ||
                apply labels_above_compile_cond ||
                (apply IHi in Heqp) ||
                (apply IHi1 in Heqp0) ||
                (apply IHi2 in Heqp) ||
                (apply IHi1 in Heqp) ||
                (apply IHi2 in Heqp0) ||
                intuition lia ||
                constructor ||
                (eapply labels_below_slack; eauto; lia) ||
                (eapply labels_above_slack; eauto; lia) ||
                idtac).
*)
 Admitted.

(* Le lemme suivant correspond au cas [If c s1 s2] de la preuve du lemme
   compile_stmt_correct, ci-dessous, plus précisément au cas où la condition [c]
   est vraie.
 *)
Lemma compile_if_true_correct:
  forall c s1 s2 st st' t
         (EC: eval_cond st c = true)
         (BS: bigstep st s1 st' t)
         (IH:
            forall stk tr nl nl' cs
                   (COMPILE: compile_stmt nl s1 = (nl', cs))
                   a b
                   (BOUND: labels_below a nl),
              eval_sprog (MState a (cs ++ b) st stk tr)
                         (MState (a ++ cs) b st' stk (tr ++ t))
         )
         stk tr nl nl' cs
         (COMPILE: compile_stmt nl (If c s1 s2) = (nl', cs))
         a b
         (BOUND: labels_below a nl),
      eval_sprog (MState a (cs ++ b) st stk tr)
                 (MState (a ++ cs) b st' stk (tr ++ t)).
Proof.
  intros.
  simpl in *.
  (* On décompose l'hypothèse COMPILE en différentes parties, puis on remplace
  [nl'] et [cs] par leurs valeurs, calculées par la fonction [compile_stmt]. *)
  repeat destr_in COMPILE; inv COMPILE.

  (* On se retrouve avec les hypothèses suivantes :
     - Heqp : compile_stmt (nl + 2) s2 = (n, l)
     - Heqp0 : compile_stmt n s1 = (nl', l0)
   *)

  (* On veut se trouver dans une situation où le deuxième paramètre de MState
  (le programme qui reste à être évalué) soit de la forme [(x ++ y)]. Ici ce
  n'est pas immédiatement le cas : on a plutôt [((x ++ y) ++ z)]. Le lemme
  [app_assoc] :

  [app_assoc : forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n]

  permet de réécrire notre but pour qu'il soit de la bonne forme. On réécrit en
  arrière [<-], et autant de fois que possible [!].
   *)
  rewrite <- ! app_assoc.

  (* On fait une première série de pas qui correspond à l'évaluation de la condition.
   *)
  eapply eval_trans. apply compile_cond_correct.

  (* La prochaine instruction est [SJmp nl], on l'évalue : *)
  eapply eval_plus. simpl.

  (* On sait que [eval_cond st c = true], et on réécrit [(bool_of_Z (Z_of_bool x))] en [x] *)
  rewrite EC, bool_of_Z_of_bool.

  (* On va chercher le label [nl] dans le programme. On commence par reformater
  la liste des instructions avec notre lemme [app_assoc]. *)
  rewrite <- ! app_assoc.

  (* On sait que le label [nl] ne figure pas dans [a], d'après l'hypothèse [BOUND]. *)
  rewrite find_label_below with (n := nl); auto.
  (* On sait que le label [nl] ne figure pas dans [compile_cond c], d'après le
  lemme [labels_below_compile_bound].

   Remarque : on utilise la notation [2: apply ...] qui permet d'appliquer une
   tactique au sous-but numéro 2. Cela permet de résoudre des buts auxiliaires,
   sans avoir à y revenir plus tard. (Lorsqu'on ne saura plus où on en était
   dans la preuve...)
   *)
  rewrite find_label_below with (n := nl); auto. 2: apply labels_below_compile_cond.

  simpl.

  (* On sait que le label [nl] ne figure pas dans [l], d'après le lemme
  [compile_stmt_bound], qui dit, entre autres, que [l] ne contient que des
  labels supérieurs ou égaux à [nl + 2]. *)
  erewrite find_label_above with (n := nl + 2). 2: lia.
  simpl.

  (* On trouve un [match Nat.eq_dec nl nl with ...]. On applique [destruct
  (Nat.eq_dec nl nl)], puis on se débarasse du cas [nl <> nl] avec la tactique
  congruence. *)
  destruct (Nat.eq_dec nl nl); try congruence.

  (* Notre but est [Some x = Some ?...] : [eauto] résoud ce but ! *)
  eauto.

  (* On doit prouver [labels_above l (nl + 2)]. Il s'agit (d'une partie) des
  conclusions du lemme [compile_stmt_bound]. Coq est suffisamment gentil pour
  accepter que l'on applique directement ce lemme : *)
  eapply compile_stmt_bound; eauto.

  (* On s'apprête à "évaluer" [SLabel nl]. Allons-y. *)
  eapply eval_plus. simpl; eauto.
  (* On reformate le programme à exécuter. *)
  rewrite <- ! app_assoc.

  (* On s'apprête à évaluer [l0], i.e. le résultat de la compilation de
  l'instruction [s1]. L'hypothèse [IH] nous dit des choses sur l'évaluation de
  [l0] ! *)
  eapply eval_trans. eapply IH. eauto.

  (* On doit prouver que tous les labels de ce sous-programme sont plus petits
     que [n]. Pour automatiser la preuve, on réécrit, autant de fois que
     possible, les lemmes [labels_below_app] et [labels_below_cons]. *)
  repeat (rewrite ? labels_below_app, ? labels_below_cons).
  (* On applique le lemme [compile_stmt_bound] à nos deux hypothèses qui
  contiennent un [compile_stmt]. *)
  eapply compile_stmt_bound in Heqp; eauto.
  eapply compile_stmt_bound in Heqp0; eauto.
  (* On se retrouve avec une conjonction dans notre but, et des conjonctions
  dans les hypothèses. La tactique [intuition try lia] décompose toutes ces
  conjonctions (\mcoq{destruct} dans les hypothèses, \mcoq{split} dans le but).
  Sur chacun des sous-buts générés, on essaie la tactique [lia]. *)
  intuition try lia.

  (* On veut prouver [labels_below a n], sachant [labels_below a nl] et [nl + 2
  <= n]. On applique le lemme [label_below_slack]. *)
  eapply labels_below_slack. eauto. lia.

  (* Les conditions ne comportent pas de label. *)
  apply labels_below_compile_cond.

  (* Liste vide : [constructor] résoud celà. *)
  constructor.
  constructor.

  (* Plus qu'une instruction [SLabel (nl + 1)] à évaluer : *)
  eapply eval_one. simpl.

  (* Les programmes sont égaux, modulo associativité de la concaténation : *)
  repeat (rewrite <- ! app_assoc; simpl); auto.
Qed.

(* Voici maintenant le lemme principal sur lequel vous allez travailler. *)
Lemma compile_stmt_correct:
  forall i st st' t
         (BS: bigstep st i st' t)
         stk tr nl nl' cs
         (COMPILE: compile_stmt nl i = (nl', cs))
         a b
         (BOUND: labels_below a nl),
      eval_sprog (MState a (cs ++ b) st stk tr)
                 (MState (a ++ cs) b st' stk (tr ++ t)).
Proof.
  induction 1; simpl; intros; eauto.

  - inv COMPILE. simpl. rewrite ! app_nil_r. apply eval_zero.

  - inv COMPILE.
    rewrite <- ! app_assoc.
    eapply eval_trans. apply compile_expr_correct.
    eapply eval_one. simpl. rewrite app_nil_r; auto.
    rewrite <- ! app_assoc. auto.

   Admitted.


Definition compile_prog i :=
  let (_, cs) := compile_stmt O i in
  cs ++ [SHalt].

(* Un joli lemme final ! *)
Lemma compile_prog_correct:
  forall i st st' t,
    bigstep st i st' t ->
    forall stk tr,
      eval_sprog (MState [] (compile_prog i) st stk tr)
                 (Finished st' (tr ++ t)).
Proof.
   Admitted.

