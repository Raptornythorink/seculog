Require Import While String.
Require Import ZArith.
Open Scope Z_scope.

Definition fac :=
  Seq
    (Assign "res" (Const 1))
    (Seq
       (While (Lt (Const 0) (Var "n"))
              (Seq
                 (Assign "res" (Binop Bmul (Var "res") (Var "n")))
                 (Assign "n" (Binop Bsub (Var "n") (Const 1)))
              )
       )
       (Output (Var "res"))
    ).

