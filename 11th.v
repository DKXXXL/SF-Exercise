Require Export "ProofObjects".
Check nat_ind.
Check eq_ind.
Theorem mult_0_r' :
  forall (n : nat),
    n * 0 = 0.
  apply nat_ind.
  Check nat_ind.

Abort.
Inductive yesno : Type :=
| yes : yesno
| no : yesno.
Check yesno_ind.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.
Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.
Check natlist1_ind.

Lemma one_not_beautiful :
  ~ (beautiful 1).
  intros h.
  remember 1 as n eqn:E.

Abort.
Check eq_ind.
Print eq_ind.
Inductive eq' (X:Type): X -> X -> Prop :=
  refl_equal' :forall (x : X), eq' X x x.
Print eq'_ind.

Print False_ind.
Check ex_ind.
Print ex.

Inductive aaa: Type :=
  bbb : aaa.
Check aaa_ind.
