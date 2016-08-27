Require Export SfLib.

Module AEXP.
  Inductive aexp: Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp.

  Fixpoint aeval (a : exp) : nat :=
    match a with
      | ANum n => n
      | APlus a1 a1 => (aeval a1) + (aeval a2)
      | AMinus a1 a2 => (aeval a1) - (aeval a2)
      | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Fixpoint beval (b : bexp) : bool :=
    match b with
      | BTrue => true
      | BFalse => false
      | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
      | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
      | BNot b1 => negb (beval b1)
      | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.
  
  