Module play1.
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint evenb (a: nat) : bool :=
  match a with
    | O => true
    | S O => false
    | S (S n) => evenb n
  end.

Fixpoint plus (a b :nat) : nat :=
  match a, b with
    | O, n => n
    | (S m) , n => (plus m (S n)) 
  end.
Fixpoint muti (a b :nat) : nat :=
  match a, b with
    | O, _ => O
    | (S n) , m => (plus m (muti n m))
  end.
Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S x => muti (S x) (factorial x)
  end.

Example test_factorial1: (factorial (S (S (S O)))) = S (S (S (S (S (S O))))).
reflexivity. Qed.

Fixpoint add (n : nat) : nat :=
  (S n).

x