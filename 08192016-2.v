Module play2.
  Inductive bool : Type :=
| true : bool
| false : bool.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition andb (a b: bool) : bool :=
    match a with
      | false => false
      | true => b
    end.
  Definition orb (a b : bool) : bool :=
    match a with
      | true => true
      | false => b
    end.

  Theorem andb_eq_orb :
    forall (b c : bool),
      (andb b c = orb b c) ->
      b = c.
  Proof.
    intros b.
    destruct b.
    intros c.
    simpl.
    intros H1.
    rewrite -> H1.
    reflexivity.
    intros c.
    simpl.
    intros H2.
    rewrite -> H2.
    reflexivity.
  Qed.

  Inductive bin : Type :=
  | zero : bin
  | double : bin -> bin
  | onemore : bin -> bin.

  Definition incr (a : bin) : bin :=
    onemore a.

  Fixpoint plus (a b : nat) :=
    match a, b with
      | O, n => n
      | (S m) , n => plus  m  (S n)
    end.

  
  Fixpoint bin_to_nat (a : bin) : nat :=
    match a with
      | zero => O
      | double x => plus (bin_to_nat x) (bin_to_nat x)
      | onemore x => S (bin_to_nat x)
    end.
  Theorem bin_incr1:
    forall (x: bin),
      bin_to_nat (incr x) = S (bin_to_nat x).
  Proof.
    destruct x.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.