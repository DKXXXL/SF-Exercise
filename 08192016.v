Module Play.

  Inductive nat : Type :=
| O : nat
| S : nat -> nat.

  Fixpoint plus (a b : nat) :=
    match a, b with
      | O, n => n
      | (S m) , n => plus m (S n)
    end.

  Theorem plus_O_n : forall n : nat, plus O n = n.
  Proof.
    intros n.
    reflexivity.
  Qed.
  Theorem plus_n_O : forall n : nat, plus n O = n.
  Proof.
    intros n.
    simpl.
  Abort.
  Theorem plus_1_l : forall n : nat, plus (S O) n = S n.
  Proof.
    intros n.
    simpl.
    reflexivity.
  Qed.
  Theorem plus_id_example : forall n m :nat,
                              n = m ->
                              plus n n = plus m m.
  Proof.
    intros m n.
    intros H.
    rewrite -> H.
    reflexivity.
  Qed.
  Theorem plus_id_exercise :
    forall n m o : nat,
      n = m -> m = o -> plus n m = plus m o.
  Proof.                               
    intros n m o.                                              
    intros H1.
    intros H2.
    rewrite -> H1.
    rewrite <- H2.
    reflexivity.
  Qed.

  Fixpoint mult (n m : nat) : nat :=
    match n, m with
      | O, _ => O
      | (S n'), m => plus m (mult n' m)
    end.
  Theorem mult_O_plus :
    forall n m : nat,
      (mult (plus O n) m) = mult n m.
  Proof.
    intros n m.
    rewrite <- plus_O_n.
    simpl.
    reflexivity.
  Qed.

  Theorem mult_S_1 :
    forall n m : nat,
      m = S n ->
      mult m (plus (S O) n) = mult m m.
  Proof.
    intros n m.
    intros H1.
    simpl.
    rewrite <- H1.
    reflexivity.
  Qed.

  Inductive bool : Type :=
  | true : bool
  | false : bool.

  Fixpoint beq_nat (a b : nat) : bool :=
    match a, b with
      | O, O => true
      | O, S n => false
      | S n , O => false
      | S n , S m => beq_nat n m
    end.

  Theorem plus_1_neq_0_firsttry :
    forall n : nat,
      beq_nat (plus n (S O)) O = false.
  Proof.
    intros n.
    destruct n as [| n' ].
    reflexivity.

    simpl.
    
  Abort.

  Theorem plus_exch:
    forall n m,
      plus n (S m) = plus (S n) m.

  Proof.
    intros n m.
    simpl.
    reflexivity.
  Qed.

  Theorem plus_1_neq_0_firsttry :
    forall n : nat,
      beq_nat (plus n (S O)) O = false.

  Proof.
    intros n.
    rewrite -> plus_exch.
    destruct n as [O | n'].
    reflexivity.
  Abort.

  Theorem identif_fn_applied_twice :
    forall (f : bool -> bool),
      (forall (x : bool), f x = x) ->
      forall (b : bool), f (f b) = b.
  Proof.
    intros f.
    intros x.
    intros b.
    rewrite -> x.
    rewrite -> x.
    reflexivity.
  Qed.

  Theorem pl0:
    forall (x : nat),
      plus (S O) x = S x.
  Proof.
    reflexivity.
  Qed.
 (*   Theorem pl00:
      forall (m n :nat),
       S m = S n -> m = n.
    Proof.
      intros m n.
      intros H.
      induction m as [| m'].
      reflexivity.*)
      Theorem pl1:
    forall (n: nat),
    forall (a b : nat),
      plus n (plus a b) = plus (plus n a) b.
    intros n.
    induction n as [| n'].
    reflexivity.
    simpl.
    rewrite <- IHn'.

    