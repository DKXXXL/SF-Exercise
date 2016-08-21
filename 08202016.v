Inductive nat : Type :=
| O : nat
| S : nat -> nat .

Fixpoint plus (n m : nat) : nat :=
  match n, m with
    | O, m' => m'
    | (S n'), m' => S (plus n' m')
  end.

Theorem plus_S_exch :
  forall (n m : nat),
    (plus (S n) m) = (plus n (S m)).

Proof.
  intros n m.
  induction n as [| n'].
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn'.
  reflexivity.
Qed.

Theorem plus_S_up:
  forall (a b : nat),
    plus (S a) b = S (plus a b).

Proof.
  intros a b.
  reflexivity.
Qed.

Theorem plus_S_exch_2:
  forall (a b : nat),
    plus (S a) b = plus a (S b).
Proof.
  intros a b.
  induction a as [|a'].
  reflexivity.
  simpl.
  rewrite <- IHa'.
  reflexivity.
Qed.

Theorem plus_exch:
  forall (a b : nat),
    plus a b= plus b a.
Proof.
  intros a.
  induction a as [| a'].
  intros b.
  induction b as [| b'].
  reflexivity.
  rewrite <- plus_S_exch_2.
  simpl.
  rewrite <- IHb'.
  reflexivity.
  intros b.
  simpl.
  rewrite <- plus_S_exch_2.
  simpl.
  rewrite <- IHa'.
  reflexivity.
Qed.

Theorem plus_cob:
  forall (n a b : nat),
    plus (plus n a) b = plus n (plus a b).
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  intros a b.
  rewrite <- IHn'.
  reflexivity.
Qed.
