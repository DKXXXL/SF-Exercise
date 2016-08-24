Require Export Logic.

Definition even (n : nat) : Prop :=
  evenb n = true.

Inductive ev  : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n, ev n -> ev (S (S n)).

Theorem double_even:
  forall n,
    ev(double n).
  intros n.
  induction n.
  simpl.
  apply ev_0.
  simpl.
  apply ev_SS in IHn.
  apply IHn.
Qed.

Inductive beautiful: nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n + m).

Theorem beautiful_8 :
  beautiful 8.
  assert (beautiful 3) as H.
  apply b_3.
  apply (b_sum 3 5 b_3 b_5).
Qed.


Theorem b_times2 :
  forall n,
    beautiful n -> beautiful (2 * n).
  intros n.
  induction n.
  intros h.
  simpl.
  apply h.
  intros h.
  assert (forall a, 2*a = a+a).
  unfold mult.
  intros a.
  assert (a+0 = a).
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> H.
  reflexivity.
  rewrite -> H.
  apply (b_sum (S n) (S n) h h).
Qed.

Theorem b_timesm:
  forall n m,
    beautiful n -> beautiful (m*n).
  induction n.
  intros m.
  assert (m * 0 = 0).
  induction m.
  reflexivity.
  simpl.
  apply IHm.
  rewrite -> H.
  intros h.
  apply h.
  induction m.
  simpl.
  intros h.
  apply b_0.
  intros h.
  assert (beautiful (S n)).
  apply h.
  apply IHm in h.
  simpl.
  assert (S (n + m * S n) = S n + m * S n).
  reflexivity.
  rewrite -> H0.
  apply (b_sum (S n) (m * S n) H h).
Qed.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3 + n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5 + n).

Theorem gorgeous_beautiful :
  forall n,
    gorgeous n -> beautiful n.
  intros n.
  intros h.
  induction h.
  apply b_0.
  apply (b_sum 3 n b_3 IHh).
  apply (b_sum 5 n b_5 IHh).
Qed.

Lemma helper_g_times2 :
  forall x y z,
    x + (z + y) = z + x + y.
  intros x y z.
  rewrite -> plus_assoc.
  assert (x + z = z + x).
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem g_times2:
  forall n,
    gorgeous n -> gorgeous (2 * n).
  intros n.
  intros h.
  induction h.
  simpl.
  apply g_0.
  unfold mult.
  unfold mult in IHh.
  rewrite -> helper_g_times2 in IHh.
  rewrite -> plus_assoc.
  rewrite -> helper_g_times2.
  rewrite -> plus_assoc.
  assert (3 + (3 + n + n + 0) = 3 + 3 + n + n + 0).
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  rewrite ->plus_assoc.
  reflexivity.
  rewrite <- H.
  apply g_plus3.
  assert (3 + (n + n+0) = 3 + n + n + 0).
  rewrite ->plus_assoc.
  rewrite -> plus_assoc.
  reflexivity.
  rewrite <- H0.
  apply g_plus3.
  apply IHh.
  unfold mult.
  rewrite <- plus_assoc.
  apply g_plus5.
  rewrite -> plus_assoc.
  assert (5 + n + n + 0 = n + (5 + n) + 0).
  rewrite -> helper_g_times2.
  reflexivity.
  rewrite <- H.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  apply g_plus5.
  simpl in IHh.
  apply IHh.
Qed.

Theorem ev_ev__ev:
  forall n m,
    ev (n + m) -> ev n -> ev m.
  intros n m h1 h2.
  induction h2.
  simpl in h1.
  apply h1.
  simpl in h1.
  inversion h1.
  apply IHh2 in H0.
  apply H0.
Qed.

Theorem even5:
  even 5 -> 2 + 2 = 9.
  intros h.
  inversion h.
Qed.


  Fixpoint rev' {X : Type} (x : list X) :=
    match x with
      | nil => nil
      | h :: t' =>(rev' t') ++ [h]
    end.
  Theorem rev'_app:
    forall (X: Type) (l l' : list X),
      rev' (l ++ l') = (rev' l') ++ (rev' l).
    intros X.
    induction l.
    simpl.
    assert (forall (x : Type) (l : list X), l++[] = l).
    induction l.
    reflexivity.
    simpl.
    rewrite -> IHl.
    reflexivity.
    intros l'.
    rewrite -> H.
    reflexivity.
    apply X.
    simpl.
    intros l'.
    rewrite -> IHl.
    assert (forall (X: Type) (a b c:list X), (a ++ b) ++ c = a ++ b ++ c).
    induction a.
    reflexivity.
    simpl.
    intros b c.
    rewrite -> IHa.
    reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

  Theorem app_assoc:
    forall (X: Type) (a b c:list X), (a ++ b) ++ c = a ++ b ++ c.
    intros X.
    induction a.
    reflexivity.
    simpl.
    intros b c.
    rewrite -> IHa.
    reflexivity.
Qed.
  Inductive pal {X : Type} : list X -> Prop :=
| palO : pal nil
| palx : forall (x : X), pal [x]
| palS : forall (s org: list X) ,pal org -> pal (s ++ org ++ (rev' s)).

Theorem pal_rev:
  forall (X : Type) (l : list X),
    pal l -> l = rev' l.
  intros X.
  intros l h.
  induction h.
  reflexivity.
  reflexivity.
  rewrite -> rev'_app.
  rewrite -> rev'_app.
  rewrite -> app_assoc.
  assert (rev' (rev' s) = s).
  induction s.
  reflexivity.
  simpl.
  rewrite -> rev'_app.
  simpl.
  rewrite -> IHs.
  reflexivity.
  rewrite -> H.
  rewrite <- IHh.
  reflexivity.

Qed.
(*I need rev l ++ rev l' = rev (l ' ++ l), 
which is totally easy proven in my definition,
while too hard to prove in THIS definition
why the hell to introduce 'snoc'? *)  
  Theorem pal_app_rev:
  forall (X : Type) (l : list X),
    pal (l ++ rev' l).
    intros X.
    induction l.
    simpl.
    apply palO.
    simpl.
    assert (x :: l ++ rev' l ++ [x] = [x] ++ (l ++ rev' l) ++ [x]).
    simpl.
    rewrite -> app_assoc.
    reflexivity.
    rewrite -> H.
    apply (palS [x] (l ++ rev' l) IHl).
Qed.
(*assert (x0 :: l ++ (rev x0 :: l) = [x0] ++ (l ++ rev l) ++ [x0])
  *)


  Inductive pal' {X : Type} : list X -> Prop :=
| pal'O :  pal' nil
| pal'x : forall (x : X), pal' [x]
| pal'S : forall (s: list X) (x : X) ,pal' [x] -> pal' (s ++ (x :: (rev' s)))
| pal'o : forall s : list X, pal' (s ++ (rev' s)).
  
  Theorem palindrom_converse:
Abort.