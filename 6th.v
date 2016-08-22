Require Export Poly.

Theorem silly1:
  forall (n m o p : nat),
    n = m ->
    [n; o] = [n;p] ->
    [n; o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 :
  forall (n m o p : nat),
    n = m ->
    (forall (q r : nat), q = r -> [q ; o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p.
  intros e1.
  intros h1.
  
  apply h1.
  apply e1.
Qed.

Theorem silly2a :
  forall (n m : nat),
    (n,n) = (m,m) ->
    (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m eq1 h1.
  apply h1.
  apply eq1.
Qed.

Theorem sill_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros h1.
  intros e1.
  apply h1.
  apply e1.
Qed.

Theorem silly3 :
  forall (n : nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n.
  intros H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

Theorem rev_exercise :
  forall (l l': list nat),
    l = rev l' ->
    l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Theorem eq_add_S :
  forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem aaa :
  forall {X : Type} (n m q : X),
    n = m -> m = q -> n = q.
Proof.
  intros X n m q.
  intros H1.
  intros H2.
  rewrite <- H2.
  apply H1.
Qed.

Theorem bbb :
  forall (a b c d e f: nat),
    [a;b] = [c;d] ->  [c;d] = [e;f] -> [a;b] = [e;f].
  intros a b c d e f.
  intros eq1 eq2.
  apply aaa with ([c;d]).
  apply eq1.
  apply eq2.
Qed.

Theorem silly7:
  forall (n m : nat),
    false = true ->
    [n] = [m].
  intros n m h1.
  inversion h1.
Qed.

Theorem f_equal :
  forall (X Y : Type) (f : X -> Y) (x y : X),
    x = y ->
    f x = f y.
  intros X Y f x y h.
  rewrite h.
  reflexivity.
Qed.

Theorem S_inj :
  forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b ->
    beq_nat n m = b.
  intros n m b h.
  simpl in h.
  apply h.
Qed.
Theorem silly3' :
  forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
  intros n h1 h2.
  simpl.
  apply h2.
Qed.
Theorem plus_n_ninjective :
  forall n m,
    n + n = m + m ->
    n = m.
  intros n.
  induction n as [| n'].
  simpl.
  induction m.
  reflexivity.
  intros h.
  inversion h.
  induction m.
  intros h.
  inversion h.
  intros h.
  simpl in h.
  inversion h.
  rewrite -> plus_comm in H0.
  symmetry in H0.
  rewrite -> plus_comm in H0.
  simpl in H0.
  inversion H0.
  symmetry in H1.
  apply IHn' in H1.
  rewrite -> H1.
  reflexivity.
Qed.

Theorem double_injective_1 :
  forall n m,
    double n = double m ->
    n = m.
  intros n.
  induction n.
  destruct m.
  reflexivity.
  simpl.
  intros h.
  inversion h.
  simpl.
  intros m.
  intros h.
  destruct m.
  simpl in h.
  inversion  h.
  assert (forall n m, n = m -> S n = S m) as H2.
  intros n0 m0 h0.
  rewrite -> h0.
  reflexivity.
  apply H2.
  apply IHn.
  simpl in h.
  inversion h.
  reflexivity.
Qed.

Theorem beq_nat_true:
  forall n m,
    beq_nat n m = true ->
    n = m.
  intros n.
  induction n.
  destruct m.
  reflexivity.
  simpl.
  intros h.
  inversion h.
  intros m.
  destruct m.
  simpl.
  intros h.
  inversion h.
  simpl.
  intros H.
  apply IHn in H.
  rewrite -> H.
  reflexivity.
Qed.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match n with
    | O => match l with
             | nil => None
             | h :: t => Some h
           end
    | S x => match l with
               | nil => None
               | h :: t => index x t
             end
  end.


Theorem index_after_last :
  forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    index n l = None.

Proof.
  intros n X l.
  generalize dependent n.
  induction l.
  simpl.
  intros n' h'.
  rewrite <- h'.
  reflexivity.
  simpl.
  intros n.
  intros h.
  destruct n.
  inversion h.
  inversion h.
  rewrite -> H0.
  simpl.
  apply IHl.
  apply H0.
Qed.

Theorem length_assoc :
  forall X (l t : list X),
    length (l ++ t) = (length l) + (length t).
  intros X.
  intros l.
  induction l.
  reflexivity.
  simpl.
  intros t.
  rewrite -> IHl.
  reflexivity.
Qed.
Theorem app_length_twice :
  forall (X : Type) (n : nat) (l : list X),
    length l = n ->
    length (l ++ l) = n + n.
  intros X n l.
  intros H.
  rewrite -> length_assoc.
  rewrite -> H.
  reflexivity.
Qed.

Theorem double_induction :
  forall (P : nat -> nat -> Prop),
    P 0 0 ->
    (forall m, P m 0 -> P (S m) 0) ->
    (forall n, P 0 n -> P 0 (S n)) ->
    (forall m n, P m n -> P (S m) (S n)) ->
    forall m n, P m n.
  intros P.
  intros h0.
  intros h1.
  intros h2.
  intros h3.
  induction m.
  induction n.
  apply h0.
  apply h2.
  apply IHn.
  destruct n.
  apply h1.
  apply IHm.
  apply h3.
  apply IHm.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false :
  forall (n : nat),
    sillyfun n = false.

  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  reflexivity.
  destruct (beq_nat n 5).
  reflexivity.
  reflexivity.
Qed.

Definition override { X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat) => if (beq_nat k' k) then x else f k'.

Theorem override_shadow :
  forall (X : Type) x1 x2 k1 k2 (f: nat -> X),
    (override (override f k1 x2) k1 x1) k2 =
    (override f k1 x1) k2.

  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k2 k1).
  reflexivity.
  reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X * list Y) :=
  match l with
    | (h1, h2) :: t => match split t with
                         | (t1,t2) => (h1 :: t1, h2 :: t2)
                       end
    | [] => ([],[])
  end.

Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 =l.
  intros X Y l l1 l2.
  intros h.
  generalize dependent l2.
  generalize dependent l.
  induction l1.
  intros l l2 h.
  destruct l.
  simpl in h.
  inversion h.
  reflexivity.
  simpl in h.
  destruct p.
  destruct (split l).
  inversion h.
  intros l l2 h.
  destruct l2.
  destruct l.
  simpl in h.
  inversion h.
  simpl in h.
  destruct p.
  destruct (split l).
  inversion h.
  simpl.
  destruct l.
  simpl in h.
  inversion h.
  assert (forall x (a b : x) (c d : list x),
            a = b -> c = d -> a :: c = b :: d) as H.
  intros x0 a b c d h1 h2.
  rewrite -> h1.
  rewrite -> h2.
  reflexivity.
  apply H.
  simpl in h.
  destruct p.
  destruct (split l).
  inversion h.
  reflexivity.
  apply IHl1.
  simpl in h.
  destruct p.
  destruct (split l).
  inversion h.
  reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd_FAILED :
  forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.

  intros n.
  unfold sillyfun1.
  destruct (beq_nat n 3) eqn: h.
Abort.

Theorem bool_fn_applied_thrice:
  forall (f: bool -> bool) (b : bool),
    f (f (f b)) = f b.

  intros f b.
  destruct b eqn:h1.
  destruct (f true) eqn : h2.
  rewrite -> h2.
  apply h2.
  destruct (f false) eqn: h3.
  apply h2.
  apply h3.
  destruct (f false) eqn:h3.
  destruct (f true) eqn: h2.
  apply h2.
  apply h3.
  rewrite -> h3.
  apply h3.
Qed.