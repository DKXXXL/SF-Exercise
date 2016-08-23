Require Export MoreCoq.

Check (3=3).

Check (forall (n : nat), n = 2).

Theorem silly :
  0 * 3 = 0.
  reflexivity.
Qed.

Print silly.

Check eq_refl.

Check Prop.
Check silly.

Theorem silly_1 :
  forall (n:nat),
    n = n.
  reflexivity.
Qed.

Check silly_1.
Check (0*3 =0).
Check (0).
Check (forall (n m:nat),n = m).
Check (eq_refl).
Print silly.

Lemma silly_implication :
  (1+1)=2 -> 0*3 = 0.
  intros H.
  reflexivity.
Qed.

Print silly_implication.

Print silly_1.
Check mult.
Check (nat -> nat -> nat).
Check (forall p q, p -> q).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.
Check and.
Check (conj).
Check (forall (p : Prop), p -> p -> and p p).
Check (0 = 0).
Check (nat).

Theorem aaaaaa:
  Prop -> Prop -> Prop.
  apply and.
Qed.
Theorem and_example :
  (0 = 0) /\ (4 = mult 2 2).
  apply conj.
  reflexivity.
  reflexivity.
Qed.
Print and_example.

Print conj.
Print and.
Theorem proj1 :
  forall (P Q : Prop),
    P /\ Q -> P.
  intros P Q H.
  destruct H.
  apply H.
Qed.

Print proj1.

Check proj1.

Theorem and_commut :
  forall (P Q : Prop),
    P /\ Q -> Q /\ P.
  intros P Q.
  intros H.
  destruct H.
  apply conj.
  apply H0.
  apply H.
Qed.

Theorem and_assoc :
  forall (P Q R : Prop),
    P /\ ( Q /\ R ) -> (P /\ Q) /\ R.

  intros P Q R h.
  destruct h.
  destruct H0.
  apply conj.
  apply conj.
  apply H.
  apply H0.
  apply H1.
Qed.

Definition iff ( P Q :Prop) := (P -> Q) /\ (Q /\ P).
Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity)
                      : type_scope.
Theorem iff_implies :
  forall (P Q :Prop),
    (P <-> Q) -> P -> Q.
  intros P Q.
  intros H.
  intros H1.
  destruct H.
  apply H in H1.
  apply H1.
Qed.

Theorem iff_sym :
  forall (P Q : Prop),
    (P <-> Q) -> (Q <-> P).
  intros P Q h.
  destruct h.
  destruct H0.
  apply conj.
  intros q.
  apply H1.
  apply conj.
  apply H1.
  apply H0.
Qed.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check (or_introl).

Theorem or_commut :
  forall (P Q : Prop),
    P \/ Q -> Q \/ P.
  intros P Q h.
  destruct h.
  apply or_intror.
  apply H.
  apply or_introl.
  apply H.
Qed.

Theorem or_distributes_over_and_1 :
  forall (P Q R : Prop),
    P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
  intros P Q R h.
  apply conj.
  destruct h.
  left.
  apply H.
  destruct H.
  right.
  apply H.
  destruct h.
  left.
  apply H.
  destruct H.
  right.
  apply H0.
Qed.

Theorem andb_prop :
  forall (b c : bool),
    andb b c = true ->
    b = true /\ c = true.
  intros b c h.
  unfold andb in h.
  destruct b.
  rewrite -> h.
  apply conj.
  reflexivity.
  reflexivity.
  apply conj.
  apply h.
  inversion h.
Qed.

Check true.
Check and.

Inductive False : Prop :=.

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
  intros  h.
  inversion h.
Qed.

Theorem False_iiiiiiiiiii :
  False -> 1 + 1 = 3.
  intros h.

  destruct h.
Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
  intros h.
  inversion h.
Qed.

Inductive Truth : Prop :=
| fact : Truth.

Definition not (P : Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.

Check not.

Theorem contradiction_implies_anything :
  forall (P Q :Prop),
    (P /\ (~P)) -> Q.
  intros P Q.
  intros H.
  unfold not in H.
  destruct H.
  apply H0 in H.
  inversion H.
Qed.

Theorem double_neg :
  forall (P : Prop),
    P -> ~~P.
  intros P p.
  unfold not.
  unfold not.
  intros h.
  apply h in p.
  inversion p.
Qed.

Definition peirce :=
  forall (P Q : Prop),
    ((P -> Q) -> P) -> P.

Definition classic :=
  forall (P : Prop),
    ~~P -> P.

Theorem O :
  peirce <-> classic.
  apply conj.
  intro h.
  unfold peirce in h.
  unfold classic.
  unfold not.
  intro P.
  intro h1.
Abort.

Theorem contrapositive:
  forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).
  intros P Q.
  intros h.
  unfold not.
  intros h1.
  intros p.
  apply h in p.
  apply h1 in p.
  destruct p.
Qed.

Theorem not_False:
  False -> False.
  intros h.
  inversion h.
Qed.

Print not_False.
Theorem excluded_middle_irrefutable:
  forall (P : Prop),
   ~~(P \/ (~P)).
  intros p.
  unfold not.
  intros h.
  apply h.
  right.
  intros p1.
  apply h.
  left.
  apply p1.
Qed.

Print excluded_middle_irrefutable.



Theorem peirce_classic :
  peirce -> classic.
  unfold peirce.
  unfold classic.
  intros h.
  unfold not.
  intros P.
  assert (((P -> False) -> P) -> P) as H.
  apply h.
  intros h1.
  apply H.
  intro h2.
  apply h1 in h2.
  inversion h2.
Qed.

Definition excluded_middle :=
  forall (P : Prop),
    P \/ ~P.

Theorem classic_excluded_middle :
  classic -> excluded_middle.
  unfold classic.
  unfold excluded_middle.
  intros H.
  intros P.
  assert (~~(P\/~P)) as h.
  apply excluded_middle_irrefutable.
  apply H in h.
  apply h.
Qed.

Definition de_morgan_not_and_not :=
  forall (P Q :Prop),
    ~(~P /\ ~Q) -> P\/Q.
(*
Theorem excluded_middle_de_morgan_not_and_not :
  classic -> de_morgan_not_and_not.
  unfold de_morgan_not_and_not.
  unfold classic.
  unfold not.
  intros h.
  intros p q.
  intros h1.
  apply h.
  intros h2.
  apply h1.
  apply conj.
  intros p1.
  apply h2.
  left.
  apply p1.
  intros q1.
  apply h2.
  right.
  apply q1.
Qed.
*)
Theorem excluded_middle_classic :
  excluded_middle -> classic.
  unfold excluded_middle.
  unfold classic.
  unfold not.
  intros h1.
  intros p.
  intros h.
  assert (p \/ (p -> False)) as H.
  apply h1.
  destruct H.
  apply H.
  apply h in H.
  inversion H.
Qed.

Theorem excluded_middle_de_morgan_not_and_not :
  excluded_middle -> de_morgan_not_and_not.
  unfold excluded_middle.
  unfold de_morgan_not_and_not.
  unfold not.
  intros h.
  intros p q.
  intro h1.
  assert (p \/ ( p -> False)) as H.
  apply h.
  destruct H.
  left.
  apply H.
  assert (q \/ (q -> False)) as H2.
  apply h.
  destruct H2.
  right.
  apply H0.
  assert ((p -> False) /\ (q -> False)) as H3.
  apply conj.
  apply H.
  apply H0.
  apply h1 in H3.
  inversion H3.
Qed.

Definition implies_to_or :=
  forall p q:Prop,
    (p -> q) -> (~p\/q).

Theorem de_morgan_not_and_not_implies_to_or:
  de_morgan_not_and_not -> implies_to_or.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  unfold not.
  intros H.
  intros p q.
  intros h1.
  apply H.
  intros h2.
  destruct h2.
  apply H0.
  intros p'.
  apply H1.
  apply h1.
  apply p'.
Qed.

Theorem implies_to_or_peirce :
  implies_to_or -> peirce.
  unfold implies_to_or.
  unfold peirce.
  unfold not.
  intros H.
  intros p q.
  intros h.
  assert ((p -> p) -> (p -> False) \/ p) as h1.
  apply H.
  assert ( p->p) as h2.
  intros p'.
  apply p'.
  apply h1 in h2.
  destruct h2.
  apply h.
  intros p'.
  apply H0 in p'.
  inversion p'.
  apply H0.
Qed.

(* Please all use excluded_middle *)


Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true :
  forall (b : bool),
    b <> false -> b = true.

  intros b.
  intros h.
  destruct b.
  reflexivity.
  unfold not in h.
  assert (false = false) as h'.
  reflexivity.
  apply h in h'.
  inversion h'.
Qed.
