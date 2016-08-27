Require Export "Prop".

Inductive ex (X:Type) (P :X->Prop) : Prop :=
  ex_intro : forall (witness : X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
                               (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex X (fun (x:X) => p))
                                   (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 :
  (ex _ (fun n => n + (n * n) = 6)).
Abort.

Theorem exists_example_2 :
  forall n,
    (exists m, n = 4 + m) ->
    (exists o, n = 2 + o).
  intros n.
  intros h.
  inversion h.
  rewrite -> H.
  apply (ex_intro _ (fun o => 4 + witness = 2 + o) (2 + witness)).
  reflexivity.
Qed.

Inductive sumbool (A B : Prop) : Set :=
|left : A -> sumbool A B
|right : B -> sumbool A B.

Notation "{ A } + { B }":= (sumbool A B) : type_scope.

Theorem eq_nat_dec:
  forall (n m : nat),
    { n = m } + { n <> m }.
  induction n.
  intros m.
  destruct m.
  left.
  reflexivity.
  right.
  unfold not.
  intros h.
  inversion h.
  intros m.
  destruct m eqn:h2.
  right.
  unfold not.
  intros h.
  inversion h.
  assert ( { n = n0} + {n <> n0}).
  apply IHn.
  inversion H.
  left.
  rewrite ->H0.
  reflexivity.
  unfold not in H0.
  right.
  intros h1.
  apply H0.
  inversion h1.
  reflexivity.

Defined.

Inductive elem (X:Type) : X -> list X -> Prop :=
| elem0 : forall (x : X), elem X x [x]
| elem1 : forall (x : X) (y z org : list X) , elem X x org -> elem X x (y ++ org ++ z).

Inductive all (X: Type): (X -> Prop) -> list X -> Prop :=
| all0 : forall (P' : X -> Prop), all X P' []
| all1 : forall (P' : X -> Prop) (x : X) (l : list X), all X P' l -> P' x -> all X P' (x::l).

Definition forallb {X : Type} (test : X -> Prop) (l : list X) : Prop :=
  all X test l.
Theorem spec_exclude_middle :
  forall (X : Type) (x y : X),
    (x = y) \/ (x <> y).
  intros X x y.
Abort.