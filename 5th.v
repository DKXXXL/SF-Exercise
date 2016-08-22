Require Export Lists.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Module MUMBLEBAZ.
Inductive mumble : Type :=
| a : mumble
| b : mumble -> nat -> mumble
| c : mumble.

Inductive grumble (X : Type) : Type :=
| d : mumble -> grumble X
| e : X -> grumble X.

Check (d mumble (b a 5)).
Check (d bool (b a 5)).
Check (e bool true).
Check (e mumble (b c 0)).
Check c.

End MUMBLEBAZ.
Check (cons nat 2 (nil nat)).
Check cons.

Fixpoint app X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length t)
  end.

Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).
Fixpoint snoc {X : Type} (a : list X) (b : X) : list X :=
  match a with
    | nil => [b]
    | h :: t => h :: (snoc t b)
  end.

Theorem snoc_with_append :
  forall (X : Type) (l1 l2 : list X) (v : X),
    snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).

Proof.
  induction l1.
  reflexivity.
  simpl.
  intros l2 v.
  rewrite -> IHl1.
  reflexivity.
Qed.

Inductive prod (X Y :Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition prod_curry {X Y Z:Type}
           (f : (X * Y) -> Z) (x : X) (y : Y) : Z :=
  f (x,y).

Definition prod_uncurry {X Y Z :Type}
           (f : X -> Y -> Z) ( p : (X * Y)) : Z :=
  match p with
    | (x , y) => f x y
  end.

Theorem uncurry_curry :
  forall (X Y Z : Type),
  forall (f : X -> Y -> Z),
  forall (x : X) (y : Y),
    (prod_curry (prod_uncurry f)) x y = f x y. 
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry :
  forall (X Y Z : Type)
         (f : (X * Y) -> Z)
         (p : (X * Y)),
    (prod_uncurry (prod_curry f)) p = f p.
Proof.
  intros X Y Z f p.
  destruct p as [x y].
  reflexivity.
Qed.

Definition doit3times {X:Type} (f : X -> X) (x : X) : X :=
  f (f (f x)).

Check (doit3times (fun n => match n with
                              | O => O
                              | S x => x
                            end) 10).

Definition override {Y : Type} (f : nat -> Y) (x : nat) (y : Y) :(nat -> Y):=
  fun (x' : nat) => if (beq_nat x' x)
                    then y
                    else f x'.
Definition plus3 :=
  plus 3.

Theorem unfold_example :
  forall n m,
    3 + n = m ->
    plus3 n + 1 = m + 1.

Proof.
  intros n m H.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

Theorem override_eq :
  forall (X :  Type)
         x k (f : nat -> X),
    (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  replace (beq_nat k k) with true.
  reflexivity.
  induction k.
  reflexivity.
  simpl.
  rewrite -> IHk.
  reflexivity.
Qed.

Module CHURCH.
  Definition nat := forall (X : Type),
                      (X -> X) -> X -> X.
  Definition zero : nat :=
    fun (X : Type) (f : X -> X) (x : X) => x.
  Definition succ (a : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f (a X f x).
  Definition one : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f x.

  
  Example succ_1 : succ zero = one. 
  Proof.
    reflexivity.
  Qed.
  Definition plus (a b : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) =>
      b X f (a X f x).
  Example plus_1 : plus zero one = one.
  Proof.
    reflexivity.
  Qed.
  