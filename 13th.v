Require Export SfLib.

Definition relation (X:Type) := X -> X -> Prop.

Definition partial_function {X : Type} (R : relation X) :=
  forall (x y1 y2 : X),
    R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.
  unfold partial_function.
  intros x y1 y2.
  intros h1 h2.
  inversion h1.
  inversion h2.
  reflexivity.
Qed.

Theorem le_nat_a_partial_function :
  ~(partial_function le).
  unfold not.
  intros h.
  unfold partial_function in h.
  assert (0 = 1).
  apply h with (x:= 0).
  apply le_n.
  apply le_S.
  apply le_n.
  inversion H.
Qed.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, R a b -> R b c -> R a c.

Theorem lt_trans' :
  transitive lt.
  unfold transitive.
  intros a b c h1 h2.
  unfold lt in h1.
  unfold lt in h2.
  unfold lt.
  induction h2.
  apply le_S.
  apply h1.
  apply le_S.
  apply IHh2.
Qed.

Theorem le_S_n:
  forall n m ,
    S n <= S m ->
    n <= m.
  intros n m h.
  generalize dependent n.
  induction m.
  intros n h1.
  inversion h1.
  apply le_n.
  inversion H0.
  intros n h1.
  inversion h1.
  apply le_n.
  apply le_S.
  apply IHm.
  apply H0.
Qed.

Theorem le_Sn_n_inf:
  forall n, ~(S n <= n).
  induction n.
  intros h.
  inversion h.
  unfold not in IHn.
  intros h.
  apply le_S_n in h.
  apply IHn in h.
  apply h.
Qed.

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symm :
  ~(symmetric le).
  intros h.
  unfold symmetric in h.
  assert (0 <= 1).
  apply le_S.
  apply le_n.
  apply h in H.
  inversion H.
Qed.

Theorem le_Sn_m_n_m' :
  forall n m,
    S n <= m -> n <= m.
  intros n m h1.
  assert (n <= S n).
  apply le_S.
  apply le_n.
  Check le_trans.
  apply (le_trans n (S n) m H h1).
Qed.
  Theorem le_trans :
  transitive le.
  unfold transitive.
  intros a b c h1 h2.
  induction h2.
  apply h1.
  apply le_S.
  apply IHh2.
Qed.
Theorem le_Sn_Sm_n_m' :
  forall n m,
    S n <= S m -> n <= m.
  intros n m h1.
  inversion h1.
  apply le_n.
  apply le_Sn_m_n_m'.
  apply H0.
Qed.

Definition antisymmetric {X:Type} (R:relation X) :=
  forall a b: X,
    (R a b) -> (R b a) -> a = b.

Inductive refl_step_closure {X : Type} (R:relation X) : relation X :=
| rsc_refl : forall (x:X), refl_step_closure R x x
| rsc_step : forall (x y z : X),
               R x y -> refl_step_closure R y z -> refl_step_closure R x z.

Theorem rsc_R :
  forall (X:Type) (R:relation X) (x y : X),
    R x y -> refl_step_closure R x y.
  intros X R x y h.
  apply (rsc_step R x y y h (rsc_refl R y)).
Qed.

Theorem rsc_trans:
  forall (X:Type) (R:relation X) (x y z : X),
    refl_step_closure R x y ->
    refl_step_closure R y z ->
    refl_step_closure R x z.
  intros X R x y z.
  intros h1.
  generalize dependent z.
  induction h1.
  intros z h1.
  apply h1.
  intros z0 h2.
  apply IHh1 in h2.
  apply rsc_step with y.
  apply H.
  apply h2.
Qed.

Print rsc_trans.

Theorem bbbbbbbbcj:
  forall (X : Type) (x y : X)(a b : nat)(R: relation X),
    refl_step_closure R x y -> a + b = b + a.
  intros X x y a b R h.
  induction h.