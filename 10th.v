Require Export MoreLogic.

Print beautiful.
Check b_sum.

Print eight_is_beautiful.

Theorem eight_is_beautiful'' : beautiful 8.
  Show Proof.
  apply b_sum with (n:=3) (m:=5).
  Show Proof.
  apply b_3.
  Show Proof.
  apply b_5.
  Show Proof.
Qed.

Print eq_ind.
Print b_times2.
Print plus_n_O.

Theorem beautiful''' :
  forall n,
    beautiful (2*n) -> beautiful (n + n).
  intros.
  simpl in H.
  rewrite <- plus_n_O in H.
  apply H.
Qed.
Print beautiful'''.
Print eq_ind_r.
Print eq_ind.
Print eq_rect.
Print eq_refl.
Print b_times2.

Print and_example.
Check conj.

Definition conj_fact :
  forall P Q R,
    P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (a : P /\ Q) (b : Q /\ R) =>
    match a with
      | conj p _ => match b with
                      | conj _ r => conj _ _ p r
                    end
    end.

Definition some_nat_is_even : Prop :=
  ex _ ev.

Check plus_comm.

Definition add1 : nat -> nat.
  intro.
  apply (S H).
Defined.