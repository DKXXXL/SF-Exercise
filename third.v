Require Export Basics.
Require String. Open Scope string_scope. Ltac move_to_top x := match reverse goal with | H : _ |- _ => try move x after H end.
Tactic Notation "assert_eq" ident(x) constr(v) := let H := fresh in assert (x = v) as H by reflexivity; clear H.
Tactic Notation "Case_aux" ident(x) constr(name) := first [ set (x := name); move_to_top x
| assert_eq x name; move_to_top x | fail 1 "because we are working on a different case" ].
Tactic Notation "Case" constr(name) := Case_aux Case name. Tactic Notation "SCase" constr(name) := Case_aux SCase name. Tactic Notation "SSCase" constr(name) := Case_aux SSCase name. Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name. Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name. Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name. Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elm1 :
  forall (b c :bool),
    andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
  reflexivity.
  Case "b = false".
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_0_r_firsttry :
  forall (n : nat),
   plus n 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
  reflexivity.
  Case "n = S n'".
  simpl. 
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem minus_diag :
  forall n,
    minus n n = 0.
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem mult_0_r :
  forall (n : nat),
    n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_SO_S :
  forall ( n: nat),
    S n = plus (S 0) n.
Proof.
  reflexivity.
Qed.

Theorem plus_cob :
  forall (n a b : nat),
    plus n (plus a b) = plus (plus n a) b.
Proof.
  intros n a b.
  induction n as [|n'].
  Case "0 + (a + b) = 0 + a + b".
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_S_n_m :
  forall (n m : nat),
    S (n + m) = (S n) + m.

Proof.
  intros n m.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_Sm_Sn_m:
  forall ( n m: nat),
    (S n) + m = n + (S m).
Proof.
  intros n m.
  induction n as [|n'].
  rewrite <- plus_SO_S.
  reflexivity.
  simpl.
  rewrite <- IHn'.
  simpl.
  reflexivity.
Qed.

Theorem plus_comm:
  forall ( n m : nat),
    n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  induction m as [| m'].
  reflexivity.
  simpl.
  rewrite <- IHm'.
  reflexivity.
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Theorem plus_assoc:
  forall ( n m p : nat),
    n + (m + p) = (n + m) + p.

Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  intros m p.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus :
  forall (n : nat),
    double n = n + n.

Proof.
  intros n.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite <- plus_n_Sm.
  rewrite <- IHn'.
  reflexivity.
Qed.

Theorem plus_swap:
  forall (n m p : nat),
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (n + m = m + n) as H.
  Case "n + m = m + n".
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_comm :
  forall (m n : nat),
    m * n = n * m.
Proof.
  induction m as [| m'].
  simpl.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite <- IHn'.
  reflexivity.
  simpl.
  intros n.
  simpl.
  rewrite -> IHm'.
  assert (n + n * m' = n * S m') as H.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> plus_swap.
  rewrite -> IHn'.
  reflexivity.
  rewrite <- H.
  reflexivity.
Qed.

Theorem evenb_n__oddb_Sn :
  forall (n : nat),
    evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [|n'].
  reflexivity.
  assert (evenb (S (S n')) = evenb n') as H.
  reflexivity.
  rewrite -> H.
  rewrite -> IHn'.
  assert (forall (a:bool), negb (negb a) = a) as H2.
  intros a.
  destruct a.
  reflexivity.
  reflexivity.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem ble_nat_refl :
  forall (n : nat),
    true = ble_nat n n.
Proof.
  intros n.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem zerp_nbeq_S:
  forall (n : nat),
    beq_nat 0 (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem andb_false_r :
  forall (b : bool),
    andb b false = false.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem plus_ble_compat_l :
  forall (n m p : nat),
    ble_nat n m = true ->
    ble_nat (p + n) (p + m) = true.

Proof.
  intros n m p.
  intros H.
  induction p as [| p'].
  simpl.
  rewrite -> H.
  reflexivity.
  simpl.
  rewrite -> IHp'.
  reflexivity.
Qed.

Theorem S_nbeq_0 :
  forall (n : nat),
    beq_nat (S n) 0 = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem all3_spec:
  forall (b c : bool),
    orb (andb b c)
        (orb (negb b)
             (negb c))
    = true.
Proof.
  intros b c.
  destruct b.
  destruct c.
  reflexivity.
  reflexivity.
  destruct c.
  reflexivity.
  reflexivity.
Qed.

Theorem mult_plus_distr_r:
  forall ( n m p : nat),
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros p.
  induction p as [|p'].
  reflexivity.
  simpl.
  intros m p.
  rewrite -> IHp'.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc:
  forall (n m p: nat),
    n * (m * p) = (n * m) * p.

Proof.
  induction n as [|n'].
  reflexivity.
  simpl.
  intros m p.
  rewrite -> mult_plus_distr_r.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem beq_nat_refl :
  forall n,
    true = beq_nat n n.
Proof.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite <- IHn'.
  reflexivity.

Qed.

Theorem plus_swap':
  forall ( n m p: nat),
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(*

Inductive bin' : Type :=
| null' : bin' (* This should not exist  *)
| one : bin'
| zero' : bin' -> bin'
| one' : bin' -> bin'.

Inductive bin : Type :=
| null : bin
| have : bin' -> bin.
(* It's a very interesting expression,
it makes a binary reversed, and because the highest bit must be one,so
the only is one.
so 1010110 -> reverse -> 0110101 -> zero'(one' (one' (zero ( .... 
The only problem is it cannot express 0, so i have to get null *)
(*
Fixpoint div2 (a : nat) : nat :=
  match a with
    | O => O
    | S O => O
    | S (S x) => S (div2 x)
  end.
*)
Fixpoint mo2(a : nat) : bool :=
  match a with
    | O => false
    | S O => true
    | S (S x) => mo2 x
  end.

Definition k(a : nat) : nat :=
  match a with
    | O => O
    | S x => x
  end.
Fixpoint m (a : nat) : nat :=
  match a with
    | O => O
    | S x => m (k (S x))
  end.



Fixpoint nat_to_bin' (a : nat) : bin' :=
  let div2 := (fix div2 (a : nat) : nat :=
                 match a with
                   | O => O
                   | S O => O
                   | S (S x) => S (div2 x)
                 end) 
  in match a with
       | O => null'
       | S O => one
       | S x => match mo2 x with
                      | true => zero' (nat_to_bin' (div2 (S x)))
                      | false => one' (nat_to_bin' (div2 (S x)))
                    end
     end.

Definition nat_to_bin (a : nat) : bin :=
  match a with
    | O => null
    | x => have (nat_to_bin' x)
  end.
