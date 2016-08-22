Require Export Induction.
Module NATLIST.
  Inductive natprod : Type :=
    pair : nat -> nat -> natprod.
  Definition fst (p : natprod) : nat :=
    match p with
      | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
      | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Definition fst' (p : natprod) : nat :=
    match p with
      | (x,y) => x
    end.
  Definition snd' (p : natprod) : nat :=
    match p with
      | (x,y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
      | (x , y) => (y , x)
    end.

  Theorem surjective_pairing' :
    forall ( n m: nat),
      (n , m) = (fst (n , m), snd (n , m)).
  Proof.
    intros n m.
    reflexivity.
  Qed.

  Theorem surjective_pairing_stuck :
    forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros p.
    destruct p.
    reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  (*Definition myist := cons 1 (cons 2 (cons 3 nil )).
  *)
  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[]" := nil.

  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
      | O => nil
      | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l : natlist) : nat :=
    match l with
      | nil => O
      | _ :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
      | nil => l2
      | h :: t => h :: (app t l2)
    end.

  Notation " x ++ y " := (app x y)
                           (right associativity, at level 60).

  Definition hd (def : nat) (l : natlist) : nat :=
    match l with
      | nil => def
      | h :: _ => h
    end.
  Definition tl (l : natlist) : natlist :=
    match l with
      | nil => nil
      | _ :: t => t
    end.

  Fixpoint nonzeros (l: natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => match h with
                    | O => nonzeros t
                    | S x => (S x) :: (nonzeros t)
                  end
    end.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
      | (a :: l1'), (b :: l2') => a :: b :: (alternate l1' l2')
      | [], l2' => l2'
      | l1, [] => l1
    end.

  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
      | nil => O
      | h :: t => match (beq_nat h v) with
                    | true => S (count v t)
                    | false => count v t
                  end
    end.

  Definition sum : bag -> bag -> bag :=
    app.

  Definition add (v : nat) (s : bag) : bag :=
    cons v s.

  Definition  membar (v:nat) (s : bag) : bool :=
    match count v s with
      | O => false
      | S x => true
    end.

  Theorem nil_app :
    forall (l : natlist),
      [] ++ l = l.

  Proof.    
    reflexivity.
  Qed.

  Theorem app_nil :
    forall (l : natlist),
      l ++ [] = l.

  Proof.
    intros l.
    induction l as [| h t].
    reflexivity.
    simpl.
    rewrite -> IHt.
    reflexivity.
  Qed.

  Theorem tl_length_pred :
    forall (l : natlist),
      pred (length l) = length (tl l).

  Proof.
    intros l.
    destruct l as [| h t].
    reflexivity.
    reflexivity.
  Qed.

  Theorem app_assoc :
    forall (l1 l2 l3 : natlist),
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1.
    induction l1 as [| h1 t1].
    reflexivity.
    intros l2 l3.
    simpl.
    rewrite -> IHt1.
    reflexivity.
  Qed.

  Theorem app_length :
    forall (l1 l2 :natlist),
      length (l1 ++ l2) = (length l1) + (length l2).

  Proof.
    induction l1 as [| h1 t1].
    reflexivity.
    simpl.
    intros l2.
    rewrite -> IHt1.
    reflexivity.
  Qed.

  Fixpoint snoc (l : natlist) (v : nat) : natlist :=
    match l with
      | nil => [v]
      | h :: t => h :: (snoc t v)
    end.
  Fixpoint rev (l : natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => snoc (rev t) h
    end.

  Fixpoint rev' (l : natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => (rev' t) ++ [h]
    end.

  Theorem length_snoc :
    forall (n : nat) (l : natlist),
      length (snoc l n) = S (length l).
  Proof.
    intros n l.
    induction l as [| h t].
    reflexivity.
    simpl.
    rewrite -> IHt.
    reflexivity.
  Qed.
  Theorem rev_length_fisrttry :
    forall (l : natlist),
      length (rev l) = length l.

  Proof.
    induction l as [| h t].
    reflexivity.
    simpl.
    rewrite -> length_snoc.
    rewrite -> IHt.
    reflexivity.
  Qed.

  Theorem length_rev' :
    forall (l : natlist),
      length (rev' l) = length l.
  Proof.
    induction l as [| h t].
    reflexivity.
    simpl.
    rewrite -> app_length.
    simpl.
    rewrite -> plus_comm.
    simpl.
    rewrite -> IHt.
    reflexivity.
  Qed.

  Theorem rev_involutive :
    forall (l : natlist),
      rev (rev l) = l.
  Proof.
    intros l.
    induction l as [| h t].
    reflexivity.
    simpl.
(*
    assert (forall (a : natlist) (b : nat),
              (snoc a b) = a ++ [b]) as H1.
    induction a as [| h1 t1].
    reflexivity.
    intros b.
    simpl.
    rewrite <- IHt1.
    reflexivity.
    rewrite -> H1.
    simpl.
 *)
    assert (forall (a:natlist)(b:nat),
              rev (snoc a b) = b :: (rev a)) as H1.
    induction a as [| h1 t1].
    reflexivity.
    simpl.
    intros b.
    rewrite -> IHt1.
    simpl.
    reflexivity.
    rewrite -> H1.
    rewrite -> IHt.
    reflexivity.
  Qed.

  Theorem rev'_intro :
    forall (a b : natlist),
      rev' (a ++ b) = (rev' b) ++ (rev' a).
  Proof.
    induction a as [| h1 t1].
    simpl.
    intros b.
    rewrite -> app_nil.
    reflexivity.
    simpl.
    intros b.
    rewrite -> IHt1.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

  Theorem rev'_involutive :
    forall (l : natlist),
      rev' (rev' l) = l.
  Proof.
    induction l as [| h t].
    reflexivity.
    simpl.
    rewrite -> rev'_intro.
    simpl.
    rewrite -> IHt.
    reflexivity.
  Qed.

  Theorem app_assoc4 :
    forall (l1 l2 l3 l4 :natlist),
      l1 ++ l2 ++ l3 ++ l4 =
      ((l1 ++ l2) ++ l3) ++ l4.

  Proof.
    intros l1 l2 l3 l4.
    rewrite ->app_assoc.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

  Theorem snoc_append :
    forall (n : nat) (l : natlist),
      snoc l n = l ++ [n].

  Proof.
    intros n.
    induction l as [| h t].
    reflexivity.
    simpl.
    rewrite -> IHt.
    reflexivity.
  Qed.

  Definition distr_rev :=
    rev'_intro.

  Check (nonzeros).

  Lemma nonzeros_app :
    forall (l1 l2 :natlist),
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).

  Proof.
    induction l1 as [| h1 t1].
    reflexivity.
    destruct h1.
    simpl.
    intros l2.
    rewrite -> IHt1.
    reflexivity.
    simpl.
    intros l2.
    rewrite -> IHt1.
    reflexivity.
  Qed.

  Fixpoint beq_natlist (l1 l2 :natlist) : bool :=
    match l1, l2 with
      | [], [] => true
      | h1 :: t1, h2 :: t2 => andb (beq_nat h1 h2) (beq_natlist t1 t2)
      | h1 :: t1, [] => false
      | [] , h2 :: t2 => false
    end.
  Theorem beq_natlist_refl:
    forall (l : natlist),
      true = beq_natlist l l.

  Proof.
    induction l as [| h t].
    reflexivity.
    simpl.
    rewrite <- IHt.
    replace (beq_nat h h) with true.
    reflexivity.
    induction h.
    reflexivity.
    simpl.
    rewrite <- IHh.
    reflexivity.
  Qed.

  
  
  Theorem count_member_nonzero :
    forall (s : bag),
      ble_nat 1 (count 1 (1 :: s)) = true.

  Proof.
    
    induction s as [| h t].
    reflexivity.
    reflexivity.
  Qed.

  Theorem ble_n_Sn :
    forall n,
      ble_nat n (S n) = true.

  Proof.
    induction n.
    reflexivity.
    simpl.
    rewrite -> IHn.
    reflexivity.
  Qed.
  Fixpoint remove_one (n : nat) (s : bag) : bag :=
    match s with
      | [] => []
      | h :: t => match (beq_nat h n) with
                    | true => t
                    | false => h :: (remove_one n t)
                  end
    end.
  
  Theorem remove_decreases_count:
    forall s,
      ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.

  Proof.
    induction s.
    reflexivity.
    destruct n.
    simpl.
    rewrite -> ble_n_Sn.
    reflexivity.
    simpl.rewrite -> IHs.
    reflexivity.
  Qed.

  Theorem rev_injective :
    forall (l1 l2 : natlist),
      rev l1 = rev l2 ->
      l1 = l2.
  Proof.
    assert (forall l1 l2, l1 = l2 -> rev l1 = rev l2) as H.
    intros l1 l2.
    intros h1.
    rewrite -> h1.
    reflexivity.
    intros l1 l2.
    intros H1.
    rewrite <- rev_involutive.
    replace l1 with (rev (rev l1)).
    rewrite -> H1.
    reflexivity.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Definition hd_opt (l : natlist) : natoption :=
    match l with
      | [] => None
      | h :: t => Some h
    end.
  
  Module DICTIONARY.

    Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

    Definition insert (key value : nat) (d : dictionary) : dictionary :=
      (record key value d).

    Fixpoint find (key : nat) (d : dictionary) : natoption :=
      match d with
        | empty => None
        | record k v d' => if (beq_nat key k)
                           then (Some v)
                           else (find key d')
      end.

    Theorem dictionary_invariant1' :
      forall (d : dictionary) (k v : nat),
        (find k (insert k v d)) = Some v.

    Proof.
      intros d k v.
      simpl.
      replace (beq_nat k k) with true.
      reflexivity.
      induction k.
      reflexivity.
      simpl.
      rewrite -> IHk.
      reflexivity.
    Qed.

    
  