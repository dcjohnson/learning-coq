Module Nat.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End Nat.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

Fixpoint sub (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | _, O => n
  | S n', S m' => sub n' m'
  end.

Fixpoint mul (n m : nat) : nat :=
  match m with
  | O => O
  | S m' => add n (mul n m')
  end.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mul n (fact n')
  end.

Inductive bool : Type :=
| true : bool
| false : bool.

Fixpoint eq_nat (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => eq_nat n' m'
  end.

Notation "x + y" := (add x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (sub x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mul x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check (S (S (S (S O)))).
Check 4.
Compute (minustwo (S (S (S (S O))))).
Compute (minustwo 4).
Compute (add 1 1).
Compute (sub 4 3).
Compute (sub 3 4).
Compute (add 3 (sub 5 2)).
Compute (mul 50 7).
Compute (add 3 1).
Compute (fact 3).
Compute (fact 7).
Compute (eq_nat 3 4).
Compute (eq_nat 6 (fact 3)).
Compute (S 3).
Compute (add 0 3).

Theorem plus_id_example : forall n m : nat,
  n = m -> (add n n) = (add m m).
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_one : forall n : nat,
  S n = 1 + n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_s_1 : forall n m : nat,
    S n = m -> mul m (1 + n) = mul m m.
Proof.
  intros n m H.
  rewrite <- plus_one.
  rewrite -> H.
  reflexivity.
Qed.
