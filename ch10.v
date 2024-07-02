Require Import Arith.
Fixpoint sum_odd_n (n:nat) : nat :=
    match n with
    0 => 0
    | S p => 1 + 2 * p + sum_odd_n p
    end.

Theorem sum_odd_equality: forall n, sum_odd_n n = n * n.
Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. ring.
    Qed.