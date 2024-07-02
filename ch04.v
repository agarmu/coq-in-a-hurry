Require Import Arith.
Require Import NArithRing.
Open Scope nat_scope.
Fixpoint sum_n (n:nat) := match n with
    | 0 => 0
    | S p => p + (sum_n p)
end.

Lemma sum_nat : forall n, 2 * sum_n n + n = n * n.
    Proof.
        induction n.
        unfold sum_n.
        reflexivity.
        assert (SnSn : S n * S n = n * n + 2 * n + 1).
        ring.
        rewrite SnSn.
        rewrite <- IHn.
        simpl.
        ring.
    Qed.


Fixpoint even (n:nat) := match n with
    | 0 => True
    | S 0 => False
    | S (S n) => even n
    end.

Lemma evenb_p : forall n, even n -> exists x, n = 2 * x.
    Proof.
        assert (Main: forall n, (even n -> exists x, n = 2 * x) /\
                    (even (S n) -> exists x, S n = 2 * x)).
        induction n.
        split; intros.
        now exists 0. simpl in H; contradiction.
        split; destruct IHn.
        exact H0. intros.
        simpl in H1. specialize (H H1).
        destruct H.
        exists (x+1).
        rewrite H. simpl. ring.
        intros.
        specialize (Main n).
        destruct Main.
        specialize (H0 H). exact H0.
    Qed.

Fixpoint add n m := match n with 0 => m | S p => add p (S m) end.
Theorem add_n_S : forall n m, add n (S m) = S (add n m).
    Proof.
        induction n; intros m; simpl.
        reflexivity.
        rewrite IHn. reflexivity.
    Qed.
    
Theorem add_S_m : forall n m, add (S n) m = S (add n m).
    Proof.
        intros n m; simpl.
        rewrite add_n_S. reflexivity.
    Qed.

Theorem add_eq_plus : forall n m, add n m = n + m.
    Proof.
        induction n; intros m.
        reflexivity.
        specialize (IHn m).
        rewrite add_S_m.
        rewrite IHn.
        rewrite Nat.add_succ_l. reflexivity.
    Qed.
