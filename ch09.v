Require Import Arith.
Inductive even : nat -> Prop :=
  even0 : even 0
| evenS : forall x:nat, even x -> even (S (S x)).

Lemma even_mult : forall x, even x -> exists y, x = 2*y.
    intros x H.
    induction H.
    now exists 0.
    destruct IHeven.
    exists (x0 + 1).
    rewrite H0.
    ring.
    Qed.

Lemma not_even_1 : ~even 1.
Proof. intros H. inversion H. Qed.

Lemma even_inv : forall x, even (S (S x)) -> even x.
    Proof.
    intros x H.
    inversion H. exact H1.
    Qed.

    