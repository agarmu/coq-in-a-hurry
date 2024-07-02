 Require Import Arith.

Fixpoint count n l :=
  match l with
    nil => 0
  | cons x xs =>
    let r := count n xs in if Nat.eqb n x  then 1+r else r
  end.

Fixpoint insert n l :=
  match l with
    nil => cons n nil
  | cons a tl => if n <=? a then cons n l else cons a (insert n tl)
  end.

Fixpoint len (l: list nat) :=
    match l with
    | nil => 0
    | cons _ xs => S(len xs)
    end.

Theorem insertion_increase_len: forall n: nat, forall l: list nat, len (insert n l) = 1 + len l.
    Proof.
        intros.
        induction l.
        simpl; reflexivity.
        simpl.
        case (n <=? a).
        simpl; reflexivity.
        simpl. rewrite IHl. reflexivity.
    Qed.
    

Theorem insertion_increases_count: forall n : nat, forall l: list nat,
    count n (insert n l) = S(count n l).
Proof.
    induction l.
    simpl.
    rewrite Nat.eqb_refl. reflexivity.
    simpl insert.
    case (n<=?a); simpl count; try rewrite Nat.eqb_refl; try rewrite IHl; try reflexivity.
    case (n=?a); reflexivity.
    Qed.
