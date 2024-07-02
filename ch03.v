(* commutative and *)
Require Import Coq.Arith.PeanoNat.
Open Scope nat_scope.
Lemma and_commutative: forall a b: Prop, a /\ b -> b /\ a.
Proof.
    intros a b H.
    split; destruct H as [H1 H2].
    exact H2. exact H1.
Qed.
    
(* commutative or *)
Lemma or_commutative: forall a b: Prop, a \/ b -> b \/ a.
Proof.
    intros a b H.
    destruct H as [H1 | H1].
    right. exact H1.
    left. exact H1.
    Qed.

Definition xor a b := (a /\ not b) \/ (b /\ not a).

Lemma xor_commutative: forall a b: Prop, xor a b -> xor b a.
Proof.
  intros a b H.
  destruct H as [H1|H2].
  right. exact H1.
  left. exact H2.
Qed.

Theorem and_comm: forall a b: Prop, (a /\ b) <-> (b /\ a).
Proof.
  intros a b.
  split; apply and_commutative.
  Qed.
Theorem or_comm: forall a b: Prop, (a \/ b) <-> (b \/ a).
Proof.
  intros a b.
  split; apply or_commutative.
  Qed.

Theorem xor_comm: forall a b: Prop, (xor a b) <-> (xor b a).
Proof.
  intros a b.
  split; apply xor_commutative.
  Qed.

Lemma ex4: 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
  Qed.

Lemma example6 : forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.
Proof.
  intros x y.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.add_assoc.
  rewrite <- Nat.add_assoc with (n := x * x).
  rewrite <- Nat.mul_comm with (n := x) (m := y).
  rewrite <- (Nat.mul_1_l (x * y)) at 1.
  rewrite <- Nat.mul_succ_l.
  rewrite Nat.mul_assoc.
  reflexivity.
  Qed.

(* exercise on logical connectives *)
Lemma and_assoc: forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
  intros. repeat destruct H as [HA H']. destruct H' as [HB HC].
  repeat split. exact HA. exact HB. exact HC.
  Qed.

Lemma and_comb: forall A B C D: Prop,(A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
  intros.
  destruct H. destruct H0. destruct H1.
  specialize (H H1).
  specialize (H0 H2).
  split. exact H. exact H0.
  Qed.

Lemma and_middle: forall A: Prop, ~(A/\~A).
Proof.
  intros A.
  unfold not. intros. destruct H.
  specialize (H0 H). exact H0.
  Qed.

Lemma or_assoc: forall A B C: Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
  intros.
  destruct H.
  left. left. exact H.
  destruct H.
  left. right. exact H.
  right. exact H.
  Qed.

Lemma disjunctive_syllogism: forall A B: Prop, (A\/B)/\~A -> B.
Proof.
  intros.
  unfold not in H.
  destruct H.
  destruct H.
  specialize (H0 H).
  contradiction.
  exact H.
  Qed.

Theorem quantify_disjunction: forall A:Type, forall P Q: A->Prop,
         (forall x, P x)\/(forall y, Q y)->forall x, P x\/Q x.
  Proof.
    intros A P Q H t.
    destruct H; specialize (H t).
    left. exact H.
    right. exact H.
    Qed.

