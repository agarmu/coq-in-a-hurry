Require Import Arith.

Inductive bin : Type :=
  L : bin
| N : bin -> bin -> bin.

Inductive tc: Type :=
  X : tc
| Y: nat -> tc -> tc -> tc
| Z: bool -> tc -> tc -> tc -> tc.

Fixpoint flatten_aux (t1 t2:bin) : bin :=
  match t1 with
    L => N L t2
  | N q1 q2 => flatten_aux q1 (flatten_aux q2 t2)
  end.
Fixpoint flatten (t:bin) : bin :=
  match t with
    L => L | N t1 t2 => flatten_aux t1 (flatten t2)
  end.

Fixpoint size (t:bin) : nat :=
  match t with
    L => 1 | N t1 t2 => 1 + size t1 + size t2
  end. 

Definition example7 (t : bin): bool :=
  match t with N L L => false | _ => true end.

Lemma example7_size :
   forall t, example7 t = false -> size t = 3.
Proof.
    intros t; destruct t.
    simpl; discriminate.
    destruct t1, t2; simpl.
    reflexivity.
    discriminate.
    discriminate.
    discriminate.
    Qed.

Lemma flatten_aux_size :
 forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
Proof.
    induction t1; simpl; intros.
    ring.
    rewrite IHt1_1.
    rewrite IHt1_2.
    ring.
    Qed.


Lemma not_subterm_self_l : forall x y, x <> N x y.
Proof.
    induction x; intros y.
    discriminate.
    intros contra.
    injection contra.
    intros.
    assert (IHx1_ : x1 <> N x1 x2).
    apply IHx1.
    case IHx1_.
    exact H0.
    Qed.


Lemma flatten_size : forall t, size (flatten t) = size t.
Proof.
  intros t.
  induction t.
  simpl. reflexivity.
  simpl. rewrite flatten_aux_size.
  rewrite IHt2. ring.
  Qed.