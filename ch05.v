Definition is_zero (n:nat) := match n with
    | 0 => true
    | _ => false
end.

Lemma not_is_zero_pred :
  forall x, is_zero x = false -> S (Nat.pred x) = x.
  intros x.
  unfold is_zero, Nat.pred.
  destruct x as [|p]. discriminate.
  intros.
  reflexivity.
  Qed.
  