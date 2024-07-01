(* examples in text *)
Check True.
Check False.
Check 3.
Check (3+4).
Check (3=5).
Check (3, 3=5).
Check (fun x => x + 2).
Check (3=5 \/ True).
Check (3=5 /\ True).
Check nat.
Check nat -> Prop.
Check nat -> nat.
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
Check (let f := fun x => (x * 3, x > 3) in f 3).


(* exercise on functions *)
Definition sum5 := fun a b c d e => a + b + c + d + e.
Check sum5. (*should be nat -> nat -> nat -> nat -> nat -> nat *)
Check sum5 1 2 3 4 5.
Compute sum5 1 2 3 4 5.