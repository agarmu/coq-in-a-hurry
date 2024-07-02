Require Import List.
Require Import Nat.

(* for n in NN, make list 0 :: 1 :: ... :: n-1 *)
Fixpoint make_list (n:nat) :=
    match n with
    0 => nil
    | S p => app (make_list p) (p::nil)
    end.

Compute make_list 10.

Fixpoint is_list_sorted (l:list nat) :=
    match l with
    | a::x::xs => (a <= x) /\ (is_list_sorted xs)
    | _ => True
    end.

Compute is_list_sorted (1::2::nil).

Fixpoint count_equal_helper (acc:nat) (val:nat) (l:list nat) :=
    match l with
    | nil => acc
    | x::xs => if x =? val then count_equal_helper (acc+1) val xs else count_equal_helper acc val xs
    end.

Definition count_equal (val:nat) (l:list nat) := count_equal_helper 0 val l.

Compute count_equal 5 (1::2::5::3::5::0::1::nil).

