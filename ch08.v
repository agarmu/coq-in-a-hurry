Fixpoint nat_fact (n:nat) : nat :=
  match n with O => 1 | S p => S p * nat_fact p end.


Fixpoint fib (n:nat) : nat :=
    match n with
    | 0 => 0
    | S q => match q with
        | 0 => 1
        | r => (fib r) + (fib q)
    end
    end.