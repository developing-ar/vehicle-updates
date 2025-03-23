Require Import Vehicle.Real.
From mathcomp Require Import ssralg ssrfun seq tuple fintype reals order.
Open Scope form_scope.

Definition tensor (A : Type) : seq nat -> Type := 
    foldr tuple_of A.

Definition tensor_of {A} : A -> tensor A [::] := id.

Definition stack {A d} : d.-tuple (tensor A nil) -> tensor A (d :: nil) := id.

Definition unstack {A d} : tensor A (d :: nil) -> d.-tuple (tensor A nil) := id.

Definition foreach {A d} (f : 'I_d -> tensor A [::]) : tensor A ([:: d]) := 
    [tuple f i | i < d].

Fixpoint const {A} (v : A) (ds : list nat) : tensor A ds :=
    match ds with
    | [::] => v
    | d :: ds => foreach (fun=> const v ds)
    end.

Local Fixpoint map {A B ds} (f : A -> B) : tensor A ds -> tensor B ds :=
    match ds with
    | [::] => f
    | d :: ds => map_tuple (map f)
    end.

Fixpoint zip {A B ds} : tensor A ds -> tensor B ds -> tensor (A * B) ds :=
    match ds with
    | [::] => pair
    | d :: ds => fun xs ys => [tuple zip (tnth xs i) (tnth ys i) | i < d]
    end.

Definition zipWith {A B C ds} (f : A -> B -> C) (xs : tensor A ds) (ys : tensor B ds) : tensor C ds :=
    map (uncurry f) (zip xs ys).

Fixpoint toList {A ds} : tensor A ds -> list A :=
    match ds with
    | [::] => fun (t : A) => [:: t]
    | d :: ds => fun t => flatten (seq.map toList t)
    end.

Definition reduce {A B ds} (f : A -> B -> B) (a : B) (t : tensor A ds) : B := foldr f a (toList t).
Definition reduceAnd {ds} : tensor bool ds -> bool := reduce andb true.
Definition reduceOr {ds} : tensor bool ds -> bool := reduce orb false.

Definition pointwise {A B ds} (f : A -> B -> Prop) (xs : tensor A ds) (ys : tensor B ds) : Prop :=
    reduce and True (zipWith f xs ys).

Section TensorOperations.

Open Scope ring_scope.

Context {ds : list nat}.
Notation zipWithR := (@zipWith R R R ds) (only parsing).
Notation mapR := (@map R R ds) (only parsing).

Definition add := zipWithR GRing.add.
Definition sub := zipWithR (fun x y => GRing.add x (GRing.opp y)).
Definition mul := zipWithR GRing.mul.
Definition opp := mapR GRing.opp.
Definition max := zipWithR Order.max.
Definition min := zipWithR Order.min.
Definition inv := mapR GRing.inv.

End TensorOperations.

Infix "+" := add : tensor_scope.
Infix "-" := sub : tensor_scope.
Infix "*" := mul : tensor_scope.
Notation "- t" := (opp t) : tensor_scope.
Notation "x - y" := (add x (opp y)) : tensor_scope.
Notation "x ^-1" := (inv x) : tensor_scope.
Notation "x / y" := (mul x (inv y)) : tensor_scope.