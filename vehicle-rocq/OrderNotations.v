From mathcomp Require Import order.
Import Coq.ssr.ssrfun.
Export DefaultTupleProdOrder.
Open Scope order_scope.

Section PropOrder.

Context {d : Order.disp_t} {s : porderType d}.

Definition leProp x y := (is_true (@Order.le d s x y)).
Definition ltProp x y := (is_true (@Order.lt d s x y)).
Definition geProp x y := (is_true (@Order.ge d s x y)).
Definition gtProp x y := (is_true (@Order.gt d s x y)).

End PropOrder.

Notation "x <=P y" := (leProp x y) (at level 70): order_scope.
Notation "x >=P y" := (y <=P x) (at level 70, only parsing) : order_scope.

Notation "x <P y" := (ltProp x y) (at level 70): order_scope.
Notation "x >P y" := (y <P x) (at level 70, only parsing) : order_scope.