From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Program Definition DiscreteCat (A : Type) : Category :=
  {|
    Obj := A;
    Hom := fun x y => x = y;
  |}.

Definition Cat1 := DiscreteCat True.
Definition Cat0 := DiscreteCat False.
