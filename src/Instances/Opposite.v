
From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.


Program Definition OppositeCat (C : Category) : Category :=
  {|
    Obj := Obj C;
    Hom := fun (X Y : Obj C) => Hom Y X;
    Hom_Id := fun (X : Obj C) => \Id X;
    Hom_comp := fun (X Y Z : Obj C) (f : Hom Z Y) (g : Hom Y X) => g \o f
  |}.
Next Obligation.
Proof.
  by rewrite Hom_assoc.
Qed.
Next Obligation.
Proof.
  by rewrite Hom_IdR.
Qed.
Next Obligation.
Proof.
  by rewrite Hom_IdL.
Qed.
