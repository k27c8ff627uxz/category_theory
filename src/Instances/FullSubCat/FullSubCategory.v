From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Set Universe Polymorphism.

Program Definition FullSubCat (C : Category) (P : Obj C -> Prop) : Category :=
  {|
    Obj := { X : Obj C | P X };
    Hom := fun X Y => Hom (proj1_sig X) (proj1_sig Y);
    Hom_Id := fun X => \Id (proj1_sig X);
    Hom_comp := fun X Y Z => fun (f : Hom Y Z) (g : Hom X Y) => f \o g
  |}.
Next Obligation.
  by rewrite Hom_assoc.
Qed.
Next Obligation.
  by rewrite Hom_IdL.
Qed.
Next Obligation.
  by rewrite Hom_IdR.
Qed.
