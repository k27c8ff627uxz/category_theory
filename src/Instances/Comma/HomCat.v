
From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import Univ.FunctorComp Comma.CommaCat.

Definition HomCat (C : Category) : Category := CommaCat (IdFunctor C) (IdFunctor C).

Definition ToHomCat {C : Category} {X Y : Obj C} (f : Hom X Y) : Obj (HomCat C) :=
  existT _ (pair X Y) f.



Definition Hom_equiv {C : Category} {X1 Y1 X2 Y2 : Obj C} (f : Hom X1 Y1) (g : Hom X2 Y2) := ToHomCat f ~~~ ToHomCat g in (HomCat C).
