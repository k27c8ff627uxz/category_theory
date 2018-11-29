
From Category.Base Require Import Logic Category Functor NatTran.

Set Universe Polymorphism.

Program Definition Types : Category :=
  {|
    Obj := Type ;
    Hom := fun (T1 T2 : Type) => T1 -> T2 ;
    Hom_Id := fun (A : Type) => fun a => a ;
    Hom_comp := fun (A B C : Type) => fun f g => fun c => f (g c)
  |}.

Program Definition Sets : Category :=
  {|
    Obj := Set ;
    Hom := fun (T1 T2 : Set) => T1 -> T2 ;
    Hom_Id := fun (A : Set) => fun a => a ;
    Hom_comp := fun (A B C : Set) => fun f g => fun c => f (g c)
  |}.


