
From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Set Universe Polymorphism.

Open Scope type_scope.

Program Definition ProductCat (C D : Category) : Category :=
  {|
    Obj := (Obj C) * (Obj D);
    Hom := fun X Y => Hom (fst X) (fst Y) * Hom (snd X) (snd Y);
    Hom_Id := fun X => pair (\Id (fst X)) (\Id (snd X));
    Hom_comp :=
      fun (X Y Z : (Obj C) * (Obj D)) =>
        fun
          (f1 : Hom (fst Y) (fst Z) * Hom (snd Y) (snd Z))
          (f2 : Hom (fst X) (fst Y) * Hom (snd X) (snd Y))
        => pair (fst f1 \o fst f2) (snd f1 \o snd f2)
          
  |}.
Next Obligation.
Proof.  
  rewrite /=.
  by repeat rewrite Hom_assoc.
Qed.
Next Obligation.
  rewrite /=.
  by repeat rewrite Hom_IdL.
Qed.
Next Obligation.
  rewrite /=.
  by repeat rewrite Hom_IdR.
Qed.


Program Definition DiagonalFunctor (C : Category) : Functor C (ProductCat C C) :=
  {|
    FApp := fun (X : Obj C) => pair X X;
    FAppH := fun (X Y : Obj C) (f : Hom X Y) => pair f f
  |}.

                                    
