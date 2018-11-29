
From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import Types Product.ProductCategory Opposite.


Definition Prod_Op_N (C : Category) : Category := ProductCat (OppositeCat C) C.
Definition Pair_Obj {C : Category} (X Y : Obj C) : Obj (Prod_Op_N C) := pair X Y.

Definition Prod_Hom_fst {C : Category} {X Y : Obj (Prod_Op_N C)} (p : Hom X Y) : @Hom C (fst Y) (fst X) := fst p.
Definition Prod_Hom_snd {C : Category} {X Y : Obj (Prod_Op_N C)} (p : Hom X Y) : @Hom C (snd X) (snd Y) := snd p.

Axiom C : Category.
Axiom X Y : Obj (Prod_Op_N C).
Axiom (p : Hom X Y).
Definition FApp_ := fun (X : Obj (Prod_Op_N C)) => (@Hom C (fst X) (snd X) : Obj Types).
Check FApp_.
Definition FAppH_ := fun (m : @Hom C (fst X) (snd X)) => (Prod_Hom_snd p) \o m \o (Prod_Hom_fst p).
Check FAppH_.
Check (FAppH_ : @Hom Types (FApp_ X) (FApp_ Y)).


Program Definition HomFunctor (C : Category) : Functor (ProductCat (OppositeCat C) C) Types :=
  {|
    FApp := fun X => @Hom C (fst X) (snd X);
    FAppH := fun X Y p =>
               fun (m : @Hom C (fst X) (snd X)) => (Prod_Hom_snd p) \o m \o (Prod_Hom_fst p)
  |}.
Next Obligation.
Proof.
  rewrite /=.
  apply: functional_extensionality.
  move => f.
  rewrite <- (Hom_assoc h2 _ h1).
  rewrite <- (Hom_assoc h2 h0 _).
  rewrite (Hom_assoc (h2 \o h0) (f \o h)).
  rewrite (Hom_assoc f h h1).
  reflexivity.
Qed.
Next Obligation.
  rewrite /=.
  apply: functional_extensionality.
  move => f.
  rewrite Hom_IdL.
  by rewrite Hom_IdR.
Qed.
