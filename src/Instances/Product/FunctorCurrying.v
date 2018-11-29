From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import NatTranComp FunctorCategory Product.ProductCategory.

Set Universe Polymorphism.

(* Currying *)
Module Currying.

  Section Currying.

    Context {C D E : Category}.
    Variable F : Functor (ProductCat C D) E.

    Program Definition Curry (X : Obj C) : Functor D E :=
      {|
        FApp := fun Y => FApp F (pair X Y);
        FAppH := fun Y1 Y2 (g : Hom Y1 Y2)
                 => FAppH F (pair (\Id X) g : @Hom (ProductCat C D) (pair X Y1) (pair X Y2))
      |}.
    Next Obligation.
    Proof.
      rewrite <- FAppH_comp_eq.
      rewrite /=.
      rewrite Hom_IdL.
      reflexivity.
    Qed.
    Next Obligation.
      rewrite Functor_id_eq.
      reflexivity.
    Qed.

    Program Definition Curry_Hom {X1 X2 : Obj C} (f : Hom X1 X2) : NatTran (Curry X1) (Curry X2) :=
      {|
        NApp := fun Y => FAppH F (pair f (\Id Y) : @Hom (ProductCat C D) (pair X1 Y) (pair X2 Y))
      |}.
    Next Obligation.
    Proof.
      repeat rewrite <- FAppH_comp_eq.
      rewrite /=.
      repeat rewrite Hom_IdL.
      repeat rewrite Hom_IdR.
      reflexivity.
    Qed.

  End Currying.

  
End Currying.


Program Definition FunctorCurrying {C D E : Category} (F : Functor (ProductCat C D) E) : Functor C (FunctorCategory D E) :=
  {|
    FApp := fun X => Currying.Curry F X;
    FAppH := fun X1 X2 f => Currying.Curry_Hom F f
  |}.
Next Obligation.
Proof.
  apply: ToNatTranEq.
  rewrite /=.
  apply: functional_extensionality_dep.
  move => W.
  rewrite <- FAppH_comp_eq.
  rewrite /=.
  rewrite Hom_IdL.
  reflexivity.
Qed.
Next Obligation.
Proof.
  apply: ToNatTranEq.
  rewrite /=.
  apply: functional_extensionality_dep.
  move => W.
  rewrite Functor_id_eq.
  reflexivity.
Qed.




(* Uncurrying *)

Program Definition FunctorUncurrying {C D E : Category} (G : Functor C (FunctorCategory D E))
  : Functor (ProductCat C D) E :=
  {|
    FApp := fun X => FApp (FApp G (fst X)) (snd X);
    FAppH := fun X1 X2 p =>
               FAppH (FApp G (fst X2)) (snd p) \o NApp (FAppH G (fst p)) (snd X1)
  |}.
Next Obligation.
Proof.
  rewrite /=.
  repeat rewrite FAppH_comp_eq.
  rewrite (Hom_assoc (FAppH (FApp G o) h2) (FAppH (FApp G o) h0)).
  rewrite (Hom_assoc (FAppH (FApp G o) h2) (NApp (FAppH G h1) o2)).
  apply: f_equal.
  rewrite /=.
  repeat rewrite <- Hom_assoc.
  apply: (f_equal (fun a => a \o NApp (FAppH G h) o4)).
  rewrite <- NatTran_rectangle.
  reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite /=.
  rewrite Functor_id_eq.
  rewrite Hom_IdL.
  rewrite Functor_id_eq.
  rewrite /=.
  reflexivity.
Qed.

Lemma F_currying_uncurrying_eq {C D E : Category} :
  forall (G : Functor C (FunctorCategory D E)),
    FunctorCurrying (FunctorUncurrying G) = G.
Proof.
  move => G.
  apply: ToFunctorEq => X1 X2 f.
  unfold Hom_eq'.
  have: (forall (X : Obj C), FApp (FunctorCurrying (FunctorUncurrying G)) X = FApp G X).
  {
    move => X.
    apply: ToFunctorEq => Y1 Y2 g.
    unfold Hom_eq'.
    rewrite /=.
    apply: eq_Hom_eq'.
    rewrite Functor_id_eq.
    rewrite /=.
    rewrite Hom_IdR.
    reflexivity.
  } 
  move => Curry_eqH.
  exists (Curry_eqH X1).
  exists (Curry_eqH X2).
  rewrite /=.
  apply: ToNatTranEq.
  apply: functional_extensionality_dep.
  move => Y.
  rewrite /=.
  rewrite Functor_id_eq.
  rewrite Hom_IdL.
  have: (forall (X : Obj C), FApp (FApp G X) Y = FApp (FApp (FunctorCurrying (FunctorUncurrying G)) X) Y).
  {
    move => X.
    move: (Curry_eqH X) =>->.
    reflexivity.
  }
  move => Curry_eqH'.
  transitivity (NApp (HomId' (Curry_eqH X2)) Y \o (HomId' (Curry_eqH' X2)) \o NApp (FAppH G f) Y).
  {
    apply: f_equal.
    simpl in Curry_eqH'.
    rewrite HomId'_id.
    rewrite Hom_IdL.
    reflexivity.
  }
  transitivity (NApp (FAppH G f) Y \o NApp (HomId' (Curry_eqH X1)) Y \o HomId' (Curry_eqH' X1)).
  {
    rewrite (NApp_HomId'_eq (Curry_eqH X2) Y (eq_sym (Curry_eqH' X2))).
    rewrite (NApp_HomId'_eq (Curry_eqH X1) Y (eq_sym (Curry_eqH' X1))).
    rewrite /=.
    rewrite HomId'_sym_id.
    rewrite Hom_IdR.
    rewrite <- Hom_assoc.
    rewrite HomId'_sym_id.
    rewrite Hom_IdL.
    reflexivity.
  }
  simpl in Curry_eqH'.
  rewrite HomId'_id.
  rewrite Hom_IdR.
  reflexivity.
Qed.

Lemma F_uncurrying_currying_eq {C D E : Category} :
  forall (F : Functor (ProductCat C D) E),
    FunctorUncurrying (FunctorCurrying F) = F.
Proof.
  move => F.
  apply: ToFunctorEq.
  case => X1 X2.
  case => Y1 Y2.
  case.
  rewrite /=.
  move => f1 f2.
  apply eq_Hom_eq'.
  rewrite <- FAppH_comp_eq.
  rewrite /=.
  rewrite Hom_IdL.
  rewrite Hom_IdR.
  reflexivity.
Qed.
