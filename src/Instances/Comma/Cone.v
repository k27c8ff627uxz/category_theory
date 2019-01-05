From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import Univ.FunctorCategory Comma.CommaCat Comma.CommaLR.

Set Universe Polymorphism.

Section Cone.
  
  Definition Cone {J C : Category} (F : Functor J C) :=
    CommaL (ToConstFunctor J C) (F : Obj (FunctorCategory J C)).
  
  Definition ConeVal
             {J C : Category} {F : Functor J C}
             (cone : Obj (Cone F))
    : Obj C := CommaLDom cone.
  
  Definition OfConeObj
             {J C : Category} {F : Functor J C}
             (cone : Obj (Cone F))
    : forall (X : Obj J), Hom (ConeVal cone) (FApp F X)
    := fun (X : Obj J) => NApp (OfCommaLObj cone) X.
  
  Lemma ConeComm :
    forall
      {J C : Category}
      {F : Functor J C}
      (cone : Obj (Cone F))
      (X1 X2 : Obj J)
      (f : Hom X1 X2),
      OfConeObj cone X2 = FAppH F f \o OfConeObj cone X1.
  Proof.
    move => J C F cone X1 X2 f.
    unfold OfConeObj.
    rewrite (NatTran_rectangle _ F (OfCommaLObj cone) X1 _ f).
    simpl.
    rewrite Hom_IdR.
    reflexivity.
  Qed.

  Definition ToConeObjCond
        {J C : Category}
        {F : Functor J C}
        (N : Obj C)
        (CHom : forall (X : Obj J), Hom N (FApp F X))
    := forall (X1 X2 : Obj J) (f : Hom X1 X2), CHom X2 = (FAppH F f) \o CHom X1.

  Program Definition ToConeObj
             {J C : Category}
             (F : Functor J C)
             (N : Obj C)
             (CHom : forall (X : Obj J), Hom N (FApp F X))
             (cond : ToConeObjCond  N CHom)
    : Obj (Cone F) :=
    ToCommaLObj
      _
      (F : Obj (FunctorCategory J C))
      N
      {| NApp := fun X => CHom X |}.
  Next Obligation.
  Proof.
    rewrite Hom_IdR.
    rewrite <- cond.
    reflexivity.
  Qed.

  Lemma Eq_ToConeObjCond
        {J C : Category}
        {F : Functor J C}
        (X : Obj (Cone F)) :
    ToConeObjCond (ConeVal X) (OfConeObj X).
  Proof.
    unfold ToConeObjCond.
    move => X1 X2 f.
    unfold OfConeObj.
    rewrite (NatTran_rectangle _ F (OfCommaLObj X)).
    rewrite /=.
    rewrite Hom_IdR.
    reflexivity.
  Qed.

  Lemma Eq_ToConeObj
        {J C : Category}
        {F : Functor J C}
        (X : Obj (Cone F)) :
    X = ToConeObj F (ConeVal X) (OfConeObj X) (Eq_ToConeObjCond X).
  Proof.
    unfold Cone in X.
    transitivity (ToCommaLObj (ToConstFunctor J C) F (CommaLDom X) (OfCommaLObj X)).
    exact: Eq_ToCommaLObj.
    unfold ToConeObj.
    unfold ConeVal.
    apply f_equal.
    apply ToNatTranEq.
    rewrite /=.
    apply functional_extensionality_dep.
    move => j.
    unfold OfConeObj.
    reflexivity.
  Qed.
    
  Definition ToConeHomCond
             {J C : Category}
             {F : Functor J C}
             {N1 N2 : Obj C}
             (CHom1 : forall (X : Obj J), Hom N1 (FApp F X))
             (CHom2 : forall (X : Obj J), Hom N2 (FApp F X))
             (f : Hom N1 N2)
    := forall (X : Obj J), CHom1 X = CHom2 X \o f.

  Program Definition ToConeHom
             {J C : Category}
             {F : Functor J C}
             {N1 N2 : Obj C}
             (CHom1 : forall (X : Obj J), Hom N1 (FApp F X))
             (CHom2 : forall (X : Obj J), Hom N2 (FApp F X))
             (cond1 : ToConeObjCond N1 CHom1)
             (cond2 : ToConeObjCond N2 CHom2)
             (f : Hom N1 N2)
             (cond : ToConeHomCond CHom1 CHom2 f)
    : Hom (ToConeObj _ N1 CHom1 cond1) (ToConeObj _ N2 CHom2 cond2) :=
    ToCommaLHom'
      (ToConeObj _ N1 CHom1 cond1)
      (ToConeObj _ N2 CHom2 cond2)
      f
      _.
  Next Obligation.
  Proof.
    unfold ToCommaLHom'Cond.
    apply ToNatTranEq.
    simpl.
    apply: functional_extensionality_dep.
    exact: cond.
  Qed.

End Cone.

Section Cocone.
  
  Definition Cocone {J C : Category} (F : Functor J C) :=
    CommaR (F : Obj (FunctorCategory J C)) (ToConstFunctor J C).
  
  Definition CoconeVal
             {J C : Category} {F : Functor J C}
             (cocone : Obj (Cocone F))
    : Obj C := CommaRCodom cocone.
  
  Definition OfCoconeObj
             {J C : Category} {F : Functor J C}
             (cocone : Obj (Cocone F))
    : forall (X : Obj J), Hom (FApp F X) (CoconeVal cocone)
    := fun (X : Obj J) => NApp (OfCommaRObj cocone) X.
  
  Lemma CoconeComm :
    forall
      {J C : Category}
      {F : Functor J C}
      (cocone : Obj (Cocone F))
      (X1 X2 : Obj J)
      (f : Hom X1 X2),
      OfCoconeObj cocone X1 = OfCoconeObj cocone X2 \o FAppH F f.
  Proof.
    move => J C F cocone X1 X2 f.
    unfold OfCoconeObj.
    move: (NatTran_rectangle F _ (OfCommaRObj cocone) _ X2 f) =><-.
    simpl.
    rewrite Hom_IdL.
    reflexivity.
  Qed.

  Definition ToCoconeObjCond
        {J C : Category}
        {F : Functor J C}
        (N : Obj C)
        (CHom : forall (X : Obj J), Hom (FApp F X) N)
    := forall (X1 X2 : Obj J) (f : Hom X1 X2), CHom X1 = CHom X2 \o (FAppH F f).

  Program Definition ToCoconeObj
             {J C : Category}
             (F : Functor J C)
             (N : Obj C)
             (CHom : forall (X : Obj J), Hom (FApp F X) N)
             (cond : ToCoconeObjCond  N CHom)
    : Obj (Cocone F) :=
    ToCommaRObj
      (F : Obj (FunctorCategory J C))
      _
      N
      {| NApp := fun X => CHom X |}.
  Next Obligation.
  Proof.
    rewrite Hom_IdL.
    rewrite <- cond.
    reflexivity.
  Qed.

  Lemma Eq_ToCoconeObjCond
        {J C : Category}
        {F : Functor J C}
        (X : Obj (Cocone F)) :
    ToCoconeObjCond (CoconeVal X) (OfCoconeObj X).
  Proof.
    unfold ToConeObjCond.
    move => X1 X2 f.
    unfold OfCoconeObj.
    rewrite <- (NatTran_rectangle F _ (OfCommaRObj X)).
    rewrite /=.
    rewrite Hom_IdL.
    reflexivity.
  Qed.

  Lemma Eq_ToCoconeObj
        {J C : Category}
        {F : Functor J C}
        (X : Obj (Cocone F)) :
    X = ToCoconeObj F (CoconeVal X) (OfCoconeObj X) (Eq_ToCoconeObjCond X).
  Proof.
    unfold Cocone in X.
    transitivity (ToCommaRObj (F : Obj (FunctorCategory J C)) (ToConstFunctor J C) (CommaRCodom X) (OfCommaRObj X)).
    exact: Eq_ToCommaRObj.
    unfold ToCoconeObj.
    unfold CoconeVal.
    apply f_equal.
    apply ToNatTranEq.
    rewrite /=.
    apply functional_extensionality_dep.
    move => j.
    unfold OfCoconeObj.
    reflexivity.
  Qed.
  
  Definition ToCoconeHomCond
             {J C : Category}
             {F : Functor J C}
             {N1 N2 : Obj C}
             (CHom1 : forall (X : Obj J), Hom (FApp F X) N1)
             (CHom2 : forall (X : Obj J), Hom (FApp F X) N2)
             (f : Hom N1 N2)
    := forall (X : Obj J), CHom2 X = f \o CHom1 X.

  Program Definition ToCoconeHom
             {J C : Category}
             {F : Functor J C}
             {N1 N2 : Obj C}
             (CHom1 : forall (X : Obj J), Hom (FApp F X) N1)
             (CHom2 : forall (X : Obj J), Hom (FApp F X) N2)
             (cond1 : ToCoconeObjCond N1 CHom1)
             (cond2 : ToCoconeObjCond N2 CHom2)
             (f : Hom N1 N2)
             (cond : ToCoconeHomCond CHom1 CHom2 f)
    : Hom (ToCoconeObj _ N1 CHom1 cond1) (ToCoconeObj _ N2 CHom2 cond2) :=
    ToCommaRHom'
      (ToCoconeObj _ N1 CHom1 cond1)
      (ToCoconeObj _ N2 CHom2 cond2)
      f
      _.
  Next Obligation.
  Proof.
    unfold ToCommaRHom'Cond.
    apply ToNatTranEq.
    simpl.
    apply: functional_extensionality_dep.
    exact: cond.
  Qed.

End Cocone.

