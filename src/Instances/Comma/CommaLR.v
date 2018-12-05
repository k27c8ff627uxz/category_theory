From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import DiscreteCat Univ.FunctorComp Comma.CommaCat.

Set Universe Polymorphism.

Section CommaRight.

  Context {C D : Category}.
  
  Definition CommaR (A : Obj C) (F : Functor D C) :=
    CommaCat (ConstFunctor Cat1 A) F.
  
  Definition CommaRCodom
             {A : Obj C} {F : Functor D C}
             (f : Obj (CommaR A F)) : Obj D := CommaCodom f.
  
  Definition OfCommaRObj
             {A : Obj C} {F : Functor D C}
             (f : Obj (CommaR A F)) : Hom A (FApp F (CommaRCodom f)) :=
    OfCommaObj f.
  
  Definition ToCommaRObj
             (A : Obj C) (F : Functor D C)
             (X : Obj D)
             (f : Hom A (FApp F X))
    : Obj (CommaR A F) :=
    ToCommaObj
      (ConstFunctor Cat1 A) F Cat1Obj X f.
  
  Lemma Eq_ToCommaRObj
        (A : Obj C) (F : Functor D C) :
    forall (h : Obj (CommaR A F)),
      h = (ToCommaRObj A F (CommaRCodom h) (OfCommaRObj h)).
  Proof.
    unfold CommaR.
    unfold ToCommaRObj.
    unfold CommaRCodom.
    unfold OfCommaRObj.
    move => h.
    rewrite (Cat1Obj_eq Cat1Obj (CommaDom h)).
    exact : Eq_ToCommaObj.
  Qed.
  
  Definition ToCommaRHomCond
             {A : Obj C} {F : Functor D C}
             {X1 X2 : Obj D}
             (h1 : Hom A (FApp F X1)) (h2 : Hom A (FApp F X2))
             (f : Hom X1 X2) :=
    h2 = (FAppH F f) \o h1.
  
  Program Definition ToCommaRHom
          {A : Obj C} {F : Functor D C}
          {X1 X2 : Obj D}
          (h1 : Hom A (FApp F X1)) (h2 : Hom A (FApp F X2))
          (f : Hom X1 X2)
          (cond : ToCommaRHomCond h1 h2 f)
    : Hom (ToCommaRObj A F X1 h1) (ToCommaRObj A F X2 h2) :=
    exist _ (pair (\Id Cat1Obj) f) _.
  Next Obligation.
  Proof.
    move: cond =>->.
    rewrite Hom_IdR.
    reflexivity.
  Qed.

  Definition CommaRHom_snd
             {A : Obj C} {F : Functor D C}
             {f1 f2 : Obj (CommaR A F)} (hh : Hom f1 f2)
    : Hom (CommaRCodom f1) (CommaRCodom f2) := CommaHom_snd hh.

  Lemma ToCommaRHomEq :
    forall {A : Obj C} {F : Functor D C},
    forall {ff1 ff2 : Obj (CommaR A F)},
    forall (hh gg : Hom ff1 ff2),
      CommaRHom_snd hh = CommaRHom_snd gg -> hh = gg.
  Proof.
    move => A F ff1 ff2 hh gg eqH.
    apply: ToCommaHomEq.
    exact: Cat1Hom_eq.
    exact: eqH.
  Qed.

  Lemma CommaRHom_Cond
        {A : Obj C} {F : Functor D C}
        {X1 X2 : Obj D}
        {f1 : Hom A (FApp F X1)}
        {f2 : Hom A (FApp F X2)} :
    forall (ff : Hom (ToCommaRObj A F X1 f1) (ToCommaRObj A F X2 f2)),
      f2 = (FAppH F (CommaRHom_snd ff)) \o f1.
  Proof.
    unfold ToCommaRObj.
    move => ff.
    move: (CommaHom_Cond ff).
    simpl.
    rewrite Hom_IdR.
    move =>->.
    reflexivity.
  Qed.
    
End CommaRight.


Section CommaLeft.

  Context {C D : Category}.
  
  Definition CommaL (F : Functor D C) (A : Obj C):=
    CommaCat F (ConstFunctor Cat1 A).
  
  Definition CommaLDom
             {F : Functor D C} {A : Obj C}
             (f : Obj (CommaL F A)) : Obj D := CommaDom f.
  
  Definition OfCommaLObj
             {F : Functor D C} {A : Obj C}
             (f : Obj (CommaL F A)) : Hom (FApp F (CommaLDom f)) A :=
    OfCommaObj f.
  
  Definition ToCommaLObj
             (F : Functor D C) (A : Obj C)
             (X : Obj D)
             (f : Hom (FApp F X) A)
    : Obj (CommaL F A) :=
    ToCommaObj
      F (ConstFunctor Cat1 A) X I f.
  
  Lemma Eq_ToCommaLObj
        (F : Functor D C) (A : Obj C) :
    forall (h : Obj (CommaL F A)),
      h = (ToCommaLObj F A (CommaLDom h) (OfCommaLObj h)).
  Proof.
    unfold CommaL.
    unfold ToCommaLObj.
    unfold CommaLDom.
    unfold OfCommaLObj.
    move => h.
    rewrite(_ : I = (CommaCodom h)).
    exact : Eq_ToCommaObj.
    case: h.
    case.
    move => X.
    case.
    unfold CommaCodom.
    unfold Comma.codom.
    simpl.
      by [].
  Qed.
  
  Definition ToCommaLHomCond
             {F : Functor D C} {A : Obj C}
             {X1 X2 : Obj D}
             (h1 : Hom (FApp F X1) A) (h2 : Hom (FApp F X2) A)
             (f : Hom X1 X2) :=
    h1 = h2 \o (FAppH F f).
  
  Program Definition ToCommaLHom
          {F : Functor D C} {A : Obj C}
          {X1 X2 : Obj D}
          (h1 : Hom (FApp F X1) A) (h2 : Hom (FApp F X2) A)
          (f : Hom X1 X2)
          (cond : ToCommaLHomCond h1 h2 f)
    : Hom (ToCommaLObj F A X1 h1) (ToCommaLObj F A X2 h2) :=
    exist _ (pair f (\Id (I : Obj Cat1))) _.
  Next Obligation.
  Proof.
    move: cond =>->.
    rewrite Hom_IdL.
    reflexivity.
  Qed.

  Definition CommaLHom_fst
             {F : Functor D C} {A : Obj C}
             {f1 f2 : Obj (CommaL F A)} (hh : Hom f1 f2)
    : Hom (CommaLDom f1) (CommaLDom f2) := CommaHom_fst hh.
  
  Lemma ToCommaLHomEq :
    forall {F : Functor D C} {A : Obj C},
    forall {ff1 ff2 : Obj (CommaL F A)},
    forall (hh gg : Hom ff1 ff2),
      CommaLHom_fst hh = CommaLHom_fst gg -> hh = gg.
  Proof.
    move => A F ff1 ff2 hh gg eqH.
    apply: ToCommaHomEq.
    exact: eqH.
    exact: Cat1Hom_eq.
  Qed.    

  Lemma CommaLHom_Cond
        {F : Functor D C} {A : Obj C}
        {X1 X2 : Obj D}
        {f1 : Hom (FApp F X1) A}
        {f2 : Hom (FApp F X2)A } :
    forall (ff : Hom (ToCommaLObj F A X1 f1) (ToCommaLObj F A X2 f2)),
      f1 = f2 \o (FAppH F (CommaLHom_fst ff)).
  Proof.
    unfold ToCommaLObj.
    move => ff.
    move: (CommaHom_Cond ff).
    simpl.
    rewrite Hom_IdL.
    move =><-.
    reflexivity.
  Qed.

End CommaLeft.
