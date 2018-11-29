From mathcomp Require Import ssreflect.
From Coq.Logic Require Export JMeq EqdepFacts.
From Category.Base Require Import Logic Category Functor NatTran.

Set Universe Polymorphism.

Section WideSubcategory.

  Context {C : Category}.

  Variable P : forall (X Y : Obj C), Hom X Y -> Prop.

  Definition WideSubCatCond : Prop :=
    (forall (X : Obj C), P _ _ (\Id X)) /\
    (forall (X Y Z : Obj C) (f : Hom Y Z) (g : Hom X Y), P _ _ f -> P _ _ g -> P _ _ (f \o g)).
  
  Program Definition WideSubcategory (cond : WideSubCatCond) : Category :=
    {|
      Obj := Obj C;
      Hom := fun X Y => { f : Hom X Y | P _ _ f};
      Hom_Id := fun X => exist _ (\Id X) ((proj1 cond) X);
      Hom_comp := fun X Y Z => fun f g => exist _ (proj1_sig f \o proj1_sig g) ((proj2 cond) _ _ _ _ _ (proj2_sig f) (proj2_sig g))
    |}.
  Next Obligation.
  Proof.
    rewrite /=.
    apply: eq_dep_eq_sig.
    apply: JMeq_eq_dep.
    exact: Hom_assoc.
    exact: p_proof_irrelevance_jmeq.
  Qed.
  Next Obligation.
    rewrite /=.
    apply: eq_dep_eq_sig.
    apply: JMeq_eq_dep.
    exact: Hom_IdL.
    exact: p_proof_irrelevance_jmeq.
  Qed.
  Next Obligation.
    rewrite /=.
    apply: eq_dep_eq_sig.
    apply: JMeq_eq_dep.
    exact: Hom_IdR.
    exact: p_proof_irrelevance_jmeq.
  Qed.

End WideSubcategory.

