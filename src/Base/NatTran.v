
From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.
From Category.Base Require Import Logic Category Functor.

Structure NatTran {C D : Category} (F G : Functor C D) : Type :=
  {
    NApp : forall (X : Obj C), Hom (FApp F X) (FApp G X);

    (* Conditions *)
    NatTran_rectangle : forall (X Y : Obj C) (f : Hom X Y), FAppH G f \o (NApp X) = (NApp Y) \o FAppH F f
  }.

Global Arguments NApp {C D} {F G}.




Lemma ToNatTranEq {C D : Category} {F G : Functor C D} :
  forall (N1 N2 : NatTran F G), NApp N1 = NApp N2 -> N1 = N2.
Proof.
  case => NApp1 NCond1.
  case => NApp2 NCond2.
  rewrite /=.
  move => eqNApp.
  move: eqNApp NCond2 =><- NCond2.
  rewrite (_: NCond1 = NCond2).
  reflexivity.
  exact: p_proof_irrelevance.
Qed.  
