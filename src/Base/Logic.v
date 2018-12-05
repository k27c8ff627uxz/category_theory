
From mathcomp Require Import ssreflect.
From Coq.Logic Require Export ClassicalFacts JMeq FunctionalExtensionality.

Axiom p_prop_extensionality : prop_extensionality.

Lemma prop_eqTrue : forall (P : Prop) (p : P), JMeq p I.
Proof.
  move => P p.
  have: (P = True).
  {
    apply: provable_prop_ext.
    exact p_prop_extensionality.
    by [].
  }
  move => eqP.
  move: eqP p =>->.
  case.
  reflexivity.
Qed.

Lemma p_proof_irrelevance_jmeq : forall (P : Prop) (p : P) (Q : Prop) (q : Q), JMeq p q.
Proof.
  move => P p Q q.
  apply: (@JMeq_trans _ True _ _ I _).
  exact: prop_eqTrue.
  symmetry.
  exact: prop_eqTrue.
Qed.

Lemma p_proof_irrelevance : proof_irrelevance.
Proof.
  move => P p1 p2.
  apply: JMeq_eq.
  exact: p_proof_irrelevance_jmeq.
Qed.

Lemma eq_exist_eq : forall {A} (P : A -> Prop) (a1 a2 : A) (prf1 : P a1) (prf2 : P a2),
    a1 = a2 -> exist P a1 prf1 = exist P a2 prf2.
Proof.
  move => A P a1 a2 prf1 prf2 eqa.
  subst.
  rewrite(_ : prf1 = prf2).
  reflexivity.
  exact: p_proof_irrelevance.
Qed.

Axiom
  dependent_unique_choice :
    forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
      (forall x : A, exists! y : B x, R x y) ->
      (exists f : (forall x:A, B x), forall x:A, R x (f x)).

Theorem unique_choice :
 forall (A B:Type) (R:A -> B -> Prop),
   (forall x:A, exists! y : B, R x y) ->
   (exists f:A->B, forall x:A, R x (f x)).
Proof.
  move => A B R cond.
  by apply: dependent_unique_choice.
Qed.  

Lemma eq_JMeq {A} : forall {x y : A}, x = y -> JMeq x y.
Proof.
  move => x y =>->.
  exact: JMeq_refl.
Qed.

