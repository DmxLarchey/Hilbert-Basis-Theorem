(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Ring Setoid Utf8.

Require Import utils.

Set Implicit Arguments.

(** Definition of a ring *)

Record ring := {
  carrier :> Type;
  un_a : carrier;
  op_a : carrier → carrier → carrier;
  iv_a : carrier → carrier;
  un_m : carrier;
  op_m : carrier → carrier → carrier;
  req  : carrier → carrier → Prop;
  eq_equiv : Equivalence req;
  is_ring : @ring_theory carrier un_a un_m op_a op_m (λ x y, op_a x (iv_a y)) iv_a req;
  eq_ext : @ring_eq_ext carrier op_a op_m iv_a req
}.

Arguments un_a {_}.
Arguments un_m {_}.
Arguments op_a {_}.
Arguments op_m {_}.
Arguments iv_a {_}.
Arguments req  {_}.

Notation "0ᵣ" := un_a.
Notation "1ᵣ" := un_m.

Notation "x ∼ᵣ y" := (req x y) (at level 70, no associativity, format "x  ∼ᵣ  y").
Notation "x +ᵣ y" := (op_a x y) (at level 31, left associativity, format "x  +ᵣ  y").
Notation "-ᵣ x" := (iv_a x) (at level 25, right associativity, format "-ᵣ x").
Notation "x −ᵣ y" := (x +ᵣ -ᵣ y) (at level 31, left associativity, format "x  −ᵣ  y").
Notation "x *ᵣ y" := (op_m x y) (at level 29, left associativity, format "x  *ᵣ  y").

Fact ring_eq_refl (R : ring) (x : R) : x ∼ᵣ x.
Proof. apply eq_equiv. Qed.

Fact ring_eq_sym (R : ring) (x y : R) : x ∼ᵣ y → y ∼ᵣ x.
Proof. apply eq_equiv. Qed.

Fact ring_eq_trans (R : ring) (x y z : R) : x ∼ᵣ y → y ∼ᵣ z → x ∼ᵣ z.
Proof. apply eq_equiv. Qed.

Hint Resolve ring_eq_refl ring_eq_sym ring_eq_trans : core.

Add Parametric Relation (R : ring) : R req 
     reflexivity proved by (ring_eq_refl _)
     symmetry proved by (ring_eq_sym _)
     transitivity proved by (ring_eq_trans _)
   as ring_eq_is_equivalence.

Add Parametric Morphism (R : ring) : (@op_a R) with signature (req) ==> (req) ==> (req) as ring_op_a_morph.
Proof. apply eq_ext. Qed.

Add Parametric Morphism (R : ring) : (@op_m R) with signature (req) ==> (req) ==> (req) as ring_op_m_morph.
Proof. apply eq_ext. Qed.

Add Parametric Morphism (R : ring) : (@iv_a R) with signature (req) ==> (req) as ring_iv_a_morph.
Proof. apply eq_ext. Qed.

Section ring_utils.

  Variable (R : ring).

  Add Ring R_is_ring : (is_ring R).

  Implicit Type (x : R).

  Fact ring_op_a_cancel x y z : x +ᵣ y ∼ᵣ x +ᵣ z → y ∼ᵣ z.
  Proof.
    intros E.
    setoid_replace y with (op_a (op_a x y) (iv_a x)) by ring.
    rewrite E; ring.
  Qed.

End ring_utils.

Section ring_homo.

  (** The notion of ring homomorphism *)

  Variables (R K : ring).

  Definition ring_homo (f : R → K) :=
      (∀ x y, x ∼ᵣ y → f x ∼ᵣ f y)
    ∧ (∀ x y, f (x +ᵣ y) ∼ᵣ f x +ᵣ f y)
    ∧ (∀ x y, f (x *ᵣ y) ∼ᵣ f x *ᵣ f y)
    ∧ f 1ᵣ ∼ᵣ 1ᵣ.

  Add Ring R_is_ring : (is_ring R).
  Add Ring K_is_ring : (is_ring K).

  Fact ring_homo_un_a f : ring_homo f → f 0ᵣ ∼ᵣ 0ᵣ.
  Proof.
    intros (H1 & H2 & H3 & H4).
    generalize (H2 un_a un_a).
    rewrite H1 with (y := un_a); try ring.
    intros E.
    apply ring_op_a_cancel with (x := f un_a).
    rewrite <- E; ring.
  Qed.

End ring_homo.

Arguments ring_homo {_ _}.

#[global] Add Parametric Morphism R K f (H : @ring_homo R K f) : f with signature (req) ==> (req) as ring_homo_morph.
Proof. apply H. Qed.

Fact ring_homo_id (R : ring) : @ring_homo R R (λ x, x).
Proof. split right; eauto. Qed.

Fact ring_homo_compose (R T K : ring) f g :
     @ring_homo R T f → @ring_homo T K g → ring_homo (λ x, g (f x)).
Proof. intros (? & ? & ? & ?) (? & ? & ? & ?); split right; eauto. Qed.

Section quotient_ring.

  Variable (R : ring)
           (rel : R → R → Prop)
           (rel_maj : req ⊆₂ rel) 
           (rel_equiv : Equivalence rel)
           (rel_ext : @ring_eq_ext R op_a op_m iv_a rel).
 
  Add Ring R_is_ring : (is_ring R).

  Definition quotient_ring : ring.
  Proof.
    exists R un_a op_a iv_a un_m op_m rel; auto.
    abstract (constructor; intros; apply rel_maj; ring).
  Defined.

End quotient_ring.

Definition ring_isomorphism {R T : ring} (f : R → T) (g : T → R) :=
    ring_homo f
  ∧ ring_homo g
  ∧ (∀p, f (g p) ∼ᵣ p)
  ∧ (∀p, g (f p) ∼ᵣ p).
