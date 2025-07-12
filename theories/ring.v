(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Ring ZArith Setoid Utf8.

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

(** Generic notations for rings *)

Notation "0ᵣ" := un_a.
Notation "1ᵣ" := un_m.

Notation "x ∼ᵣ y" := (req x y) (at level 70, no associativity, format "x  ∼ᵣ  y").
Notation "x +ᵣ y" := (op_a x y) (at level 31, left associativity, format "x  +ᵣ  y").
Notation "-ᵣ x" := (iv_a x) (at level 25, right associativity, format "-ᵣ x").
Notation "x −ᵣ y" := (x +ᵣ -ᵣ y) (at level 31, left associativity, format "x  −ᵣ  y").
Notation "x *ᵣ y" := (op_m x y) (at level 29, left associativity, format "x  *ᵣ  y").

(** req/∼ᵣ is a equivalence relation, defining a setoid *)

Fact ring_eq_refl (𝓡 : ring) (x : 𝓡) : x ∼ᵣ x.
Proof. apply eq_equiv. Qed.

Fact ring_eq_sym (𝓡 : ring) (x y : 𝓡) : x ∼ᵣ y → y ∼ᵣ x.
Proof. apply eq_equiv. Qed.

Fact ring_eq_trans (𝓡 : ring) (x y z : 𝓡) : x ∼ᵣ y → y ∼ᵣ z → x ∼ᵣ z.
Proof. apply eq_equiv. Qed.

Hint Resolve ring_eq_refl ring_eq_sym ring_eq_trans : core.

Add Parametric Relation (𝓡 : ring) : 𝓡 req
    reflexivity proved by (ring_eq_refl _)
    symmetry proved by (ring_eq_sym _)
    transitivity proved by (ring_eq_trans _)
  as ring_eq_is_equivalence.

(** ring operations are morphisms wrt. req/∼ᵣ *)

Add Parametric Morphism (𝓡 : ring) : (@op_a 𝓡) with signature (req) ==> (req) ==> (req) as ring_op_a_morph.
Proof. apply eq_ext. Qed.

Add Parametric Morphism (𝓡 : ring) : (@op_m 𝓡) with signature (req) ==> (req) ==> (req) as ring_op_m_morph.
Proof. apply eq_ext. Qed.

Add Parametric Morphism (𝓡 : ring) : (@iv_a 𝓡) with signature (req) ==> (req) as ring_iv_a_morph.
Proof. apply eq_ext. Qed.

(** Some obvious derived equations for rings *)

Section ring_utils.

  Variable (𝓡 : ring).

  Implicit Type (x : 𝓡).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Fact ring_sub_a_id x : x −ᵣ x ∼ᵣ 0ᵣ.
  Proof. ring. Qed.

  Fact ring_op_a_cancel x y z : x +ᵣ y ∼ᵣ x +ᵣ z → y ∼ᵣ z.
  Proof.
    intros E.
    setoid_replace y with (x +ᵣ y −ᵣ x) by ring.
    rewrite E; ring.
  Qed.

  Fact ring_op_m_un_a x : x *ᵣ 0ᵣ ∼ᵣ 0ᵣ.      Proof. ring. Qed.
  Fact ring_op_m_un_m x : x *ᵣ 1ᵣ ∼ᵣ x.       Proof. ring. Qed.
  Fact ring_op_a_un_a x : x +ᵣ 0ᵣ ∼ᵣ x.       Proof. ring. Qed.
  Fact ring_un_a_op_a x : 0ᵣ +ᵣ x ∼ᵣ x.       Proof. ring. Qed.

End ring_utils.

(** The notion of ring homorphism *)

Section ring_homo.

  Variables (𝓡 𝓚 : ring) (f : 𝓡 → 𝓚).

  Definition ring_homo :=
      (∀ x y, x ∼ᵣ y → f x ∼ᵣ f y)
    ∧ (∀ x y, f (x +ᵣ y) ∼ᵣ f x +ᵣ f y)
    ∧ (∀ x y, f (x *ᵣ y) ∼ᵣ f x *ᵣ f y)
    ∧ f 1ᵣ ∼ᵣ 1ᵣ.

  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓚_is_ring : (is_ring 𝓚).

  Hypothesis Hf : ring_homo.

  Fact ring_homo_congr x y : x ∼ᵣ y → f x ∼ᵣ f y.
  Proof. apply Hf. Qed.

  Fact ring_homo_op_a x y : f (x +ᵣ y) ∼ᵣ f x +ᵣ f y.
  Proof. apply Hf. Qed.

  Fact ring_homo_op_m x y : f (x *ᵣ y) ∼ᵣ f x *ᵣ f y.
  Proof. apply Hf. Qed.

  Fact ring_homo_un_m : f 1ᵣ ∼ᵣ 1ᵣ.
  Proof. apply Hf. Qed.

  Fact ring_homo_un_a : f 0ᵣ ∼ᵣ 0ᵣ.
  Proof.
    generalize (ring_homo_op_a un_a un_a).
    rewrite ring_homo_congr with (y := 0ᵣ); try ring.
    intros E.
    apply ring_op_a_cancel with (x := f 0ᵣ).
    rewrite <- E; ring.
  Qed.

  Fact ring_homo_iv_a x : f (-ᵣ x) ∼ᵣ -ᵣ f x.
  Proof.
    apply ring_op_a_cancel with (f x).
    rewrite <- ring_homo_op_a, ring_sub_a_id with (x := f x), <- ring_homo_un_a.
    apply ring_homo_congr; ring.
  Qed.

  Fact ring_homo_sub_a x y : f (x −ᵣ y) ∼ᵣ (f x −ᵣ f y).
  Proof. rewrite ring_homo_op_a, ring_homo_iv_a; ring. Qed.

End ring_homo.

Arguments ring_homo {_ _}.

#[global] Add Parametric Morphism 𝓡 𝓚 f (H : @ring_homo 𝓡 𝓚 f) : f with signature (req) ==> (req) as ring_homo_morph.
Proof. apply H. Qed.

Fact ring_homo_id (𝓡 : ring) : @ring_homo 𝓡 𝓡 (λ x, x).
Proof. split right; eauto. Qed.

Fact ring_homo_compose {𝓡 𝓣 𝓚 : ring} {f g} :
  @ring_homo 𝓡 𝓣 f → @ring_homo 𝓣 𝓚 g → ring_homo (λ x, g (f x)).
Proof. intros (? & ? & ? & ?) (? & ? & ? & ?); split right; eauto. Qed.

(** The notion of ring isomorphism *)

Definition ring_isomorphism {𝓡 𝓣 : ring} (f : 𝓡 → 𝓣) (g : 𝓣 → 𝓡) :=
    ring_homo f
  ∧ ring_homo g
  ∧ (∀p, f (g p) ∼ᵣ p)
  ∧ (∀p, g (f p) ∼ᵣ p).

Section quotient_ring.

  Variable (𝓡 : ring)
           (rel : 𝓡 → 𝓡 → Prop)
           (rel_maj : req ⊆₂ rel) 
           (rel_equiv : Equivalence rel)
           (rel_ext : @ring_eq_ext _ op_a op_m iv_a rel).
 
  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Definition quotient_ring : ring.
  Proof.
    exists 𝓡 un_a op_a iv_a un_m op_m rel; auto.
    abstract (constructor; intros; apply rel_maj; ring).
  Defined.

  Fact quotient_homo : @ring_homo 𝓡 quotient_ring (λ x, x).
  Proof. split right; ring || auto. Qed.

End quotient_ring.

Section product_ring.

  Variables (𝓡 𝓣 : ring).
 
  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓣_is_ring : (is_ring 𝓣).

  Let PR := (𝓡 * 𝓣)%type.
  Let pun_a : PR := (0ᵣ,0ᵣ).
  Let pop_a (a b : PR) : PR := (fst a +ᵣ fst b,snd a +ᵣ snd b).
  Let piv_a (a : PR) : PR := (-ᵣ fst a, -ᵣ snd a).
  Let pun_m : PR := (1ᵣ,1ᵣ).
  Let pop_m (a b : PR) : PR := (fst a *ᵣ fst b,snd a *ᵣ snd b).
  Let prel (a b : PR) : Prop := fst a ∼ᵣ fst b ∧ snd a ∼ᵣ snd b.

  Local Fact PR_equiv : Equivalence prel.
  Proof.
    split; unfold prel.
    + intros []; simpl; auto.
    + intros [] []; simpl; intros []; auto.
    + intros [] [] []; simpl; intros [] []; eauto.
  Qed.

  Tactic Notation "solve" "PR" :=
    repeat match goal with 
    | |- forall _ : PR, _ => intros []
    end; simpl; split; ring.

  Local Fact PR_ring : ring_theory pun_a pun_m pop_a pop_m (λ x y : PR, pop_a x (piv_a y)) piv_a prel.
  Proof. split; unfold prel; solve PR. Qed.

  Local Fact PR_ring_ext : ring_eq_ext pop_a pop_m piv_a prel.
  Proof.
    split; unfold prel.
    1,2: intros [] [] (E1 & E2) [] [] (E3 & E4); simpl in *; rewrite E1, E2, E3, E4; split; ring.
    intros [] [] (E1 & E2); simpl in *; rewrite E1, E2; split; ring.
  Qed.

  Hint Resolve PR_equiv PR_ring PR_ring_ext : core.

  Definition product_ring : ring.
  Proof.
    exists PR pun_a pop_a piv_a pun_m pop_m prel; abstract auto.
  Defined.

End product_ring.

(** The ring of relative integers *)

Definition Z_ring : ring.
Proof.
  exists Z 0%Z Z.add Z.opp 1%Z Z.mul (@eq Z).
  + apply eq_equivalence.
  + apply Zth.
  + abstract (split; intros ? ? []; auto; intros ? ? []; auto).
Defined.



