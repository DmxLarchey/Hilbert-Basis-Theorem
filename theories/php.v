(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Permutation Relations Utf8.

Require Import utils.

Import ListNotations.

Set Implicit Arguments.

#[local] Infix "⊆" := incl (at level 70, no associativity).

#[local] Hint Resolve
           incl_nil_l incl_cons
           in_eq in_cons incl_tl
           incl_refl incl_tran in_or_app : core.

Section finite_pigeon_hole.

  Hint Constructors Permutation : core.
  
  Hint Resolve Permutation_sym Permutation_middle Permutation_app
               Permutation_sym Permutation_in : core.

  Variable (X : Type).

  Implicit Types (l m : list X) (x : X).

  Notation lhd l := (∃ x m, l ≈ₚ x::x::m).

  Fact list_has_dup_eq_duplicates k : lhd k ↔ ∃ x l m r, k = l++x::m++x::r.
  Proof.
    split.
    + intros (x & k' & E).
      destruct (@in_split _ x k) as (a & b & ->); eauto.
      apply Permutation_app_inv with (l3 := [_]) in E.
      assert (x ∈ a++b) as [ (u & v & ->)%in_split | (u & v & ->)%in_split ]%in_app_iff; eauto.
      exists x, u, v, b; now rewrite <- app_assoc.
    + intros (x & a & b & c & ->).
      exists x, (a++b++c).
      apply Permutation_sym, Permutation_cons_app.
      rewrite (app_assoc _ _ (_::_)).
      apply Permutation_cons_app.
      rewrite app_assoc; auto.
  Qed.

  Hint Resolve Permutation_pigeonhole : core.

  (** list based PHP *)

  Theorem list_php l m : ⌊l⌋ < ⌊m⌋ → m ⊆ l → ∃ x a b c, m = a++x::b++x::c.
  Proof. rewrite <- list_has_dup_eq_duplicates; eauto. Qed.

End finite_pigeon_hole.

Section fin_rel_php.

  Variables (X Y : Type)
            (R : X → Y → Prop)
            (l : list X) (m : list Y)
            (HR : ∀x, x ∈ l → ∃y, y ∈ m ∧ R x y).

  (* l has a R-image included in m *)
  Local Fact R_image_l : ∃l', l' ⊆ m ∧ Forall2 R l l'.
  Proof.
    destruct reif_Forall2 with (1 := HR) as (Rl & HRl).
    exists Rl; split.
    + clear HR.
      rewrite Forall2_conj in HRl.
      apply proj1, Forall2_right_Forall, proj1 in HRl.
      rewrite Forall_forall in HRl; auto.
    + revert HRl; apply Forall2_impl; tauto.
  Qed.

  Hypothesis (Hlm : ⌊m⌋ < ⌊l⌋).

  (** The finite relational PHP *)

  Theorem fin_rel_php : ∃ a x b y c v, l = a++x::b++y::c ∧ v ∈ m ∧ R x v ∧ R y v.
  Proof.
    destruct R_image_l as (l' & H1 & H2).
    destruct list_php with (2 := H1) as (v & x & y & z & ->).
    + apply Forall2_length in H2; lia.
    + apply Forall2_special_inv_r in H2 as (a & x1 & b & x2 & c & ? & ? & ? & ? & ? & ->).
      exists a, x1, b, x2, c, v; repeat split; auto.
  Qed.

End fin_rel_php.

(** If E is a partial equivalence relation, l is a
    list contained in the list m (upto E), and m is 
    shorter than l, then l contains a duplicate upto E *)

Theorem php_upto X (E : X → X → Prop) (l m : list X) :
    symmetric _ E                             (* E is a PER *)
  → transitive _ E                            (* PER = Partial Equivalence Relation *)
  → (∀x, x ∈ l → ∃y, y ∈ m ∧ E x y)           (* l contained in m (up to E) *)
  → ⌊m⌋ < ⌊l⌋                                 (* m is shorter than l *)
  → ∃ a x b y c, l = a++x::b++y::c ∧ E x y    (* l contains a duplicate (up to E) *)
  .
Proof.
  intros HR1 HR2 H1 H2; red in HR2.
  destruct fin_rel_php with (R := E) (2 := H2)
    as (a & x & b & y & c & z & ? & ? & []); auto.
  exists a, x, b, y, c; eauto.
Qed.
