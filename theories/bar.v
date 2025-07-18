(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Permutation Utf8.

Require Import utils.

Import ListNotations.

Section bar.

  (** Code partly imported/inspired from Kruskal-AlmostFull in https://dmxlarchey.github.io/Coq-Kruskal/ *)

  Variables (A : Type).

  Implicit Type (R : list A → list A → Prop) (P : list A → Prop) (m : list A).

  Inductive bar P l : Prop :=
    | bar_stop : P l → bar P l
    | bar_next : (∀a, bar P (a::l)) → bar P l.

  Hint Constructors bar : core.

  Fact bar_mono P Q : P ⊆₁ Q → bar P ⊆₁ bar Q.
  Proof. induction 2; eauto. Qed.

  Local Fact bar_app_rec P m r : bar P m → ∀l, m = l++r → bar (λ p, P (p++r)) l.
  Proof.
    induction 1 as [ | v _ IHv ]; intros ? ->; eauto.
    constructor 2; intro x; now apply IHv with x.
  Qed.

  Fact bar_app_iff P l r : bar P (l++r) ↔ bar (λ p, P (p++r)) l.
  Proof.
    split.
    + intro; now apply bar_app_rec with (2 := eq_refl).
    + induction 1; eauto.
  Qed.

  Fact bar_above_length n P : (∀l, n ≤ ⌊l⌋ → P l) → ∀l, bar P l.
  Proof.
    intros Hn.
    assert (∀p, ∀l, n ≤ p+⌊l⌋ → bar P l) as H.
    + induction p as [ | p IHp ]; intros l Hl.
      * constructor 1; eauto.
      * constructor 2; intro; apply IHp; simpl; lia.
    + intros l; apply (H n); lia.
  Qed.

  (** This results subsumes bar_app_middle, bar_permutation below *) 
  Lemma bar_rel_closed R P :
      (∀ a l m, R l m → R (a::l) (a::m))
    → (∀ l m, R l m → P l → P m)
    →  ∀ l m, R l m → bar P l → bar P m.
  Proof. intros ? ? l m H1 H2; revert H2 m H1; induction 1; eauto. Qed.
  
  Inductive list_insert m : list A → list A → Prop :=
    | list_insert_intro l r : list_insert m (l++r) (l++m++r).

  Hint Constructors list_insert : core.

  (** This result is not part of Kruskal-AlmostFull and could be added there !! *)
  Lemma bar_app_middle P m :
   (∀ l r, P (l++r) → P (l++m++r))
  → ∀ l r, bar P (l++r) → bar P (l++m++r).
  Proof.
    intros ? ? ?.
    apply bar_rel_closed with (R := list_insert m); eauto; induction 1; eauto.
    constructor 1 with (l := _::_).
  Qed.
  
  Fact bar_permutation P :
      (∀ l m, l ≈ₚ m → P l → P m)
    → (∀ l m, l ≈ₚ m → bar P l → bar P m).
  Proof. apply bar_rel_closed; now constructor. Qed.

  Notation monotone P := (∀ a l, P l → P (a::l)).

  Fact bar_monotone P : monotone P → monotone (bar P).
  Proof. induction 2; eauto. Qed.

  Hint Resolve bar_monotone : core.

  Fact bar_app_left P : monotone P → ∀ l r, bar P r → bar P (l++r).
  Proof. intros ? l ? ?; induction l; simpl; eauto. Qed.

  Fact bar_sequences P l : bar P l → ∀ρ, ∃n, P (pfx_rev ρ n ++ l).
  Proof.
    induction 1 as [ l Hl | l _ IHl ].
    + exists 0; auto.
    + intros f.
      destruct (IHl (f 0) (λ n, f (1+n))) as (n & Hn).
      exists (S n); now rewrite pfx_rev_S, <- app_assoc.
  Qed.

  Lemma bar__Acc_not P l : bar P l → Acc (λ l m, extends⁻¹ l m ∧ ¬ P m) l.
  Proof.
    induction 1; constructor.
    + tauto.
    + intros ? ([]&?); auto.
  Qed.

End bar.

Arguments bar {_}.

Section bar_relmap.

  Variables (A B : Type) (f : A → B → Prop)
            (R : list A → Prop)
            (T : list B → Prop)
            (Hf : ∀b, ∃a, f a b)                       (** f is surjective *)
            (HRT : ∀ l m, Forall2 f l m → R l → T m)   (** f is a morphism form R to T *)
            .

  Theorem bar_relmap l m : Forall2 f l m → bar R l → bar T m.
  Proof.
    intros H1 H2; revert H2 m H1 T HRT.
    induction 1 as [ l Hl | l Hl IHl ]; intros m H1 T HRT.
    * constructor 1; revert Hl; apply HRT; auto.
    * constructor 2; intros b.
      destruct (Hf b) as (a & ?).
      apply (IHl a); auto.
  Qed.

End bar_relmap.

Section bar_double_ind.

  Variables (X Y : Type) (P : list X → Prop) (Q : list Y → Prop) 
            (K : list X → list Y → Prop)
            (HPK : ∀ l m, P l → K l m) 
            (HQK : ∀ l m, Q m → K l m)
            (HPQK : ∀ l m, (∀x, K (x::l) m) → (∀y, K l (y::m)) → K l m).

  Theorem bar_double_ind l m : bar P l → bar Q m → K l m.
  Proof.
    induction 1 in m |- *; auto.
    induction 1 as [ | ? ?%bar_next ]; auto.
  Qed.

End bar_double_ind.

Section bar_nc.

  (** This section is about bar in "non-constructive" settings *)

  Variables (A : Type) (Q : list A → Prop).

  Local Fact not_bar_1 l : ¬ bar Q l → ¬ Q l.
  Proof. intros H ?; apply H; now constructor 1. Qed.

  Hypothesis xm : ∀P, P ∨ ¬ P.

  Local Fact not_bar_2__XM l : ¬ bar Q l → ∃a, ¬ bar Q (a::l).
  Proof.
    intros H.
    destruct (xm (∃a, ¬ bar Q (a::l))) as [ | C ]; auto.
    destruct H; constructor 2.
    intros a.
    destruct (xm (bar Q (a::l))) as [ | D ]; auto.
    destruct C; eauto.
  Qed.

  Hypothesis dc : ∀ B (R : B → B → Prop), (∀a, ∃b, R a b) → ∀a, ∃ρ, ρ 0 = a ∧ ∀n, R (ρ n) (ρ (1+n)).

  (** This is a form of dependent choice over Σ-types *)
  Fact dc_sigma B (P : B → Prop) R : 
      (∀a, P a → ∃b, P b ∧ R a b)
     → ∀a, P a → ∃ρ, ρ 0 = a ∧ (∀n, P (ρ n) ∧ R (ρ n) (ρ (S n))).
  Proof.
    intros HP a Ha.
    set (C := sig P).
    set (T (x y : C) := R (proj1_sig x) (proj1_sig y)).
    destruct (dc _ T) with (a := exist _ a Ha) as (f & H1 & H2).
    + intros (c & Hc).
      destruct (HP _ Hc) as (b & Hb & ?).
      exists (exist _ b Hb); auto.
    + exists (λ n, proj1_sig (f n)); split.
      * now rewrite H1.
      * intro; split.
        - apply proj2_sig.
        - apply H2.
  Qed.

  Hint Constructors extends bar : core.

  Lemma not_bar_nil__XM_DC : ¬ bar Q [] → ∃ρ, ∀n, ¬ Q (pfx_rev ρ n).
  Proof.
    intros H0.
    destruct dc_sigma
      with (P := λ x, ¬ bar Q x)
           (R := @extends A)
           (a := @nil A)
      as (f & H1 & H2); auto.
    + intros l (a & ?)%not_bar_2__XM.
      exists (a::l); auto.
    + destruct (extends_pfx_rev f) as (g & Hg); auto.
      * intro; apply H2.
      * exists g.
        intros n Hn.
        apply (H2 n); rewrite Hg; auto.
  Qed.

  (** Reminder of the bar theorem (under XM + DC of course), see also
           https://github.com/DmxLarchey/Constructive-Konig *)
  Theorem bar_theorem__XM_DC : bar Q [] ↔ ∀ρ, ∃n, Q (pfx_rev ρ n).
  Proof.
    split.
    + intros H rho.
      apply bar_sequences with (ρ := rho) in H.
      destruct H as (n & Hn).
      exists n; now rewrite app_nil_r in Hn.
    + intros H.
      destruct (xm (bar Q [])) as [ | C ]; auto.
      apply not_bar_nil__XM_DC in C as (rho & Hrho).
      now destruct (H rho) as (n & Hn%Hrho).
  Qed.

End bar_nc.

