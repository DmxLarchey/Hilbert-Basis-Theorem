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

  Variables (X : Type).

  Implicit Type (P : list X → Prop).

  Inductive bar P l : Prop :=
    | bar_stop : P l → bar P l
    | bar_next : (∀x, bar P (x::l)) → bar P l.

  Hint Constructors bar : core.

  Fact bar_mono P Q : P ⊆₁ Q → bar P ⊆₁ bar Q.
  Proof. induction 2; eauto. Qed.

  Local Fact bar_app_rec P m r : bar P m → ∀l, m = l++r → bar (λ x, P (x++r)) l.
  Proof.
    induction 1 as [ | v _ IHv ]; intros ? ->; eauto.
    constructor 2; intro x; now apply IHv with x.
  Qed.

  Fact bar_app_iff P l r : bar P (l++r) ↔ bar (λ x, P (x++r)) l.
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

  Notation monotone P := (∀ x l, P l → P (x::l)).

  Lemma bar_monotone P : monotone P → monotone (bar P).
  Proof. induction 2; eauto. Qed.

  Hint Resolve bar_monotone : core.

  Lemma bar_app_left P : monotone P → ∀ l r, bar P r → bar P (l++r).
  Proof. intros ? l ? ?; induction l; simpl; eauto. Qed.

  (** This result is not part of Kruskal-AlmostFull and could be added there !! *)
  Lemma bar_app_middle P :
   (∀ l m r, P (l++r) → P (l++m++r))
  → ∀ l m r, bar P (l++r) → bar P (l++m++r).
  Proof. intros ? ? ? ? H%bar_app_iff; apply bar_app_iff; revert H; apply bar_mono; eauto. Qed.

  Fact bar_permutation P :
      (∀ l m, l ≈ₚ m → P l → P m)
    → (∀ l m, l ≈ₚ m → bar P l → bar P m).
  Proof. intros H l m H1 H2; revert H2 m H1; induction 1; eauto. Qed.
  
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

Section bar_nc.

  (** This section is about bar in "non-constructive" settings *)

  Variables (X : Type) (P : list X → Prop).

  Local Fact not_bar_1 l : ¬ bar P l → ¬ P l.
  Proof. intros H ?; apply H; now constructor 1. Qed.

  Hypothesis xm : ∀A, A ∨ ¬ A.

  Local Fact not_bar_2__XM l : ¬ bar P l → ∃x, ¬ bar P (x::l).
  Proof.
    intros H.
    destruct (xm (∃x, ¬ bar P (x::l))) as [ | C ]; auto.
    destruct H; constructor 2.
    intros x.
    destruct (xm (bar P (x::l))) as [ | D ]; auto.
    destruct C; eauto.
  Qed.

  Hypothesis dc : ∀ A (R : A → A → Prop), (∀a, ∃b, R a b) → ∀a, ∃ρ, ρ 0 = a ∧ ∀n, R (ρ n) (ρ (1+n)).

  (** This is a form of dependent choice over Σ-types *)
  Fact dc_sigma A (Q : A → Prop) R : 
      (∀a, Q a → ∃b, Q b ∧ R a b)
     → ∀a, Q a → ∃ρ, ρ 0 = a ∧ (∀n, Q (ρ n) ∧ R (ρ n) (ρ (S n))).
  Proof.
    intros HQ a Ha.
    set (B := sig Q).
    set (T (x y : B) := R (proj1_sig x) (proj1_sig y)).
    destruct (dc _ T) with (a := exist _ a Ha) as (f & H1 & H2).
    + intros (c & Hc).
      destruct (HQ _ Hc) as (b & Hb & ?).
      exists (exist _ b Hb); auto.
    + exists (λ n, proj1_sig (f n)); split.
      * now rewrite H1.
      * intro; split.
        - apply proj2_sig.
        - apply H2.
  Qed.

  Hint Constructors extends bar : core.

  Lemma not_bar_nil__XM_DC : ¬ bar P [] → ∃ρ, ∀n, ¬ P (pfx_rev ρ n).
  Proof.
    intros H0.
    destruct dc_sigma
      with (Q := λ x, ¬ bar P x)
           (R := @extends X)
           (a := @nil X)
      as (f & H1 & H2); auto.
    + intros l (x & Hx)%not_bar_2__XM.
      exists (x::l); auto.
    + destruct (extends_pfx_rev f) as (g & Hg); auto.
      * intro; apply H2.
      * exists g.
        intros n Hn.
        apply (H2 n); rewrite Hg; auto.
  Qed.

  (** Reminder of the bar theorem (under XM + DC of course), see also
           https://github.com/DmxLarchey/Constructive-Konig *)
  Theorem bar_theorem__XM_DC : bar P [] ↔ ∀ρ, ∃n, P (pfx_rev ρ n).
  Proof.
    split.
    + intros H rho.
      apply bar_sequences with (ρ := rho) in H.
      destruct H as (n & Hn).
      exists n; now rewrite app_nil_r in Hn.
    + intros H.
      destruct (xm (bar P [])) as [ | C ]; auto.
      apply not_bar_nil__XM_DC in C as (rho & Hrho).
      now destruct (H rho) as (n & Hn%Hrho).
  Qed.

End bar_nc.

