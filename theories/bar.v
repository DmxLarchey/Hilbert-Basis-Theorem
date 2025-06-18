(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Arith Lia Permutation Utf8.

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

  Lemma bar__Acc_not P l : bar P l → Acc (λ l m, extends⁻¹ l m ∧ ¬ P m) l.
  Proof.
    induction 1; constructor.
    + tauto.
    + intros ? ([]&?); auto.
  Qed.

End bar.

Arguments bar {_}.

Definition lmax := fold_right max 0.

Fact lmax_in l x : x ∈ l → x ≤ lmax l.
Proof.
  revert x; rewrite <- Forall_forall.
  induction l as [ | n l IHl ]; simpl; constructor; try lia.
  revert IHl; apply Forall_impl; lia.
Qed.

Section extends.

  Variables (X : Type).

  Definition pfx_rev (f : nat → X) :=
    fix loop n :=
      match n with
      | 0   => []
      | S n => f n :: loop n
      end.

  Fact in_pfx_rev f n x : x ∈ pfx_rev f n ↔ ∃k, k < n ∧ f k = x.
  Proof.
    induction n as [ | n IHn ]; simpl.
    + split; [ easy | ]; now intros (? & ? & _).
    + rewrite IHn; split.
      * intros [ <- | (k & ? & <-) ]; [ exists n | exists k ]; split; auto; lia.
      * intros (k & H1 & H2).
        destruct (eq_nat_dec n k) as [ <- | ]; auto; right; exists k; split; auto; lia.
  Qed.

  Implicit Type (l : list X).

  Hint Constructors extends : core.

  Fact extends_inv l m :
      extends l m
    → match m with
      | []   => False
      | _::m => l = m
      end.
  Proof. now induction 1. Qed.

  Fact hd_extends {l m} : extends l m → { x : X | m = x::l }.
  Proof.
    destruct m as [ | x m ]; intros H%extends_inv.
    + easy.
    + now exists x; subst.
  Qed.

  (* extends-sequences are sequences of n-prefixes *)
  Fact extends_pfx_rev (α : nat → list X) (l₀ : list X) :
      α 0 = l₀ 
    → (∀n, extends (α n) (α (S n)))
    → { ρ | ∀n, α n = pfx_rev ρ n ++ l₀ }.
  Proof.
    intros H1 H2.
    exists (λ n, proj1_sig (hd_extends (H2 n))).
    intros n.
    induction n as [ | n IHn ].
    + now simpl.
    + simpl.
      rewrite <- IHn.
      exact (proj2_sig (hd_extends _)).
  Qed.

End extends.

Arguments pfx_rev {X}.
Arguments extends {X}.
Arguments extends_pfx_rev {X}.

#[local] Hint Constructors extends : core.

Section bar_nc.

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

  Hypothesis dc : ∀ X (R : X → X → Prop), (∀x, ∃y, R x y) → ∀x, ∃ρ, ρ 0 = x ∧ ∀n, R (ρ n) (ρ (1+n)).

  Lemma not_bar_nil__XM_DC : ¬ bar P [] → ∃ρ, ∀n, ¬ P (pfx_rev ρ n).
  Proof.
    intros H0.
    set (Q x := ¬ bar P x).
    set (R (l m : sig Q) := extends (proj1_sig l) (proj1_sig m)).
    destruct (dc _ R) with (x := exist Q [] H0)
                      as (rho & H1 & H2).
    + intros (l & Hl).
      destruct (not_bar_2__XM _ Hl) as (x & Hx).
      exists (exist Q _ Hx); red; simpl; auto.
    + set (f := λ n, proj1_sig (rho n)).
      destruct (extends_pfx_rev f []) as (g & Hg); auto.
      * unfold f; now rewrite H1.
      * exists g.
        intros n Hn.
        apply (proj2_sig (rho n)).
        fold (f n).
        rewrite Hg, app_nil_r.
        now constructor 1.
  Qed.
  
End bar_nc.

