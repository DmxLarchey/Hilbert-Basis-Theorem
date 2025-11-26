(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Wellfounded Relations Setoid Utf8.

Import ListNotations.

Require Import utils bar ring ideal poly noetherian noetherian_wf.

#[local] Hint Resolve
           incl_refl incl_nil_l incl_cons incl_tl 
           in_eq in_cons
         : core.

#[local] Hint Constructors extends : core.

#[local] Notation "P '⊂w' Q" := (witnessed_strict_incl P Q) (at level 70, format "P  ⊂w  Q").
#[local] Notation PA := pauses.

Definition sincl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ¬ Q ⊆₁ P.

Fact strict_incl_sincl X : @witnessed_strict_incl X ⊆₂ sincl.
Proof. intros ? ? (? & ? & []); split; auto. Qed.

(** "ML-Noetherian" and "RS-Noetherian" terminology come from Perdry 2004

    "strongly discrete ring" is a terminology of Schuster&Yengui 2025
    which is called "a ring with detachable ideals" in Perdry 2004 *)

Definition RS_noetherian (𝓡 : ring) :=
  ∀ (ρ : nat → 𝓡 → Prop),
    (∀n, ρ n ⊆₁ ρ (S n))
  → (∀n, fg_ideal (ρ n))
  → ∃n, ρ (S n) ⊆₁ ρ n.

Definition ML_noetherian 𝓡 := well_founded (λ P Q : sig (@fg_ideal 𝓡), sincl (proj1_sig Q) (proj1_sig P)).

Section fg_ideal_dec.

  Variables (𝓡 : ring) (𝓘 : 𝓡 → Prop) (H𝓘 : fg_ideal 𝓘).

  Lemma fg_ideal_dec (l : list 𝓡) :
      (∀x, idl ⌞l⌟ x ∨ ¬ idl ⌞l⌟ x)
    → (∃x, 𝓘 x ∧ ¬ idl ⌞l⌟ x) ∨ 𝓘 ⊆₁ idl ⌞l⌟.
  Proof.
    intros Hl.
    destruct H𝓘 as (b & Hb).
    destruct list_choice
      with (P := idl ⌞l⌟) (Q := λ x, ¬ idl ⌞l⌟ x) (l := b)
      as [ (x & []) | ]; auto.
    + left; exists x; rewrite Hb; split; auto.
    + right.
      intro; rewrite Hb.
      now apply idl_closed.
  Qed.

End fg_ideal_dec.

Definition strongly_discrete (𝓡 : ring) := ∀ l (x : 𝓡), idl ⌞l⌟ x ∨ ¬ idl ⌞l⌟ x.

Section strongly_discrete__inclusion__pauses.

  Variables (𝓡 : ring)
            (𝓡_strongly_discrete : strongly_discrete 𝓡).

  Implicit Type (l : list 𝓡).

  (** In a strongly discrete ring, strict inclusion between finitely
      generated ideals entails witnessed strict inclusion *)
  Proposition strictly_discrete_sincl_fingen_ideal (P Q : 𝓡 → Prop) : 
      fg_ideal P
    → fg_ideal Q
    → sincl P Q → P ⊂w Q.
  Proof.
    intros (l & Hl) HQ (H1 & H2); split; auto.
    destruct fg_ideal_dec with (𝓘 := Q) (l := l)
      as [ (x & H3 & H4) | ]; auto.
    + exists x; now rewrite Hl.
    + destruct H2; intro; rewrite Hl; auto.
  Qed.

   Fact strongly_discrete__PA_dec l : PA l ∨ ¬ PA l.
  Proof.
    induction l as [ | x l Hl ].
    + right; red; apply PA_nil_inv.
    + rewrite PA_cons_inv.
      generalize (𝓡_strongly_discrete l x); tauto.
  Qed.
  
  Variables (𝓡_noetherian : ML_noetherian 𝓡).
 
  Hint Resolve incl_tl incl_refl incl_tran : core.

  Variables (ρ : nat → 𝓡 → Prop)
            (ρ_incr : forall n, ρ n ⊆₁ ρ (S n))
            (ρ_fingen : forall n, fg_ideal (ρ n)).

  Let T n m := ρ m ⊂w ρ n.

  Local Fact T_wf : well_founded T.
  Proof.
    generalize 𝓡_noetherian.
    wf rel morph (fun P n => proj1_sig P = ρ n); eauto.
    + intros n; now exists (exist _ _ (ρ_fingen n)).
    + intros P Q n m -> ->; apply strict_incl_sincl.
  Qed.

  Local Lemma find_pause_from n : ∃m, n ≤ m ∧ ρ (S m) ⊆₁ ρ m.
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type T_wf).
    destruct (ρ_fingen n) as (ln & Hn).
    destruct fg_ideal_dec with (l := ln) (𝓘 := ρ (S n))
      as [ (x & H1 & H2)| H ]; auto.
    + destruct (IHn (S n)) as (m & G1 & G2).
      * split; auto; exists x; split; auto.
        now rewrite Hn.
      * exists m; split; auto; lia.
    + exists n; split; auto.
      now intros x ?%H%Hn.
  Qed.

End strongly_discrete__inclusion__pauses.

Section Bar_noetherian__ML_noetherian__strongly_discrete.

  Variables (𝓡 : ring)
            (H𝓡 : strongly_discrete 𝓡).

  Implicit Type (l : list 𝓡).

  (** In a strongly discrete ring, Noetherian entails ML-Noetherian *)
  Local Lemma noetherian__ML_noetherian : noetherian 𝓡 → ML_noetherian 𝓡.
  Proof.
    intros H%noetherian__wf_strict_incl_ideal; revert H.
    wf rel morph (λ P Q, proj1_sig P = proj1_sig Q).
    + intros (P & HP).
      now exists (exist _ P (fg_ideal__ideal HP)).
    + intros (P & HP) (Q & HQ) (P' & HP') (Q' & HQ'); simpl.
      intros <- <-; now apply strictly_discrete_sincl_fingen_ideal.
  Qed.

  Hint Resolve strongly_discrete__PA_dec : core.

  Local Lemma ML_noetherian__noetherian :
      ML_noetherian 𝓡 → noetherian 𝓡.
  Proof.
    intros HR.
    (* Since PA is decidable, bar PA is equivalent to 
       Acc (λ l m, extends m l ∧ ¬ PA l) *)
    apply Acc_not__bar; auto.
    generalize (@nil 𝓡).
    revert HR.
    wf rel morph (λ P l, proj1_sig P = idl ⌞l⌟).
    + intros l; now exists (exist _ (idl ⌞l⌟) (idl__fg_ideal _ _)).
    + intros (P & HP) (Q & HQ) m l; simpl.
      intros -> -> ([x] & ?).
      split.
      * apply idl_mono; eauto.
      * contradict H.
        constructor 1; apply H; constructor; auto.
  Qed.

  Hint Resolve noetherian__ML_noetherian ML_noetherian__noetherian : core.

  Theorem strongly_discrete__Bar_ML_noetherian_iff : noetherian 𝓡 ↔ ML_noetherian 𝓡.
  Proof. split; auto. Qed.

End Bar_noetherian__ML_noetherian__strongly_discrete.

Check strongly_discrete__Bar_ML_noetherian_iff.

Theorem strongly_discrete__ML_RS_noetherian (𝓡 : ring) :
    strongly_discrete 𝓡
  → ML_noetherian 𝓡
  → RS_noetherian 𝓡.
Proof.
  intros ? ? rho ? ?.  
  destruct (find_pause_from 𝓡) with (n := 0) (ρ := rho) as (m & []); eauto.
Qed.

Check strongly_discrete__ML_RS_noetherian.