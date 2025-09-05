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

Section fg_ideal_dec_comp.

  Variables (𝓡 : ring) (b : list 𝓡).

  Lemma fg_ideal_dec_comp (l : list 𝓡) :
      (∀x, { idl ⌞l⌟ x } + { ¬ idl ⌞l⌟ x })
    → { x | idl ⌞b⌟ x ∧ ¬ idl ⌞l⌟ x } + { idl ⌞b⌟ ⊆₁ idl ⌞l⌟ }.
  Proof.
    intros Hl.
    destruct list_choice_comp
      with (P := idl ⌞l⌟) (Q := λ x, ¬ idl ⌞l⌟ x) (l := b)
      as [ (x & []) | ]; eauto.
    right.
    now apply idl_closed.
  Qed.

End fg_ideal_dec_comp.

Definition sincl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ~ Q ⊆₁ P.

Fact strict_incl_sincl X : @witnessed_strict_incl X ⊆₂ sincl.
Proof. intros ? ? (? & ? & []); split; auto. Qed.

(** "ML-Noetherian" and "RS-Noetherian" terminology come from Perdry 2004

    "strongly discrete ring" is a terminology of Schuster&Yengui 2025
    which is called "a ring with detachable ideals" in Perdry 2004 *)

Definition ML_noetherian 𝓡 := well_founded (λ P Q : sig (@fg_ideal 𝓡), sincl (proj1_sig Q) (proj1_sig P)).

Definition RS_noetherian (𝓡 : ring) :=
  ∀ (ρ : nat → 𝓡 → Prop),
    (∀n, ρ n ⊆₁ ρ (S n))
  → (∀n, fg_ideal (ρ n))
  → ∃n, ρ (S n) ⊆₁ ρ n.

Theorem noetherian__RS_noetherian_alt 𝓡 : 
    noetherian 𝓡
  → ∀ρ : nat → 𝓡, ∃n, idl ⌞pfx_rev ρ n⌟ (ρ n).
Proof.
  intros H rho.
  destruct bar_sequences
    with (1 := H) (ρ := rho)
    as (n & Hn).
  apply PA_split in Hn as (l & x & r & H1 & H2).
  symmetry in H1.
  apply pfx_rev_app_inv in H1 as (a & b & H3 & H4 & H5).
  apply pfx_rev_cons_inv in H5 as (i & ? & ? & ?).
  now exists i; subst.
Qed.

Definition strongly_discrete (𝓡 : ring) := ∀ l (x : 𝓡), idl ⌞l⌟ x ∨ ¬ idl ⌞l⌟ x.

Section zero_test.

  Variable (𝓡 : ring).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Fact zero_test__discrete : (∀ x : 𝓡, x ∼ᵣ 0ᵣ ∨ ¬ x ∼ᵣ 0ᵣ) → ∀ x y : 𝓡, x ∼ᵣ y ∨ ¬ x ∼ᵣ y.
  Proof.
    intros HR x y.
    destruct (HR (x −ᵣ y)) as [ H | H ]; [ left | right ].
    + rewrite <- (ring_op_a_un_a _ y), <- H; ring.
    + contradict H; rewrite H; ring.
  Qed.

End zero_test.

Fact strongly_discrete__discrete 𝓡 : strongly_discrete 𝓡 → ∀ x y : 𝓡, x ∼ᵣ y ∨ ¬ x ∼ᵣ y.
Proof.
  intros HR; apply zero_test__discrete.
  intros x.
  destruct (HR [] x) as [ ?%idl_iff_lc__list%lc_inv | H ]; [ left | right ]; auto.   
  contradict H; rewrite H; constructor 3.
Qed.

Section strongly_discrete_poly.

  Variables (𝓡 : ring)
            (H𝓡 : strongly_discrete 𝓡).

  Theorem stronly_discrete_poly : strongly_discrete (poly_ring 𝓡).
  Proof.
    intros l.
  Admitted.

End strongly_discrete_poly.

Section strongly_discrete_ML_noetherian.

  Variables (𝓡 : ring)
            (H𝓡 : strongly_discrete 𝓡).

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
  
  Implicit Type (l : list 𝓡).
  
  Fact strongly_discrete__PA_dec l : PA l ∨ ¬ PA l.
  Proof.
    induction l as [ | x l Hl ].
    + right; red; apply PA_nil_inv.
    + rewrite PA_cons_inv.
      generalize (H𝓡 l x); tauto.
  Qed.

  Hint Resolve strongly_discrete__PA_dec : core.

  Local Lemma ML_noetherian__noetherian :
      well_founded (λ P Q : sig (@fg_ideal 𝓡), sincl (proj1_sig Q) (proj1_sig P))
    → noetherian 𝓡.
  Proof.
    intros HR.
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

  Theorem strongly_discrete__ML_noetherian_iff : noetherian 𝓡 ↔ ML_noetherian 𝓡.
  Proof. split; auto. Qed.

End strongly_discrete_ML_noetherian.

Check strongly_discrete__ML_noetherian_iff.

Section find_basis.

  Variables (𝓡 : ring)
            (H𝓡 : noetherian 𝓡)
            (𝓘 : 𝓡 → Prop)
            (H𝓘1 : ideal 𝓘)
            (H𝓘2 : ∀l, (∃x, 𝓘 x ∧ ¬ idl ⌞l⌟ x) ∨ 𝓘 ⊆₁ idl ⌞l⌟).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)

  Lemma complete_basis l : ⌞l⌟ ⊆₁ 𝓘 → ∃b, ⌞l⌟ ⊆₁ ⌞b⌟ ∧ 𝓘 ≡₁ idl ⌞b⌟.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_fg_idl_strict_incl H𝓡)).
    intros Hl.
    destruct (H𝓘2 l) as [ (x & H1 & H2) | H ].
    + destruct (IH (x::l)) as (b & []).
      * split.
        - apply idl_mono; eauto.
        - exists x; simpl; eauto.
      * intros ? [ <- | ]; auto.
      * exists b; split; eauto.
    + exists l; split right; auto.
      apply idl_smallest; auto.
  Qed.

  Theorem find_basis : ∃b, 𝓘 ≡₁ idl ⌞b⌟.
  Proof.
    destruct (complete_basis []) as (b & []).
    + intros _ [].
    + now exists b.
  Qed.

End find_basis.

Section strongly_discrete__RS_noetherian.

  Variables (𝓡 : ring)
            (𝓡_strongly_discrete : strongly_discrete 𝓡)
            (𝓡_noetherian : ML_noetherian 𝓡).
 
  Hint Resolve incl_tl incl_refl incl_tran : core.

  Variables (ρ : nat → 𝓡 → Prop)
            (ρ_incr : forall n, ρ n ⊆₁ ρ (S n))
            (ρ_fingen : forall n, fg_ideal (ρ n)).

  Let R n m := ρ m ⊂w ρ n.

  Local Fact R_wf : well_founded R.
  Proof.
    generalize 𝓡_noetherian.
    wf rel morph (fun P n => proj1_sig P = ρ n); eauto.
    + intros n; now exists (exist _ _ (ρ_fingen n)).
    + intros P Q n m -> ->; apply strict_incl_sincl.
  Qed.

  Local Lemma find_pause_from n : ∃m, n ≤ m ∧ ρ (S m) ⊆₁ ρ m.
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type R_wf).
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

End strongly_discrete__RS_noetherian.

Theorem strongly_discrete__RS_noetherian (𝓡 : ring) :
    strongly_discrete 𝓡
  → ML_noetherian 𝓡
  → RS_noetherian 𝓡.
Proof.
  intros ? ? rho ? ?.  
  destruct (find_pause_from 𝓡) with (n := 0) (ρ := rho) as (m & []); eauto.
Qed.

Check strongly_discrete__RS_noetherian.

Section find_pause.

  Variables (𝓡 : ring)
            (𝓡_strongly_discrete : strongly_discrete 𝓡)
            (𝓡_noetherian : noetherian 𝓡).
 
  Hint Resolve incl_tl incl_refl incl_tran : core.

  Variable ρ : nat → 𝓡.
  
  Hint Resolve noetherian__ML_noetherian : core.

  Theorem find_pause : ∃n, idl ⌞pfx_rev ρ n⌟ (ρ n).
  Proof. 
    destruct strongly_discrete__RS_noetherian
      with (ρ := fun n => idl ⌞pfx_rev ρ n⌟)
      as (n & Hn); auto.
    + intros ? ?; apply idl_mono; simpl; auto.
    + intro; apply idl__fg_ideal.
    + exists n; apply Hn.
      constructor; simpl; auto.
  Qed.

End find_pause.

Section compute_basis.

  Variables (𝓡 : ring)
            (H𝓡 : noetherian 𝓡)
            (𝓘 : 𝓡 → Prop)
            (𝓘_ideal : ideal 𝓘)
            (𝓘_discrete : ∀l, {x | 𝓘 x ∧ ¬ idl ⌞l⌟ x} + (𝓘 ⊆₁ idl ⌞l⌟)).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)
  Lemma grow_basis l : ⌞l⌟ ⊆₁ 𝓘 → {b | ⌞l⌟ ⊆₁ ⌞b⌟ ∧ 𝓘 ≡₁ idl ⌞b⌟}.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_fg_idl_strict_incl H𝓡)).
    intros Hl.
    destruct (𝓘_discrete l) as [ (x & H1 & H2) | H ].
    + destruct (IH (x::l)) as (b & []).
      * split.
        - apply idl_mono; eauto.
        - exists x; simpl; eauto.
      * intros ? [ <- | ]; auto.
      * exists b; split; eauto.
    + exists l; split right; auto.
      apply idl_smallest; auto.
  Qed.

  Theorem compute_basis : {b | 𝓘 ≡₁ idl ⌞b⌟}.
  Proof.
    destruct (grow_basis []) as (b & []).
    + intros _ [].
    + now exists b.
  Qed.

End compute_basis.

Section compute_pause.

  Variables (𝓡 : ring)
            (𝓡_noetherian : noetherian 𝓡)
            (𝓡_discrete_strong : ∀ l (x : 𝓡), { idl ⌞l⌟ x } + { ¬ idl ⌞l⌟ x }).
 
  Hint Resolve incl_tl incl_refl incl_tran : core.

  Variable ρ : nat → 𝓡.

  Let R n m := idl ⌞pfx_rev ρ m⌟ ⊂w idl ⌞pfx_rev ρ n⌟.

  Local Fact R_wf' : well_founded R.
  Proof.
    generalize (noetherian__wf_idl_strict_incl 𝓡_noetherian).
    wf rel morph (fun P n => P = idl ⌞pfx_rev ρ n⌟); eauto.
    intros P Q n m -> ->.
    unfold R.
    intros (H1 & x & H2 & H3).
    split.
    + now apply idl_mono.
    + exists x; split.
      * now constructor 1.
      * contradict H3.
        now apply idl_idem.
  Qed.

  Local Lemma compute_pause_from n : { m | n ≤ m ∧ idl ⌞pfx_rev ρ m⌟ (ρ m) }.
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type R_wf').
    destruct (𝓡_discrete_strong (pfx_rev ρ n) (ρ n)) as [ H | H ]; eauto.
    destruct (IHn (S n)) as (m & H1 & H2).
    + split.
      * apply idl_mono; simpl; eauto.
      * exists (ρ n); split; simpl; auto.
    + exists m; split; auto; lia.
  Qed.

  Theorem compute_pause : { n | idl ⌞pfx_rev ρ n⌟ (ρ n) }.
  Proof. destruct (compute_pause_from 0) as (m & []); eauto. Qed.

End compute_pause.

Section incl_witnessed_dec__XM.

  Hypothesis xm : ∀P, P ∨ ¬ P.

  Fact incl_witnessed_dec__XM A (P Q : A → Prop) : (∃a, P a ∧ ¬ Q a) ∨ P ⊆₁ Q.
  Proof. 
    destruct xm with (P := ∃a, P a ∧ ¬ Q a); auto.
    right.
    intros a Ha.
    destruct xm with (P := Q a); auto.
    destruct H; eauto.
  Qed.

End incl_witnessed_dec__XM.



  

