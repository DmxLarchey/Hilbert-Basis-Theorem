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

Require Import utils bar ring ideal poly noetherian noetherian_wf noetherian_alt.

#[local] Hint Resolve
           incl_refl incl_nil_l incl_cons incl_tl 
           in_eq in_cons
         : core.

#[local] Hint Constructors extends : core.

#[local] Notation "P '⊂w' Q" := (witnessed_strict_incl P Q) (at level 70, format "P  ⊂w  Q").
#[local] Notation PA := pauses.

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

Section find_pause.

  Variables (𝓡 : ring)
            (𝓡_strongly_discrete : strongly_discrete 𝓡)
            (𝓡_noetherian : noetherian 𝓡).
 
  Hint Resolve incl_tl incl_refl incl_tran : core.

  Variable ρ : nat → 𝓡.

  Hint Resolve noetherian__ML_noetherian : core.

  Theorem find_pause : ∃n, idl ⌞pfx_rev ρ n⌟ (ρ n).
  Proof. 
    destruct strongly_discrete__ML_RS_noetherian
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



  

