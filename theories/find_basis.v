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

Require Import utils bar ring ideal poly noetherian.

#[local] Hint Resolve
           incl_refl incl_nil_l incl_cons incl_tl 
           in_eq in_cons
         : core.

#[local] Hint Constructors extends : core.

(* This is witnessed strict inclusion and it is 
   stronger than P ⊆₁ Q ∧ ¬ Q ⊆₁ P (unless one can
   actually find a witness when ¬ Q ⊆₁ P holds) *)

Definition strict_incl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ∃x, Q x ∧ ¬ P x.

#[local] Notation "P ⊂₁ Q" := (strict_incl P Q) (at level 70, format "P  ⊂₁  Q").
#[local] Notation PA := pauses.

Section noetherian_wf.

  Variable (𝓡 : ring).

  Implicit Type (l m k : list 𝓡).

  Local Lemma Acc_extends__strict_incl_rev k :
      Acc (λ l m, extends⁻¹ l m ∧ ¬ PA m) k
    → ¬ PA k
    → ∀P, ⌞k⌟ ⊆₁ P → Acc (λ P Q, Q ⊂₁ P ∧ ring_ideal Q) P.
  Proof.
    induction 1 as [ l _ IHl ].
    intros Gl P Hl; constructor.
    intros Q ((HPQ & x & Qx & Px) & HP).
    apply IHl with (x::l); eauto.
    + contradict Gl.
      apply PA_cons_inv in Gl as [ H | H ]; auto.
      destruct Px.
      revert H; now apply idl_smallest.
    + intros ? [ <- | ]; eauto.
  Qed.
  
  Hypothesis 𝓡_noeth : noetherian 𝓡.

  Local Fact Acc_extends_nil : Acc (λ l m, extends⁻¹ l m ∧ ¬ PA m) [].
  Proof. apply bar__Acc_not; auto. Qed.

  Hint Resolve Acc_extends_nil : core.

  (** If 𝓡 is (constructivelly) Noetherian then witnessed strict 
      reverse inclusion is (constructivelly) well-founded on the 
      ideals of 𝓡. Hence any strictly increasing sequence of 
      ideals of 𝓡 is terminating. *)

  Theorem noetherian__wf_strict_incl_rev :
    well_founded (λ P Q : 𝓡 → Prop, Q ⊂₁ P ∧ ring_ideal Q).
  Proof.
    intro.
    apply Acc_extends__strict_incl_rev with (k := []); auto.
    + now intros ?%PA_nil_inv.
    + simpl; tauto.
  Qed.

  Corollary noetherian__wf_strict_incl_ideal :
    well_founded (λ P Q : sig (@ring_ideal 𝓡), proj1_sig Q ⊂₁ proj1_sig P).
  Proof.
    generalize noetherian__wf_strict_incl_rev.
    wf rel morph (λ x y, x = proj1_sig y).
    + intros []; simpl; eauto.
    + intros ? ? [] []; simpl; intros; subst; auto.
  Qed.

  Corollary noetherian__wf_idl_strict_incl :
    well_founded (λ P Q : 𝓡 → Prop, idl Q ⊂₁ idl P).
  Proof.
    generalize noetherian__wf_strict_incl_ideal.
    wf rel morph (λ P Q, proj1_sig P = idl Q).
    + intros P; now exists (exist _ _ (idl_ring_ideal _ P)).
    + intros ? ? ? ? -> ->; auto.
  Qed.

  Corollary noetherian__wf_fin_idl_strict_incl :
    well_founded (λ l m : list 𝓡, idl ⌞m⌟ ⊂₁ idl ⌞l⌟).
  Proof.
    generalize noetherian__wf_idl_strict_incl.
    wf rel morph (λ P l, P = ⌞l⌟).
    + intros l; now exists ⌞l⌟.
    + intros ? ? ? ? -> ->; auto.
  Qed.

End noetherian_wf.

Arguments noetherian__wf_strict_incl_rev {_}.
Arguments noetherian__wf_strict_incl_ideal {_}.
Arguments noetherian__wf_idl_strict_incl {_}.
Arguments noetherian__wf_fin_idl_strict_incl {_}.

Definition fingen_ideal {𝓡 : ring} 𝓘 := ∃ l : list 𝓡, 𝓘 ≡₁ idl ⌞l⌟.

Fact fingen_ideal__ring_ideal 𝓡 : @fingen_ideal 𝓡 ⊆₁ ring_ideal.
Proof.
  intros P (m & Hm); split right.
  1,3,4: intros ? ?.
  all: rewrite !Hm; apply idl_ring_ideal.
Qed.

Fact idl__fingen_ideal 𝓡 l : @fingen_ideal 𝓡 (idl ⌞l⌟).
Proof. now exists l. Qed.

Section fingen_ideal_dec.

  Variables (𝓡 : ring) (𝓘 : 𝓡 → Prop) (H𝓘 : fingen_ideal 𝓘).

  Lemma fingen_ideal_dec (l : list 𝓡) :
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

End fingen_ideal_dec.

Section fingen_ideal_dec_comp.

  Variables (𝓡 : ring) (b : list 𝓡).

  Lemma fingen_ideal_dec_comp (l : list 𝓡) :
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

End fingen_ideal_dec_comp.

Definition sincl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ~ Q ⊆₁ P.

Fact strict_incl_sincl X : @strict_incl X ⊆₂ sincl.
Proof. intros ? ? (? & ? & []); split; auto. Qed.

(** "ML-Noetherian" and "RS-Noetherian" terminology come from Perdry 2004

    "strongly discrete ring" is a terminology of Schuster&Yengui 2025
    which is called "a ring with detachable ideals" in Perdry 2004 *)

Definition ML_noetherian 𝓡 := well_founded (λ P Q : sig (@fingen_ideal 𝓡), sincl (proj1_sig Q) (proj1_sig P)).

Definition RS_noetherian (𝓡 : ring) :=
  ∀ (ρ : nat → 𝓡 → Prop),
    (∀n, ρ n ⊆₁ ρ (S n))
  → (∀n, fingen_ideal (ρ n))
  → ∃n, ρ (S n) ⊆₁ ρ n.

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
      fingen_ideal P
    → fingen_ideal Q
    → sincl P Q → P ⊂₁ Q.
  Proof.
    intros (l & Hl) HQ (H1 & H2); split; auto.
    destruct fingen_ideal_dec with (𝓘 := Q) (l := l)
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
      now exists (exist _ P (fingen_ideal__ring_ideal _ _ HP)).
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
      well_founded (λ P Q : sig (@fingen_ideal 𝓡), sincl (proj1_sig Q) (proj1_sig P))
    → noetherian 𝓡.
  Proof.
    intros HR.
    apply Acc_not__bar; auto.
    generalize (@nil 𝓡).
    revert HR.
    wf rel morph (λ P l, proj1_sig P = idl ⌞l⌟).
    + intros l; now exists (exist _ (idl ⌞l⌟) (idl__fingen_ideal _ _)).
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
            (H𝓘1 : ring_ideal 𝓘)
            (H𝓘2 : ∀l, (∃x, 𝓘 x ∧ ¬ idl ⌞l⌟ x) ∨ 𝓘 ⊆₁ idl ⌞l⌟).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)

  Lemma complete_basis l : ⌞l⌟ ⊆₁ 𝓘 → ∃b, ⌞l⌟ ⊆₁ ⌞b⌟ ∧ 𝓘 ≡₁ idl ⌞b⌟.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_fin_idl_strict_incl H𝓡)).
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
            (ρ_fingen : forall n, fingen_ideal (ρ n)).

  Let R n m := ρ m ⊂₁ ρ n.

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
    destruct fingen_ideal_dec with (l := ln) (𝓘 := ρ (S n))
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
    + intro; apply idl__fingen_ideal.
    + exists n; apply Hn.
      constructor; simpl; auto.
  Qed.

End find_pause.

Section compute_basis.

  Variables (𝓡 : ring)
            (H𝓡 : noetherian 𝓡)
            (𝓘 : 𝓡 → Prop)
            (𝓘_ideal : ring_ideal 𝓘)
            (𝓘_discrete : ∀l, {x | 𝓘 x ∧ ¬ idl ⌞l⌟ x} + (𝓘 ⊆₁ idl ⌞l⌟)).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)
  Lemma grow_basis l : ⌞l⌟ ⊆₁ 𝓘 → {b | ⌞l⌟ ⊆₁ ⌞b⌟ ∧ 𝓘 ≡₁ idl ⌞b⌟}.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_fin_idl_strict_incl H𝓡)).
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

  Let R n m := idl ⌞pfx_rev ρ m⌟ ⊂₁ idl ⌞pfx_rev ρ n⌟.

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



  

