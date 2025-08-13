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

Require Import utils bar ring ideal noetherian.

#[local] Hint Resolve
           incl_refl incl_nil_l incl_cons incl_tl 
           in_eq in_cons
         : core.

#[local] Hint Constructors extends : core.

Definition strict_incl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ∃x, Q x ∧ ¬ P x.

#[local] Notation "P ⊂₁ Q" := (strict_incl P Q) (at level 70, format "P  ⊂₁  Q").
#[local] Notation LD := linearly_dependent.

Section noetherian_wf.

  Variable (𝓡 : ring).

  Implicit Type (l m k : list 𝓡).

  Local Lemma Acc_strict_incl_rev_upclosed_right k :
      Acc (λ l m, extends⁻¹ l m ∧ ¬ LD m) k
    → ¬ LD k
    → ∀P, ⌞k⌟ ⊆₁ P → Acc (λ P Q, Q ⊂₁ P ∧ ring_ideal Q) P.
  Proof.
    induction 1 as [ l _ IHl ].
    intros Gl P Hl; constructor.
    intros Q ((HPQ & x & Qx & Px) & HP).
    apply IHl with (x::l); eauto.
    + contradict Gl.
      apply Good_inv in Gl as [ H | H ]; auto.
      destruct Px.
      revert H; now apply Idl_smallest.
    + intros ? [ <- | ]; eauto.
  Qed.
  
  Hypothesis 𝓡_noeth : noetherian 𝓡.

  (** If 𝓡 is (constructivelly) Noetherian then strict reverse inclusion
      is (constructivelly) well-founded on ideals of R, 
      Hence any strictly increasing sequence of ideals of R is terminating. *)

  Theorem noetherian__wf_strict_incl_rev :
    well_founded (λ P Q : 𝓡 → Prop, Q ⊂₁ P ∧ ring_ideal Q).
  Proof.
    intros P.
    apply Acc_strict_incl_rev_upclosed_right with (k := []).
    + now apply bar__Acc_not.
    + now intros ?%Good_inv.
    + simpl; tauto.
  Qed.

  Corollary noetherian__wf_strict_incl_ideal :
    well_founded (λ P Q : sig (@ring_ideal 𝓡), proj1_sig Q ⊂₁ proj1_sig P).
  Proof.
    generalize noetherian__wf_strict_incl_rev.
    wf rel morph (fun x y => x = proj1_sig y).
    + intros []; simpl; eauto.
    + intros ? ? [] []; simpl; intros; subst; auto.
  Qed.

  Corollary noetherian__wf_Idl_strict_incl :
    well_founded (λ P Q : 𝓡 → Prop, Idl Q ⊂₁ Idl P).
  Proof.
    generalize noetherian__wf_strict_incl_ideal.
    wf rel morph (fun P Q => proj1_sig P = Idl Q).
    + intros P; now exists (exist _ _ (Idl_ring_ideal _ P)).
    + intros ? ? ? ? -> ->; auto.
  Qed.

  Corollary noetherian__wf_fin_Idl_strict_incl :
    well_founded (λ l m : list 𝓡, Idl ⌞m⌟ ⊂₁ Idl ⌞l⌟).
  Proof.
    generalize noetherian__wf_Idl_strict_incl.
    wf rel morph (λ P l, P = ⌞l⌟).
    + intros l; now exists ⌞l⌟.
    + intros ? ? ? ? -> ->; auto.
  Qed.

End noetherian_wf.

Arguments noetherian__wf_strict_incl_rev {_}.
Arguments noetherian__wf_strict_incl_ideal {_}.
Arguments noetherian__wf_Idl_strict_incl {_}.
Arguments noetherian__wf_fin_Idl_strict_incl {_}.

Definition fingen_ideal {𝓡 : ring} 𝓘 := ∃ l : list 𝓡, 𝓘 ≡₁ Idl ⌞l⌟.

Fact fingen_ideal__ring_ideal 𝓡 : @fingen_ideal 𝓡 ⊆₁ ring_ideal.
Proof.
  intros P (m & Hm); split right.
  1,3,4: intros ? ?.
  all: rewrite !Hm; apply Idl_ring_ideal.
Qed.

Fact Idl__fingen_ideal 𝓡 l : @fingen_ideal 𝓡 (Idl ⌞l⌟).
Proof. now exists l. Qed.

Section fingen_ideal_wdec.

  Variables (𝓡 : ring) (𝓘 : 𝓡 → Prop) (H𝓘 : fingen_ideal 𝓘).

  Lemma fingen_ideal_wdec (l : list 𝓡) :
      (∀x, Idl ⌞l⌟ x ∨ ¬ Idl ⌞l⌟ x)
    → (∃x, 𝓘 x ∧ ¬ Idl ⌞l⌟ x) ∨ 𝓘 ⊆₁ Idl ⌞l⌟.
  Proof.
    intros Hl.
    destruct H𝓘 as (b & Hb).
    destruct list_choice
      with (P := Idl ⌞l⌟) (Q := λ x, ¬ Idl ⌞l⌟ x) (l := b)
      as [ (x & []) | ]; auto.
    + left; exists x; rewrite Hb; split; auto.
    + right.
      intro; rewrite Hb.
      now apply Idl_closed.
  Qed.

End fingen_ideal_wdec.

Section fingen_ideal_dec.

  Variables (𝓡 : ring) (b : list 𝓡).

  Lemma fingen_ideal_dec (l : list 𝓡) :
      (∀x, { Idl ⌞l⌟ x } + { ¬ Idl ⌞l⌟ x })
    → { x | Idl ⌞b⌟ x ∧ ¬ Idl ⌞l⌟ x } + { Idl ⌞b⌟ ⊆₁ Idl ⌞l⌟ }.
  Proof.
    intros Hl.
    destruct list_choice_strong
      with (P := Idl ⌞l⌟) (Q := λ x, ¬ Idl ⌞l⌟ x) (l := b)
      as [ (x & []) | ]; eauto.
    right.
    now apply Idl_closed.
  Qed.

End fingen_ideal_dec.

Definition sincl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ~ Q ⊆₁ P.

Fact strict_incl_sincl X : @strict_incl X ⊆₂ sincl.
Proof. intros ? ? (? & ? & []); split; auto. Qed.

Definition ML_noetherian 𝓡 := well_founded (λ P Q : sig (@fingen_ideal 𝓡), sincl (proj1_sig Q) (proj1_sig P)).

Section strongly_discrete_ML_noetherian.

  (** "strongly discrete ring" is a terminology of Schuster&Yengui 2025
      which is called "a ring with detachable ideals" in Perdry 2004 *)

  Variables (𝓡 : ring)
            (strongly_discrete : ∀ l (x : 𝓡), Idl ⌞l⌟ x ∨ ¬ Idl ⌞l⌟ x).

  (** In a strongly discrete ring, strict inclusion between finitely
      generated ideals entails witnessed strict inclusion *)
  Proposition strictly_discrete_sincl_fingen_ideal (P Q : 𝓡 → Prop) : 
      fingen_ideal P
    → fingen_ideal Q
    → sincl P Q → P ⊂₁ Q.
  Proof.
    intros (l & Hl) HQ (H1 & H2); split; auto.
    destruct fingen_ideal_wdec with (𝓘 := Q) (l := l)
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
  
  Fact strongly_discrete__LD_wdec l : LD l ∨ ¬ LD l.
  Proof.
    induction l as [ | x l Hl ].
    + right; red; apply LD_nil_inv.
    + rewrite LD_cons_inv.
      generalize (strongly_discrete l x); tauto.
  Qed.

  Hint Resolve strongly_discrete__LD_wdec : core.

  Local Lemma ML_noetherian__noetherian :
      well_founded (λ P Q : sig (@fingen_ideal 𝓡), sincl (proj1_sig Q) (proj1_sig P))
    → noetherian 𝓡.
  Proof.
    intros HR.
    apply Acc_not__bar; auto.
    generalize (@nil 𝓡).
    revert HR.
    wf rel morph (λ P l, proj1_sig P = Idl ⌞l⌟).
    + intros l; now exists (exist _ (Idl ⌞l⌟) (Idl__fingen_ideal _ _)).
    + intros (P & HP) (Q & HQ) m l; simpl.
      intros -> -> ([x] & ?).
      split.
      * apply Idl_mono; eauto.
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
            (H𝓘2 : ∀l, (∃x, 𝓘 x ∧ ¬ Idl ⌞l⌟ x) ∨ 𝓘 ⊆₁ Idl ⌞l⌟).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)

  Lemma complete_basis l : ⌞l⌟ ⊆₁ 𝓘 → ∃b, ⌞l⌟ ⊆₁ ⌞b⌟ ∧ 𝓘 ≡₁ Idl ⌞b⌟.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_fin_Idl_strict_incl H𝓡)).
    intros Hl.
    destruct (H𝓘2 l) as [ (x & H1 & H2) | H ].
    + destruct (IH (x::l)) as (b & []).
      * split.
        - apply Idl_mono; eauto.
        - exists x; simpl; eauto.
      * intros ? [ <- | ]; auto.
      * exists b; split; eauto.
    + exists l; split right; auto.
      apply Idl_smallest; auto.
  Qed.

  Theorem find_basis : ∃b, 𝓘 ≡₁ Idl ⌞b⌟.
  Proof.
    destruct (complete_basis []) as (b & []).
    + intros _ [].
    + now exists b.
  Qed.

End find_basis.

Section compute_basis.

  Variables (𝓡 : ring)
            (H𝓡 : noetherian 𝓡)
            (𝓘 : 𝓡 → Prop)
            (𝓘_ideal : ring_ideal 𝓘)
            (𝓘_discrete : ∀l, {x | 𝓘 x ∧ ¬ Idl ⌞l⌟ x} + (𝓘 ⊆₁ Idl ⌞l⌟)).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)
  Lemma grow_basis l : ⌞l⌟ ⊆₁ 𝓘 → {b | ⌞l⌟ ⊆₁ ⌞b⌟ ∧ 𝓘 ≡₁ Idl ⌞b⌟}.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_fin_Idl_strict_incl H𝓡)).
    intros Hl.
    destruct (𝓘_discrete l) as [ (x & H1 & H2) | H ].
    + destruct (IH (x::l)) as (b & []).
      * split.
        - apply Idl_mono; eauto.
        - exists x; simpl; eauto.
      * intros ? [ <- | ]; auto.
      * exists b; split; eauto.
    + exists l; split right; auto.
      apply Idl_smallest; auto.
  Qed.

  Theorem compute_basis : {b | 𝓘 ≡₁ Idl ⌞b⌟}.
  Proof.
    destruct (grow_basis []) as (b & []).
    + intros _ [].
    + now exists b.
  Qed.

End compute_basis.

Section compute_pause.

  Variables (𝓡 : ring)
            (𝓡_noetherian : noetherian 𝓡)
            (𝓡_discrete_strong : ∀ l (x : 𝓡), { Idl ⌞l⌟ x } + { ¬ Idl ⌞l⌟ x }).
 
  Hint Resolve incl_tl incl_refl incl_tran : core.

  Variable ρ : nat → 𝓡.

  Let R n m := Idl ⌞pfx_rev ρ m⌟ ⊂₁ Idl ⌞pfx_rev ρ n⌟.

  Local Fact R_wf : well_founded R.
  Proof.
    generalize (noetherian__wf_Idl_strict_incl 𝓡_noetherian).
    wf rel morph (fun P n => P = Idl ⌞pfx_rev ρ n⌟); eauto.
    intros P Q n m -> ->.
    unfold R.
    intros (H1 & x & H2 & H3).
    split.
    + now apply Idl_mono.
    + exists x; split.
      * now constructor 1.
      * contradict H3.
        now apply Idl_idem.
  Qed.

  Local Lemma compute_pause_from n : { m | n ≤ m ∧ Idl ⌞pfx_rev ρ m⌟ (ρ m) }.
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type R_wf).
    destruct (𝓡_discrete_strong (pfx_rev ρ n) (ρ n)) as [ H | H ]; eauto.
    destruct (IHn (S n)) as (m & H1 & H2).
    + split.
      * apply Idl_mono; simpl; eauto.
      * exists (ρ n); split; simpl; auto.
    + exists m; split; auto; lia.
  Qed.

  Theorem compute_pause : { n | Idl ⌞pfx_rev ρ n⌟ (ρ n) }.
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



  

