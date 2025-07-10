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

(** Unused below, weaker that strictly_incl *)
Local Definition sincl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ~ Q ⊆₁ P.

#[local] Hint Constructors extends : core.

Definition strict_incl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ∃x, Q x ∧ ¬ P x.

#[local] Notation "P ⊂₁ Q" := (strict_incl P Q) (at level 70, format "P  ⊂₁  Q").
#[local] Notation LD := linearly_dependent.

Local Lemma Acc_strict_incl_rev_upclosed_right (R : ring) l :
    Acc (λ l m : list R, extends⁻¹ l m ∧ ¬ LD m) l
  → ¬ LD l
  → ∀P, ⌞l⌟ ⊆₁ P → Acc (λ P Q, Q ⊂₁ P ∧ ring_ideal Q) P.
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

(** If R is (constructivelly) Noetherian then strict reverse inclusion
    is (constructivelly) well-founded on ideals of R, 
    Hence any strictly increasing sequence of ideals of R is terminating. *)

Theorem noetherian__wf_strict_incl_rev {R} :
    noetherian R
  → well_founded (λ P Q : R → Prop, Q ⊂₁ P ∧ ring_ideal Q).
Proof.
  intros H P.
  apply Acc_strict_incl_rev_upclosed_right with (l := []).
  + now apply bar__Acc_not.
  + now intros ?%Good_inv.
  + simpl; tauto.
Qed.

Theorem noetherian__wf_strict_incl_ideal {R} :
    noetherian R
  → well_founded (λ P Q : sig (@ring_ideal R), proj1_sig Q ⊂₁ proj1_sig P).
Proof.
  intros H%noetherian__wf_strict_incl_rev; revert H.
  wf rel morph (fun x y => x = proj1_sig y).
  + intros []; simpl; eauto.
  + intros ? ? [] []; simpl; intros; subst; auto.
Qed.

Theorem noetherian__wf_Idl_strict_incl {R} :
    noetherian R
  → well_founded (λ P Q : R → Prop, Idl Q ⊂₁ Idl P).
Proof.
  intros H%noetherian__wf_strict_incl_ideal; revert H.
  wf rel morph (fun P Q => proj1_sig P = Idl Q).
  + intros P; now exists (exist _ _ (Idl_ring_ideal _ P)).
  + intros ? ? ? ? -> ->; auto.
Qed.

Theorem noetherian__wf_fin_Idl_strict_incl {R} :
    noetherian R
  → well_founded (λ l m : list R, Idl ⌞m⌟ ⊂₁ Idl ⌞l⌟).
Proof.
  intros H%noetherian__wf_Idl_strict_incl; revert H.
  wf rel morph (fun P l => P = ⌞l⌟).
  + intros l; now exists ⌞l⌟.
  + intros ? ? ? ? -> ->; auto.
Qed.

Definition fingen_ideal {R : ring} I := ∃ l : list R, I ≡₁ Idl ⌞l⌟.

Section fingen_ideal_wdec.

  Variables (R : ring) (I : R → Prop) (HI : fingen_ideal I).

  Lemma fingen_ideal_wdec (l : list R) :
      (∀x, Idl ⌞l⌟ x ∨ ¬ Idl ⌞l⌟ x)
    → (∃x, I x ∧ ¬ Idl ⌞l⌟ x) ∨ I ⊆₁ Idl ⌞l⌟.
  Proof.
    intros Hl.
    destruct HI as (b & Hb).
    destruct list_choice
      with (P := Idl ⌞l⌟) (Q := λ x, ¬ Idl ⌞l⌟ x) (l := b)
      as [ | (x & []) ]; auto.
    + right.
      intros x.
      rewrite Hb.
      apply Idl_smallest; auto.
      apply Idl_ring_ideal.
    + left; exists x; rewrite Hb; split; auto. 
  Qed.

End fingen_ideal_wdec.

Section find_basis.

  Variables (R : ring)
            (HR : noetherian R)
            (I : R → Prop)
            (HI1 : ring_ideal I)
            (HI2 : ∀l, (∃x, I x ∧ ¬ Idl ⌞l⌟ x) ∨ I ⊆₁ Idl ⌞l⌟).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)

  Lemma complete_basis l : ⌞l⌟ ⊆₁ I → ∃b, ⌞l⌟ ⊆₁ ⌞b⌟ ∧ I ≡₁ Idl ⌞b⌟.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_fin_Idl_strict_incl HR)).
    intros Hl.
    destruct (HI2 l) as [ (x & H1 & H2) | H ].
    + destruct (IH (x::l)) as (b & []).
      * split.
        - apply Idl_mono; eauto.
        - exists x; simpl; eauto.
      * intros ? [ <- | ]; auto.
      * exists b; split; eauto.
    + exists l; split; auto.
      intros x; split; auto.
      revert x; apply Idl_smallest; auto.
  Qed.

  Theorem find_basis : ∃b, I ≡₁ Idl ⌞b⌟.
  Proof.
    destruct (complete_basis []) as (b & []).
    + intros _ [].
    + now exists b.
  Qed.

End find_basis.

Section incl_witnessed_dec__XM.

  Hypothesis xm : ∀A, A ∨ ¬ A.

  Fact incl_witnessed_dec__XM X (P Q : X → Prop) : (∃x, P x ∧ ¬ Q x) ∨ P ⊆₁ Q.
  Proof. 
    destruct xm with (A := ∃x, P x ∧ ¬ Q x); auto.
    right.
    intros x Hp.
    destruct xm with (A := Q x); auto.
    destruct H; eauto.
  Qed.

End incl_witnessed_dec__XM.



  

