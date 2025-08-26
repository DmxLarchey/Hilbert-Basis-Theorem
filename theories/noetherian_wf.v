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

(* This is witnessed strict inclusion and it is 
   stronger than P ⊆₁ Q ∧ ¬ Q ⊆₁ P (unless one can
   actually find a witness when ¬ Q ⊆₁ P holds) *)

Definition witnessed_strict_incl {X} (P Q : X → Prop) := P ⊆₁ Q ∧ ∃x, Q x ∧ ¬ P x.

#[local] Notation "P ⊂𞁤 Q" := (witnessed_strict_incl P Q) (at level 70, format "P  ⊂𞁤  Q").
#[local] Notation PA := pauses.

Section noetherian_wf.

  Variable (𝓡 : ring).

  Implicit Type (l m k : list 𝓡).

  Let T (P Q : 𝓡 → Prop) := Q ⊂𞁤 P ∧ ring_ideal Q.

  Local Lemma bar_PA__Acc l : bar PA l → ¬ PA l → ∀P, ⌞l⌟ ⊆₁ P → Acc T P.
  Proof.
    induction 1 as [ l Hl | l _ IHl ].
    + now intros [].
    + intros Gl P Hl; constructor.
      intros Q ((HPQ & x & Qx & Px) & HP).
      apply IHl with x; eauto.
      * contradict Gl.
        apply PA_cons_inv in Gl as [ H | ]; auto.
        destruct Px.
        revert H; now apply idl_smallest.
      * intros ? [ <- | ]; eauto.
  Qed.

  Hypothesis 𝓡_noeth : noetherian 𝓡.

  (** If 𝓡 is (Bar) Noetherian then witnessed strict 
      reverse inclusion is well-founded on the 
      ideals of 𝓡. Hence any strictly increasing 
      sequence of ideals of 𝓡 is terminating. *)

  Theorem noetherian__wf_strict_incl_rev :
    well_founded T.
  Proof.
    intro.
    apply bar_PA__Acc with (l := []); auto.
    + now intros ?%PA_nil_inv.
    + simpl; tauto.
  Qed.

  Corollary noetherian__wf_strict_incl_ideal :
    well_founded (λ P Q : sig (@ring_ideal 𝓡), proj1_sig Q ⊂𞁤 proj1_sig P).
  Proof.
    generalize noetherian__wf_strict_incl_rev.
    unfold T.
    wf rel morph (λ x y, x = proj1_sig y).
    + intros []; simpl; eauto.
    + intros ? ? [] []; simpl; intros; subst; auto.
  Qed.

  Corollary noetherian__wf_idl_strict_incl :
    well_founded (λ P Q : 𝓡 → Prop, idl Q ⊂𞁤 idl P).
  Proof.
    generalize noetherian__wf_strict_incl_ideal.
    wf rel morph (λ P Q, proj1_sig P = idl Q).
    + intros P; now exists (exist _ _ (idl_ring_ideal _ P)).
    + intros ? ? ? ? -> ->; auto.
  Qed.

  Corollary noetherian__wf_fin_idl_strict_incl :
    well_founded (λ l m : list 𝓡, idl ⌞m⌟ ⊂𞁤 idl ⌞l⌟).
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