(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Arith Lia Wellfounded Relations Setoid Utf8.

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

Lemma Acc_strict_incl_rev_upclosed_right (R : ring) l :
    Acc (λ l m : list R, extends⁻¹ l m ∧ ¬ linearly_dependent m) l
  → ¬ linearly_dependent l
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

Theorem noetherian__wf_strict_incl_rev R :
    noetherian R
  → well_founded (λ P Q : R → Prop, Q ⊂₁ P ∧ ring_ideal Q).
Proof.
  intros H P.
  apply Acc_strict_incl_rev_upclosed_right with (l := []).
  + now apply bar__Acc_not.
  + now intros ?%Good_inv.
  + simpl; tauto.
Qed.

Definition Idl_strict_incl (R : ring) (l m : list R) := Idl ⌞l⌟ ⊂₁ Idl ⌞m⌟.

Theorem noetherian__wf_Idl_strict_incl {R} : noetherian R → well_founded (Idl_strict_incl R)⁻¹.
Proof.
  intros H%noetherian__wf_strict_incl_rev; revert H.
  wf rel morph (fun P l => P = Idl ⌞l⌟).
  + intro; eauto.
  + intros ? ? l m -> ->; split; auto.
    apply Idl_ring_ideal.
Qed.

Section find_basis.

  Variables (R : ring)
            (HR : noetherian R)
            (P : R → Prop)
            (HP1 : ring_ideal P)
            (HP2 : ∀l, (∃x, P x ∧ ¬ Idl ⌞l⌟ x) ∨ P ⊆₁ Idl ⌞l⌟).

  Hint Resolve incl_tl incl_refl incl_tran : core.

  (* Any list contained in P can be expanded (as a list) into a basis of P *)

  Lemma complete_basis l : ⌞l⌟ ⊆₁ P → ∃b, ⌞l⌟ ⊆₁ ⌞b⌟ ∧ P ≡₁ Idl ⌞b⌟.
  Proof.
    induction l as [ l IH ]
      using (well_founded_induction_type (noetherian__wf_Idl_strict_incl HR)).
    intros Hl.
    destruct (HP2 l) as [ (x & H1 & H2) | H ].
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

  Theorem find_basis : ∃b, P ≡₁ Idl ⌞b⌟.
  Proof.
    destruct (complete_basis []) as (b & []).
    + intros _ [].
    + now exists b.
  Qed.

End find_basis.

Check find_basis.

Section finitely_generated_ideals.

  Variables (X : Type) (R : ring) (HR : noetherian R)
            (P : R → Prop) (HP : ∃b, P ≡₁ Idl ⌞b⌟).

  (* Membership ie Idl ⌞l⌟ x is not necessarily decidable ... 
     Is it decidable for polynomials provided it is decidable
     for base elements? 
     For instance assume b1 , ... , bk is polynomial.
     Is p a linear combination of b1, ...., bk ?
       1) deg p < max (deg bi)
       2) dep p >= max (dep bi)

     In case 2, we could try to obtain the dom coef
     of p as a linear combination of the dom coef of the bi
     If not possible, the p cannot be a linear combination
     of the bi. 
     If possible, remove the leading coef of p and start over
     with the remaining polynomial of lesser degree.

     In case 1, we cannot simply ignore the polynomials
     bi of higher degrees. Unless they all have different
     degrees. Is this possible? 
     
     What about Groebner bases ? *)

  Fact finitely_gen_ideal_choice l : (∃x, P x ∧ ¬ Idl ⌞l⌟ x) ∨ P ⊆₁ Idl ⌞l⌟.
  Proof.
    destruct HP as (b & Hb).
  Admitted.

End finitely_generated_ideals.



  

