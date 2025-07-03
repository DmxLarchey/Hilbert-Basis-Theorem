(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Ring ZArith Lia Lia Setoid Utf8.

Import ListNotations.

Require Import utils bar ring ideal php.

#[local] Hint Resolve
           incl_refl incl_nil_l incl_cons incl_tl 
           in_eq in_cons
         : core.

Section Good_and_bar.

  (** The generalization of good : rel₂ X → rel₁ (list X) 
                         as Good : rel (list X) X → rel₁ (list X)
      subsumes both the notion of good (finite) sequence for binary relation
                and the notion of Good increasing sequence of finitely generated ideals of a ring *)  

  Variables (X : Type).

  Implicit Types (P Q : list X → X → Prop).

  Inductive Good P : list X → Prop :=
    | Good_stop x l : P l x    → Good P (x::l)
    | Good_skip x l : Good P l → Good P (x::l).

  Hint Constructors Good : core.

  Fact Good_inv P l :
      Good P l
    → match l with
      | []   => False
      | x::l => P l x ∨ Good P l
      end.
  Proof. destruct 1; eauto. Qed.

  Fact Good_mono P Q : P ⊆₂ Q → Good P ⊆₁ Good Q.
  Proof. induction 2; eauto. Qed.

  Fact Good_app_left P l r : Good P r → Good P (l++r).
  Proof. intro; induction l; simpl; eauto. Qed.

  Hint Resolve Good_app_left : core.

  (* Another characterization (in FOL) *)
  Lemma Good_split P m : Good P m ↔ ∃ l x r, m = l++x::r ∧ P r x.
  Proof.
    split.
    + induction 1 as [ x m H | x m _ (l & y & r & -> & H) ].
      * now exists [], x, m.
      * now exists (x::l), y, r.
    + intros (l & x & r & -> & H); auto.
  Qed.

  Hint Resolve bar_monotone : core.

  Fact bar_Good_app_left P l m : bar (Good P) m → bar (Good P) (l++m).
  Proof. apply bar_app_left; eauto. Qed.
  
  Section Good_app_middle.

    Variables (P : list X → X → Prop) (m : list X)
              (P_app_middle : ∀ l r x, P (l++r) x → P (l++m++r) x).

    Fact Good_app_middle l r : Good P (l++r) → Good P (l++m++r).
    Proof. induction l; simpl; eauto; intros []%Good_inv; auto. Qed.

    Hint Resolve Good_app_middle bar_app_middle : core.

    Fact bar_Good_app_middle l r : bar (Good P) (l++r) → bar (Good P) (l++m++r).
    Proof. eauto. Qed.

  End Good_app_middle.

End Good_and_bar.

#[local] Hint Constructors Good : core.

Arguments Good {_}.

(** This gives a definition of L(inear) D(ependence) of m
    at some point x in the sequence m = l++[x]++r, 
    Idl ⌞r⌟ does not increase, ie Idl ⌞x::r⌟ ⊆ Idl ⌞r⌟

    see LD_split below
    
    Notice that (λ m, Idl ⌞m⌟) ignores the order of the list m *)

Definition linearly_dependent {R : ring} := Good (λ m : list R, Idl ⌞m⌟).

#[local] Notation LD := linearly_dependent.

(** bar LD l can be read as l is bound to become linearly dependent 
    after finitely many steps, however it is extended by adding 
    elements (on the lhs) 
    
    Hence bar LD [] means that whichever way you build a list,
    it is bound to become LD after finitely many steps. *) 
    
Definition noetherian (R : ring) := bar (@LD R) [].

(** Noetherianess is invariant under surjective homomorphisms *)
Lemma noetherian_surj_homo (R T : ring) :
    (∃ f : R → T, ring_homo f ∧ ∀x, ∃y, f y ∼ᵣ x)
  → noetherian R → noetherian T.
Proof.
  intros (f & H1 & H2).
  apply bar_relmap with (f := λ x y, f x ∼ᵣ y); eauto.
  intros l m Hlm H; revert H m Hlm.
  induction 1 as [ x l Hx | x l _ IH ].
  + intros ? (y & m & E & ? & ->)%Forall2_cons_inv_l.
    constructor 1; rewrite <- E.
    revert Hx.
    clear y E H2.
    generalize H1; intros (H2 & H3 & H4 & H5).
    induction 1 as [ x Hx | x y <-%H2 _ IH | | | ]. 
    * apply Forall2_in_inv_l with (1 := H) in Hx as (? & ? & ->); auto.
    * trivial.
    * rewrite ring_homo_un_a; auto.
    * rewrite H3, ring_homo_iv_a; auto.
    * rewrite H4; auto.
  + intros ? (? & ? & ? & ? & ->)%Forall2_cons_inv_l.
    constructor 2; now apply IH.
Qed.

Section noetherian_finite.

  (** Rings that have finitely many members (up-to equivalence)
      are Noetherian. *)

  (* This is enough to show that Z/kZ is Noetherian, for k ≠ 0 *)

  Variables (R : ring)
            (HR : ∃lR, ∀x : R, ∃y, y ∈ lR ∧ x ∼ᵣ y).

  Theorem finite_noetherian : noetherian R.
  Proof.
    destruct HR as (lR & HlR).
    apply bar_mono with (P := Good (λ l x, ∃y, y ∈ l ∧ x ∼ᵣ y)).
    + apply Good_mono.
      intros l x (y & ? & ->).
      now constructor 1.
    + apply bar_above_length with (S ⌊lR⌋).
      intros l (a & x & b & y & c & -> & ?)%(@php_upto _ (@req R)); auto.
      * apply Good_app_left; constructor 1; exists y; split; auto.
        rewrite in_app_iff; simpl; auto.
      * intros ? ? ->; trivial.
      * intros ? ? ? ->; trivial.
  Qed.

End noetherian_finite.

Check finite_noetherian.

Section wf_strict_divisibility_principal_noetherian.

  (* If R is:
       a) a principal ring, ie every finitely generated ideal in mono-generated 
       b) divisibility is weakly decidable,
       c) strict divisibility is well-founded
     then R is (constructivelly) Noetherian

     This is enough to show that Z (the integers)
     is constructivelly Noetherian. *)

  Notation ring_sdiv := (λ x y, x |ᵣ y ∧ ¬ y |ᵣ x).

  Variables (R : ring) (HR : principal R)
            (HR1 : ∀ x y : R, x |ᵣ y ∨ ¬ x |ᵣ y).

  Add Ring R_is_ring : (is_ring R).

  (* If g is Acc(essible) for strict divisibility
     then any list l generating the same ideal as g
     is eventually extended in to a linearly dependent list *)  
  Local Lemma Acc_sdiv__bar_Good (g : R) :
      Acc ring_sdiv g
    → ∀l, Idl ⌞l⌟ ≡₁ ring_div g 
    → bar LD l.
  Proof.
    induction 1 as [ g _ IHg ]; intros l Hl.
    constructor 2; intros x.
    destruct (HR (x::l)) as (e & He).
    destruct (HR1 g e) as [ Hge | Hge ].
    + constructor; constructor.
      apply Hl, ring_div_trans with (1 := Hge), He.
      constructor 1; eauto.
    + apply (IHg e); auto; split; auto.
      apply He, Idl_mono with ⌞l⌟; auto.
      apply Hl, ring_div_refl.
  Qed.

  Hypothesis (HR2 : @well_founded R ring_sdiv).

  (* Hence since 0ᵣ is Acc(essible), the
     list [] generating the ideal {0ᵣ} 
     is eventually becoming LD *)
     
  Theorem wf_principal_noetherian : noetherian R.
  Proof.
    apply Acc_sdiv__bar_Good with 0ᵣ; auto.
    intro; rewrite Idl_iff_lc__list; split.
    + intros <-%lc_inv; apply ring_div_refl.
    + intros (? & ->); constructor; ring.
  Qed.

End wf_strict_divisibility_principal_noetherian.

Check wf_principal_noetherian.

#[local] Open Scope Z_scope.

Local Definition Zsdiv x y := (x | y)%Z ∧ ¬ (y | x)%Z.

Local Lemma Zsdiv_Acc_not_zero n : ∀z, Z.abs z = n → z ≠ 0 → Acc Zsdiv z.
Proof.
  induction n using (well_founded_induction Wf_Z.R_wf); intros z H1 H2.
  constructor.
  intros y (H3 & H4).
  assert (y ≠ 0) as H5.
  1: intros ->; apply H4; exists 0; ring.
  apply H with (2 := eq_refl); auto.
  split; [ apply Z.abs_nonneg | ].
  apply Z.abs_pos in H5.
  rewrite <- H1.
  destruct H3 as (d & ->).
  rewrite Z.abs_mul, <- (Z.mul_1_l (_ y)) at 1.
  apply Z.mul_lt_mono_pos_r; auto.
  cut (Z.abs d = 0 ∨ Z.abs d = 1 ∨ 1 < Z.abs d); [ | lia ].
  intros [ C | [C|] ]; auto.
  + rewrite Z.abs_0_iff in C; subst d.
    destruct H2; ring.
  + destruct H4; exists d.
    rewrite Z.mul_assoc, <- Z.abs_square, !C; ring.
Qed.

Local Proposition Zsdiv_wf : well_founded Zsdiv.
Proof.
  intros z.
  destruct (Z.eq_dec z 0) as [ -> | H ].
  + constructor.
    intros y (H1 & H2).
    apply Zsdiv_Acc_not_zero with (1 := eq_refl); auto.
    intros ->; apply H2.
    exists 0; ring.
  + apply Zsdiv_Acc_not_zero with (1 := eq_refl); auto.
Qed.

#[local] Hint Resolve Z_principal : core.

Theorem Z_noetherian : noetherian Z_ring.
Proof.
  apply wf_principal_noetherian; auto; simpl.
  + intros x y; destruct (Znumtheory.Zdivide_dec x y); auto.
  + apply Zsdiv_wf.
Qed.

Section quotient_noetherian.

  Variable (R : ring)
           (rel : R → R → Prop)
           (rel_ovr : req ⊆₂ rel) 
           (rel_eqv : Equivalence rel)
           (rel_ext : @ring_eq_ext R op_a op_m iv_a rel).

  Notation Q := (@quotient_ring R rel rel_ovr rel_eqv rel_ext).

  Add Ring R_is_ring : (is_ring R).
  Add Ring Q_is_ring : (is_ring Q).

  Hint Constructors Idl : core.

  Fact quotient_Idl : @Idl R ⊆₂ @Idl Q.
  Proof.
    intros I.
    induction 1 as [ | x y H _ IH | | | ]; eauto.
    + revert IH; now apply Idl_req, rel_ovr.
    + change (@un_a R) with (@un_a Q); auto.
    + change (@op_a R x (@iv_a R y)) with (@op_a Q x (@iv_a Q y)); auto.
    + change (@op_m R a x) with (@op_m Q a x); auto.
  Qed.

  Fact quotient_linearly_dependent l : @LD R l → @LD Q l.
  Proof.
    induction 1 as [ x l H | x l H IH ].
    + constructor 1; apply quotient_Idl, H.
    + now constructor 2. 
  Qed.

  Hypothesis HR : noetherian R.  

  Theorem quotient_noetherian: noetherian (@quotient_ring R rel rel_ovr rel_eqv rel_ext).
  Proof.
    revert HR.
    unfold noetherian, quotient_ring; simpl.
    generalize ([] : list R).
    induction 1 as [ l Hl | l Hl IHl ].
    + constructor 1; now apply quotient_linearly_dependent.
    + constructor 2; intros x. 
      apply IHl; auto.
  Qed.

End quotient_noetherian.

Check quotient_noetherian.

(** How can we show that Q (the field of rationals) is
    Noetherian. Trivial because Idl ⌞l⌟ is either {0} or the whole Q *)

Section fields.

  Variables (F : ring)
            (HF : ∀x : F, x ∼ᵣ 0ᵣ ∨ ∃y, y *ᵣ x ∼ᵣ 1ᵣ).

  Add Ring R_is_ring : (is_ring F).

  Local Fact req_list_choose l : (∃ x y : F, x ∈ l ∧ y *ᵣ x ∼ᵣ 1ᵣ) ∨ ∀x, x ∈ l → x ∼ᵣ 0ᵣ.
  Proof.
    destruct list_choice
      with (Q := fun x : F => ∃y, op_m y x ∼ᵣ un_m)
           (P := fun x : F => x ∼ᵣ un_a)
           (l := l)
      as [ | (? & ? & []) ]; eauto.
  Qed.

  Theorem field_principal : principal F.
  Proof.
    intros l.
    destruct (req_list_choose l)
      as [ (x & y & H1 & Hy) | H ].
    + exists un_m; intros z; split.
      * exists z; ring.
      * intros (k & ->).
        constructor 2 with (op_m (op_m k y) x).
        1: rewrite <- Hy; ring.
        constructor 5. 
        now constructor 1.
    + exists un_a; intros z; split.
      * apply Idl_smallest.
        - apply ring_div_ideal.
        - intros ? ->%H; apply ring_div_refl.
      * intros (k & ->).
        constructor 2 with un_a; try ring.
        constructor 3.
  Qed.

  Theorem field_noetherian : noetherian F.
  Proof.
    constructor 2; intros x.
    destruct (HF x) as [ Hx | (z & Hz) ].
    + constructor 1; constructor 1.
      constructor 2 with un_a.
      * now rewrite Hx.
      * constructor 3.
    + constructor 2; intros y.
      constructor 1; constructor 1.
      constructor 2 with (op_m (op_m y z) x).
      * setoid_replace y with (op_m y un_m) at 2 by ring.
        rewrite <- Hz; ring.
      * constructor 5; constructor 1; auto.
  Qed.

End fields.

