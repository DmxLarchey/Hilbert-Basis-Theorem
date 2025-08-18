(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Ring ZArith Lia Setoid Utf8.

Import ListNotations.

Require Import utils bar monotone_closure ring ideal bezout php.

#[local] Hint Resolve
           incl_refl incl_nil_l incl_cons incl_tl 
           in_eq in_cons
         : core.

#[local] Hint Constructors MC : core.

(** This gives a definition of L(inear) D(ependence) of m:
    at some point x in the sequence m = l++[x]++r, 
    idl ⌞r⌟ does not increase, ie idl ⌞x::r⌟ ⊆ idl ⌞r⌟
    or equivalently idl ⌞r⌟ x (see LD_split below)

    Notice that (λ m, idl ⌞m⌟) ignores the order of the list m 
    because ⌞m⌟ is the "set" of members of the list m 

    This definition is equivalent to the usual definition
    of linear dependence for fields: 
      [x₁,...,xₙ] is linearly dependent 
      if there are a₁,...,aₙ with a₁x₁+...+aₙxₙ = 0 
         and aᵢ ≠ 0 for some i in {1,..,n}

    But it may not be so for non-integral rings *)

Definition linearly_dependent {𝓡 : ring} := MC (λ m : list 𝓡, idl ⌞m⌟).

#[local] Notation LD := linearly_dependent.

Section linearly_dependent.

  Variables (𝓡 : ring).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Implicit Type (l m : list 𝓡).

  Fact LD_monotone : monotone (@LD 𝓡).
  Proof. now constructor 2. Qed.

  (** FOL characterization of LD *)
  Fact LD_split m : LD m ↔ ∃ l x r, m = l++x::r ∧ idl ⌞r⌟ x.
  Proof. apply MC_split. Qed.

  Fact LD_nil_inv : @LD 𝓡 [] → False.
  Proof. apply MC_inv. Qed.

  Fact LD_cons_inv x m : LD (x::m) ↔ idl ⌞m⌟ x ∨ LD m.
  Proof. apply MC_cons_inv. Qed.

  (** Tools for analyzing the LD of lists which already
      have a (partially) specified structure *)

  (* If l++r is LD then the linear dependency occurs either in l or in r *)
  Fact LD_app_inv l r : LD (l++r) ↔ (∃ l' x m, l = l'++x::m ∧ idl ⌞m++r⌟ x) ∨ LD r.
  Proof. apply MC_app_inv. Qed.

  (* If l++[x]++r is LD then the linear dependency occurs either in l, or at x or in r *)
  Fact LD_middle_inv l x r : 
       LD (l++x::r)
    ↔ (∃ l' y m, l = l'++y::m ∧ idl ⌞m++x::r⌟ y) (* in l *)
    ∨ idl ⌞r⌟ x                                  (* at x *)
    ∨ LD r                                       (* in r *)
    .
  Proof. rewrite LD_app_inv, LD_cons_inv; tauto. Qed.

  (* If l++m++[x]++r is LD then the linear dependency occurs either in l, or in m or at x or in r *) 
  Fact LD_special_inv l m x r :
       LD (l++m++x::r)
    ↔ (∃ l₁ y l₂, l = l₁++y::l₂ ∧ idl ⌞l₂++m++x::r⌟ y) (* in l *)
    ∨ (∃ m₁ y m₂, m = m₁++y::m₂ ∧ idl ⌞m₂++x::r⌟ y)    (* in m *)
    ∨ idl ⌞r⌟ x                                        (* at x *)
    ∨ LD r                                             (* in r*)
    .
  Proof. rewrite !LD_app_inv, LD_cons_inv; tauto. Qed.

  (** Since we know that idl _ is invariant under update
      We derive, in sequence, that:
        a) LD _ is invariant under update
        b) bar LD _ is invariant under update *)

  Hint Resolve idl_update_closed
               idl_substract : core.

  Hint Constructors bar update : core.

  (* linear dependency is invariant under update *)
  Lemma LD_update_closed l m : update l m → LD l → LD m.
  Proof. unfold LD; induction 1 as [ ? ? ? ?%idl_iff_lc__list |]; intros []%MC_inv; eauto. Qed.

  Hint Resolve LD_update_closed : core.

  (* bar LD is invariant under update *)
  Theorem bar_LD_update_closed l m : update l m → bar LD l → bar LD m.
  Proof. apply bar_rel_closed; eauto. Qed.

  (** Since LD _ is invariant under insertion anywhere in the list,
      then so is bar LD _. *)

  Fact LD_app_middle m : ∀ l r, LD (l++r) → LD (l++m++r).
  Proof.
    apply MC_app_middle.
    intros ? ? ?; apply idl_mono.
    intros ?; rewrite !in_app_iff; tauto.
  Qed.

  Fact LD_app_left l r : LD r → LD (l++r).
  Proof. apply MC_app_left. Qed.

  Fact LD_app_right l r : LD l → LD (l++r).
  Proof.
    intros H.
    rewrite <- app_nil_r, <- app_assoc.
    apply LD_app_middle.
    now rewrite app_nil_r.
  Qed.

  (** Three specializations of bar_app_middle *)

  (* bar LD is invariant under adding elements anywhere *)
  Fact bar_LD_app_middle m : ∀ l r, bar LD (l++r) → bar LD (l++m++r).
  Proof. apply bar_app_middle, LD_app_middle. Qed.

  Fact bar_LD_app_left l r : bar LD r → bar LD (l++r).
  Proof. apply bar_LD_app_middle with (l := []). Qed.

  Fact bar_LD_cons_middle l x r : bar LD (l++r) → bar LD (l++x::r).
  Proof. apply bar_LD_app_middle with (m := [_]). Qed.

End linearly_dependent.

#[local] Hint Resolve in_map : core.

(** LD is invariant under sub-homomorphisms *)
Fact LD_sub_homo (𝓡 𝓣 : ring) (f : 𝓡 → 𝓣) :
    ring_sub_homo f
  → ∀ l : list 𝓡, LD l → LD (map f l).
Proof.
  unfold LD.
  induction 2 as [ x l Hl | ]; simpl; auto.
  constructor 1.
  apply idl_sub_homo with (f := f) in Hl; auto.
  revert Hl; apply idl_mono.
  intros ? (? & -> & ?); eauto.
Qed. 

(** bar LD l can be read as l is bound to become linearly dependent
    after finitely many steps, however it is extended by appending
    elements (at its head).

    Hence bar LD [] means that whichever way you grow a list,
    it is bound to become LD after finitely many steps. *) 

Definition noetherian (𝓡 : ring) := bar (@LD 𝓡) [].

(** Noetherianess is invariant under surjective homomorphisms *)
Lemma noetherian_surj_homo (𝓡 𝓣 : ring) :
    (∃ f : 𝓡 → 𝓣, ring_homo f ∧ ∀x, ∃y, f y ∼ᵣ x)
  → noetherian 𝓡 → noetherian 𝓣.
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
    * rewrite H3; auto.
    * rewrite H4; auto.
  + intros ? (? & ? & ? & ? & ->)%Forall2_cons_inv_l.
    constructor 2; now apply IH.
Qed.

(** Hence also invariant under isomorphisms *)
Corollary noetherian_isomorphism (𝓡 𝓣 : ring) :
    (∃ (f : 𝓡 → 𝓣) (g : 𝓣 → 𝓡), ring_isomorphism f g)
  → noetherian 𝓡 → noetherian 𝓣.
Proof.
  intros H; apply noetherian_surj_homo.
  destruct H as (f & ? & ? & ? & []); eauto.
Qed.

Section noetherian_finite.

  (** Rings that have finitely many members (up-to equivalence)
      are Noetherian. *)

  (* This is enough to show that Z/kZ is Noetherian (for k ≠ 0) *)

  Variables (𝓡 : ring)
            (H𝓡 : ∃l, ∀x : 𝓡, ∃y, y ∈ l ∧ x ∼ᵣ y).

  Theorem finite_noetherian : noetherian 𝓡.
  Proof.
    destruct H𝓡 as (lR & HlR).
    apply bar_mono with (P := MC (λ l x, ∃y, y ∈ l ∧ x ∼ᵣ y)).
    + apply MC_mono.
      intros l x (y & ? & ->).
      now constructor 1.
    + apply bar_above_length with (S ⌊lR⌋).
      intros l (a & x & b & y & c & -> & ?)%(@php_upto _ (@req 𝓡)); auto.
      * apply MC_app_left; constructor 1; exists y; split; auto.
        rewrite in_app_iff; simpl; auto.
      * intros ? ? ->; trivial.
      * intros ? ? ? ->; trivial.
  Qed.

End noetherian_finite.

Check finite_noetherian.

Section quotient_noetherian.

  Variable (𝓡 : ring)
           (rel : 𝓡 → 𝓡 → Prop)
           (rel_ovr : req ⊆₂ rel) 
           (rel_eqv : Equivalence rel)
           (rel_ext : ring_eq_ext op_a op_m iv_a rel).

  Notation 𝓚 := (@quotient_ring _ rel rel_ovr rel_eqv rel_ext).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓚_is_ring : (is_ring 𝓚).

  Hint Constructors idl : core.

  Fact quotient_idl : @idl 𝓡 ⊆₂ @idl 𝓚.
  Proof.
    intros I.
    induction 1 as [ | x y H _ IH | | | ]; eauto.
    + revert IH; now apply idl_req, rel_ovr.
    + change (@un_a 𝓡) with (@un_a 𝓚); auto.
    + change (@op_a 𝓡 x y) with (@op_a 𝓚 x y); auto.
    + change (@op_m 𝓡 a x) with (@op_m 𝓚 a x); auto.
  Qed.

  Hint Resolve quotient_idl : core.

  Fact quotient_linearly_dependent l : @LD 𝓡 l → @LD 𝓚 l.
  Proof. unfold linearly_dependent; induction 1; eauto. Qed.

  Hint Resolve quotient_linearly_dependent : core.
  Hint Constructors bar : core.

  Theorem quotient_noetherian : noetherian 𝓡 → noetherian 𝓚.
  Proof.
    unfold noetherian, quotient_ring; simpl.
    generalize ([] : list 𝓡).
    induction 1; eauto.
  Qed.

End quotient_noetherian.

Check quotient_noetherian.

(** We prove a theorem about Bezout rings
    and Noetherianess to establish that
    the ring of integers Z is Noetherian. *)

Section wf_strict_divisibility_bezout_noetherian.

  (* If 𝓡 is:
       a) a Bezout ring, ie every finitely generated ideal is singleton-generated 
       b) divisibility is (logically) decidable,
       c) strict divisibility is well-founded
     then 𝓡 is (constructivelly) Noetherian

     This is enough to show that Z (the integers)
     is constructivelly Noetherian. *)

  Notation ring_sdiv := (λ x y, x |ᵣ y ∧ ¬ y |ᵣ x).

  Variables (𝓡 : ring)
            (bezout : bezout_ring 𝓡)
            (div_dec : ∀ x y : 𝓡, x |ᵣ y ∨ ¬ x |ᵣ y).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  (* If g is Acc(essible) for strict divisibility
     then any list l generating the same ideal as g
     is eventually extended in to a linearly dependent list *)  
  Local Lemma Acc_sdiv__bar_Good (g : 𝓡) :
      Acc ring_sdiv g
    → ∀l, idl ⌞l⌟ ≡₁ ring_div g 
    → bar LD l.
  Proof.
    induction 1 as [ g _ IHg ]; intros l Hl.
    constructor 2; intros x.
    destruct (bezout (x::l)) as (e & He).
    destruct (div_dec g e) as [ Hge | Hge ].
    + constructor; constructor.
      apply Hl, ring_div_trans with (1 := Hge), He.
      constructor 1; eauto.
    + apply (IHg e); auto; split; auto.
      apply He, idl_mono with ⌞l⌟; auto.
      apply Hl, ring_div_refl.
  Qed.

  Hypothesis (sdiv_wf : @well_founded 𝓡 ring_sdiv).

  (* Hence since 0ᵣ is Acc(essible), the
     list [] generating the ideal {0ᵣ} 
     is eventually becoming LD *)

  Theorem wf_sdiv_bezout_noetherian : noetherian 𝓡.
  Proof.
    apply Acc_sdiv__bar_Good with 0ᵣ; auto.
    intro; rewrite idl_iff_lc__list; split.
    + intros <-%lc_inv; apply ring_div_refl.
    + intros (? & ->); constructor; ring.
  Qed.

End wf_strict_divisibility_bezout_noetherian.

Check wf_sdiv_bezout_noetherian.

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

(** Using wf_sdiv_bezout_noetherian, we can show that
    the ring of integers Z is a Noetherian ring, on 
    top of being a Bezout ring *)

Theorem Z_noetherian : noetherian Z_ring.
Proof.
  apply wf_sdiv_bezout_noetherian; auto; simpl.
  + exact Z_bezout_ring.
  + intros x y; destruct (Znumtheory.Zdivide_dec x y); auto.
  + exact Zsdiv_wf.
Qed.


