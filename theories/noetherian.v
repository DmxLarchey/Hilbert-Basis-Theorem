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

#[local] Notation MC := monotone_closure.
#[local] Hint Constructors MC : core.

(** This gives a definition of "pauses"/PA ) 
    for the finite sequence (m : list 𝓡)

      PA (m : list 𝓡) := MC (λ l, idl ⌞l⌟) m

    We give it as an instance of the monotone_closure MC
    an inductive predicate, but the FOL characterization
    given by PA_split (see below) would have worked as well:

    at some point x in the sequence m = l++[x]++r,
    idl ⌞r⌟ pauses, i.e. idl ⌞x::r⌟ ⊆ idl ⌞r⌟
    or equivalently idl ⌞r⌟ x (see PA_split below)
    or equivalently lc r x. 

    Notice that (λ l, idl ⌞l⌟) ignores the order of the list l 
    because ⌞l⌟ is the "set" of members of the list l.
 *)

Definition pauses {𝓡 : ring} := MC (λ l : list 𝓡, idl ⌞l⌟).

#[local] Notation PA := pauses.

Section pauses.

  Variables (𝓡 : ring).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Implicit Type (l m : list 𝓡).

  Fact PA_monotone : monotone (@PA 𝓡).
  Proof. now constructor 2. Qed.

  (** FOL characterization of PA *)
  Fact PA_split m : PA m ↔ ∃ l x r, m = l++x::r ∧ idl ⌞r⌟ x.
  Proof. apply MC_split. Qed.

  (** Some tools for analyzing the PA of lists which already
      have a (partially) specified structure *)

  Fact PA_nil_inv : @PA 𝓡 [] → False.
  Proof. apply MC_inv. Qed.

  Fact PA_cons_inv x m : PA (x::m) ↔ idl ⌞m⌟ x ∨ PA m.
  Proof. apply MC_cons_inv. Qed.

  (* If l++r is PA then the pause occurs either in l or in r *)
  Fact PA_app_inv l r : PA (l++r) ↔ (∃ l' x m, l = l'++x::m ∧ idl ⌞m++r⌟ x) ∨ PA r.
  Proof. apply MC_app_inv. Qed.

  (* If l++[x]++r is PA then the pause occurs either in l, or at x or in r *)
  Fact PA_middle_inv l x r : 
       PA (l++x::r)
    ↔ (∃ l' y m, l = l'++y::m ∧ idl ⌞m++x::r⌟ y) (* in l *)
    ∨ idl ⌞r⌟ x                                  (* at x *)
    ∨ PA r                                       (* in r *)
    .
  Proof. rewrite PA_app_inv, PA_cons_inv; tauto. Qed.

  (* If l++m++[x]++r is PA then the pause occurs either in l, or in m or at x or in r *) 
  Fact PA_special_inv l m x r :
       PA (l++m++x::r)
    ↔ (∃ l₁ y l₂, l = l₁++y::l₂ ∧ idl ⌞l₂++m++x::r⌟ y) (* in l *)
    ∨ (∃ m₁ y m₂, m = m₁++y::m₂ ∧ idl ⌞m₂++x::r⌟ y)    (* in m *)
    ∨ idl ⌞r⌟ x                                        (* at x *)
    ∨ PA r                                             (* in r*)
    .
  Proof. rewrite !PA_app_inv, PA_cons_inv; tauto. Qed.

  (** Since we know that idl _ is invariant under update
      We derive, in sequence, that:
        a) PA _ is invariant under update
        b) bar PA _ is invariant under update *)

  Hint Resolve idl_update_closed
               idl_substract : core.

  Hint Constructors bar update : core.

  (* pause is invariant under update *)
  Lemma PA_update_closed l m : update l m → PA l → PA m.
  Proof. unfold PA; induction 1 as [ ? ? ? ?%idl_iff_lc__list | ]; intros []%MC_inv; eauto. Qed.

  Hint Resolve PA_update_closed : core.

  (* bar PA is invariant under update *)
  Theorem bar_PA_update_closed l m : update l m → bar PA l → bar PA m.
  Proof. apply bar_rel_closed; eauto. Qed.

  Fact PA_app_left l r : PA r → PA (l++r).
  Proof. apply MC_app_left. Qed.

  (** Since PA, the existence of a pause, is invariant 
      under insertion anywhere in the list, then so is 
      bar PA. *)

  Fact PA_app_middle m : ∀ l r, PA (l++r) → PA (l++m++r).
  Proof.
    apply MC_app_middle.
    intros ? ? ?; apply idl_mono.
    intros ?; rewrite !in_app_iff; tauto.
  Qed.

  Fact PA_app_right l r : PA l → PA (l++r).
  Proof.
    intros H.
    rewrite <- app_nil_r, <- app_assoc.
    apply PA_app_middle.
    now rewrite app_nil_r.
  Qed.

  (** Three specializations of bar_app_middle *)

  (* bar PA is invariant under adding elements anywhere *)
  Fact bar_PA_app_middle m : ∀ l r, bar PA (l++r) → bar PA (l++m++r).
  Proof. apply bar_app_middle, PA_app_middle. Qed.

  Fact bar_PA_app_left l r : bar PA r → bar PA (l++r).
  Proof. apply bar_PA_app_middle with (l := []). Qed.

  Fact bar_PA_cons_middle l x r : bar PA (l++r) → bar PA (l++x::r).
  Proof. apply bar_PA_app_middle with (m := [_]). Qed.

End pauses.

#[local] Hint Resolve in_map : core.

(** PA is invariant under sub-homomorphisms *)
Fact PA_sub_homo (𝓡 𝓣 : ring) (f : 𝓡 → 𝓣) :
    ring_sub_homo f
  → ∀ l : list 𝓡, PA l → PA (map f l).
Proof.
  unfold PA.
  induction 2 as [ x l Hl | ]; simpl; auto.
  constructor 1.
  apply idl_sub_homo with (f := f) in Hl; auto.
  revert Hl; apply idl_mono.
  intros ? (? & -> & ?); eauto.
Qed. 

(** bar PA l can be read as l unavoidably pauses
    after finitely many steps, however it is 
    extended by appending elements at its head.

    Hence bar PA [] means that whichever way you 
    grow a list starting from the empty list, it 
    unavoidably pauses after finitely many steps. *) 

Definition noetherian (𝓡 : ring) := bar (@PA 𝓡) [].

(** PA is barred and we find a pause in any "lawlike"
    sequence of fg ideals n → idl ⌞[ρ (n-1);...;ρ 0⌟ *)
Fact noetherian_idl_pauses 𝓡 : 
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

  (** Rings that have finitely many members (up to equivalence)
      are Noetherian.

      This is enough to show that Z/kZ is Noetherian (for k ≠ 0)
   *)

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

  Local Fact quotient_idl : @idl 𝓡 ⊆₂ @idl 𝓚.
  Proof.
    intros I.
    induction 1 as [ | x y H _ IH | | | ]; eauto.
    + revert IH; now apply idl_req, rel_ovr.
    + change (@un_a 𝓡) with (@un_a 𝓚); auto.
    + change (@op_a 𝓡 x y) with (@op_a 𝓚 x y); auto.
    + change (@op_m 𝓡 a x) with (@op_m 𝓚 a x); auto.
  Qed.

  Hint Resolve quotient_idl : core.

  Local Fact quotient_pauses l : @PA 𝓡 l → @PA 𝓚 l.
  Proof. unfold PA; induction 1; eauto. Qed.

  Hint Resolve quotient_pauses : core.
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
     is (Bar) Noetherian. *)

  Notation ring_sdiv := (λ x y, x |ᵣ y ∧ ¬ y |ᵣ x).

  Variables (𝓡 : ring)
            (bezout : bezout_ring 𝓡)
            (div_dec : ∀ x y : 𝓡, x |ᵣ y ∨ ¬ x |ᵣ y).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Hypothesis (sdiv_wf : @well_founded 𝓡 ring_sdiv).

  (* For any g, if it generates the same ideal as l
     then extending l unavoidably pauses. *)
  Lemma wf_sdiv__bar_PA (g : 𝓡) :
      ∀l, idl ⌞l⌟ ≡₁ ring_div g
    → bar PA l.
  Proof.
    induction g as [ g IHg ] using (well_founded_induction sdiv_wf);
      intros l Hl.
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

  Theorem wf_sdiv_bezout_noetherian : noetherian 𝓡.
  Proof.
    apply wf_sdiv__bar_PA with 0ᵣ; auto.
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

Proposition Zsdiv_wf : well_founded Zsdiv.
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


