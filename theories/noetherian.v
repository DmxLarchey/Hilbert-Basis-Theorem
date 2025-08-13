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

Require Import utils bar ring ideal principal php.

#[local] Hint Resolve
           incl_refl incl_nil_l incl_cons incl_tl 
           in_eq in_cons
         : core.

Section Good_and_bar.

  (** The generalization of good : rel₂ X → rel₁ (list A) 
                         as Good : rel (list A) A → rel₁ (list A)
      subsumes both the notion of good (finite) sequence for binary relation
                and the notion of Good increasing sequence of finitely generated ideals of a ring *)  

  Variables (A : Type).

  Implicit Types (P Q : list A → A → Prop).

  Inductive Good P : list A → Prop :=
    | Good_stop a l : P l a    → Good P (a::l)
    | Good_skip a l : Good P l → Good P (a::l).

  Hint Constructors Good : core.

  Fact Good_inv P l :
      Good P l
    → match l with
      | []   => False
      | a::l => P l a ∨ Good P l
      end.
  Proof. destruct 1; eauto. Qed.

  Fact Good_cons_inv P x l : Good P (x::l) ↔ P l x ∨ Good P l.
  Proof.
    split.
    + apply Good_inv.
    + intros []; eauto.
  Qed.

  Fact Good_mono P Q : P ⊆₂ Q → Good P ⊆₁ Good Q.
  Proof. induction 2; eauto. Qed.

  Fact Good_app_left P l r : Good P r → Good P (l++r).
  Proof. intro; induction l; simpl; eauto. Qed.

  Fact Good_app_right P r : 
      (∀ l x, P l x → P (l++r) x)
    → (∀l, Good P l → Good P (l++r)).
  Proof. induction 2; simpl; eauto. Qed.

  Hint Resolve Good_app_left : core.

  (* Another characterization (in FOL) *)
  Lemma Good_split P m : Good P m ↔ ∃ l a r, m = l++a::r ∧ P r a.
  Proof.
    split.
    + induction 1 as [ a m H | a m _ (l & b & r & -> & H) ].
      * now exists [], a, m.
      * now exists (a::l), b, r.
    + intros (? & ? & ? & -> & ?); auto.
  Qed.
  
  Lemma Good_app_inv P l r : Good P (l++r) ↔ (∃ l' a m, l = l'++a::m ∧ P (m++r) a) ∨ Good P r.
  Proof.
    induction l as [ | x l IHl ]; simpl.
    + split; auto; now intros [ ([] & ? & ? & ? & _) | ].
    + rewrite Good_cons_inv, IHl; split.
      * intros [ H1 | [ (l' & y & m & -> & ?) | H1 ] ]; eauto.
        - left; now exists [], x, l.
        - left; now exists (x::l'), y, m.
      * intros [ ([ | z l'] & y & m & [=] & ?) | ]; subst; auto.
        right; left; now exists l', y, m.
  Qed.

  Hint Resolve bar_monotone : core.

  Fact bar_Good_app_left P l m : bar (Good P) m → bar (Good P) (l++m).
  Proof. apply bar_app_left; eauto. Qed.
  
  Section Good_app_middle.

    Variables (P : list A → A → Prop) (m : list A)
              (P_app_middle : ∀ l r a, P (l++r) a → P (l++m++r) a).

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

Definition linearly_dependent {𝓡 : ring} := Good (λ m : list 𝓡, Idl ⌞m⌟).

#[local] Notation LD := linearly_dependent.

Section linearly_dependent.

  Variables (𝓡 : ring).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Implicit Type (l m : list 𝓡).

  (** Since we know that Idl _ is invariant under update
      We derive, in sequence, that:
        a) LD _ is invariant under update
        b) bar LD _ is invariant under update *)

  Hint Resolve Idl_update_closed
               Idl_substract: core.
  Hint Constructors Good : core.

  (** FOL characterization of LD *)
  Fact LD_split m : LD m ↔ ∃ l x r, m = l++x::r ∧ Idl ⌞r⌟ x.
  Proof. apply Good_split. Qed.

  Fact LD_nil_inv : @LD 𝓡 [] → False.
  Proof. apply Good_inv. Qed.

  Fact LD_cons_inv x m : LD (x::m) ↔ Idl ⌞m⌟ x ∨ LD m.
  Proof. apply Good_cons_inv. Qed.

  Fact LD_monotone : monotone (@LD 𝓡).
  Proof. now constructor 2. Qed.

  Fact LD_app_inv l r : LD (l++r) ↔ (∃ l' x m, l = l'++x::m ∧ Idl ⌞m++r⌟ x) ∨ LD r.
  Proof. apply Good_app_inv. Qed.

  Fact LD_middle_inv l x r : LD (l++x::r) ↔ (∃ l' y m, l = l'++y::m ∧ Idl ⌞m++x::r⌟ y) ∨ Idl ⌞r⌟ x ∨ LD r.
  Proof. rewrite LD_app_inv, LD_cons_inv; tauto. Qed.

  Fact LD_special_inv l m x r : LD (l++m++x::r) ↔ (∃ l₁ y l₂, l = l₁++y::l₂ ∧ Idl ⌞l₂++m++x::r⌟ y)
                                                ∨ (∃ m₁ y m₂, m = m₁++y::m₂ ∧ Idl ⌞m₂++x::r⌟ y)
                                                ∨ Idl ⌞r⌟ x
                                                ∨ LD r.
  Proof. rewrite !LD_app_inv, LD_cons_inv; tauto. Qed.

  (* linear dependency is invariant under update *)
  Lemma LD_update_closed l m : update l m → LD l → LD m.
  Proof. unfold LD; induction 1 as [ ? ? ? ?%Idl_iff_lc__list |]; intros []%Good_inv; eauto. Qed.

  Hint Constructors bar update : core.
  Hint Resolve LD_update_closed : core.

  (* bar LD is invariant under update *)
  Theorem bar_LD_update_closed l m : update l m → bar LD l → bar LD m.
  Proof. apply bar_rel_closed; eauto. Qed.

  Fact LD_app_middle m : ∀ l r, LD (l++r) → LD (l++m++r).
  Proof.
    apply Good_app_middle.
    intros ? ? ?; apply Idl_mono.
    intros ?; rewrite !in_app_iff; tauto.
  Qed.
  
  Fact LD_app_left l r : LD r → LD (l++r).
  Proof. apply Good_app_left. Qed.
  
  Fact LD_app_right l r : LD l → LD (l++r).
  Proof.
    intros H.
    rewrite <- app_nil_r, <- app_assoc.
    apply LD_app_middle.
    now rewrite app_nil_r.
  Qed.

   (** Three specializations of bar_Good_app_middle *)

  (* bar LD is invariant under adding elements anywhere *)
  Fact bar_LD_app_middle m : ∀ l r, bar LD (l++r) → bar LD (l++m++r).
  Proof. apply bar_app_middle, LD_app_middle. Qed.

  Fact bar_LD_app_left l r : bar LD r → bar LD (l++r).
  Proof. apply bar_LD_app_middle with (l := []). Qed.

  Fact bar_LD_cons_middle l x r : bar LD (l++r) → bar LD (l++x::r).
  Proof. apply bar_LD_app_middle with (m := [_]). Qed.

End linearly_dependent.

#[local] Hint Resolve in_map : core.

Fact LD_sub_homo (𝓡 𝓣 : ring) (f : 𝓡 → 𝓣) :
    ring_sub_homo f
  → ∀ l : list 𝓡, LD l → LD (map f l).
Proof.
  unfold LD.
  induction 2 as [ x l Hl | ]; simpl; auto.
  constructor 1.
  apply Idl_sub_homo with (f := f) in Hl; auto.
  revert Hl; apply Idl_mono.
  intros ? (? & -> & ?); eauto.
Qed. 

(** bar LD l can be read as l is bound to become linearly dependent 
    after finitely many steps, however it is extended by adding 
    elements (on the lhs) 

    Hence bar LD [] means that whichever way you build a list,
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

  (* This is enough to show that Z/kZ is Noetherian, for k ≠ 0 *)

  Variables (𝓡 : ring)
            (H𝓡 : ∃l, ∀x : 𝓡, ∃y, y ∈ l ∧ x ∼ᵣ y).

  Theorem finite_noetherian : noetherian 𝓡.
  Proof.
    destruct H𝓡 as (lR & HlR).
    apply bar_mono with (P := Good (λ l x, ∃y, y ∈ l ∧ x ∼ᵣ y)).
    + apply Good_mono.
      intros l x (y & ? & ->).
      now constructor 1.
    + apply bar_above_length with (S ⌊lR⌋).
      intros l (a & x & b & y & c & -> & ?)%(@php_upto _ (@req 𝓡)); auto.
      * apply Good_app_left; constructor 1; exists y; split; auto.
        rewrite in_app_iff; simpl; auto.
      * intros ? ? ->; trivial.
      * intros ? ? ? ->; trivial.
  Qed.

End noetherian_finite.

Check finite_noetherian.

Section wf_strict_divisibility_principal_noetherian.

  (* If 𝓡 is:
       a) a principal ring, ie every finitely generated ideal in mono-generated 
       b) divisibility is weakly decidable,
       c) strict divisibility is well-founded
     then 𝓡 is (constructivelly) Noetherian

     This is enough to show that Z (the integers)
     is constructivelly Noetherian. *)

  Notation ring_sdiv := (λ x y, x |ᵣ y ∧ ¬ y |ᵣ x).

  Variables (𝓡 : ring)
            (princ : principal 𝓡)
            (div_wdec : ∀ x y : 𝓡, x |ᵣ y ∨ ¬ x |ᵣ y).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  (* If g is Acc(essible) for strict divisibility
     then any list l generating the same ideal as g
     is eventually extended in to a linearly dependent list *)  
  Local Lemma Acc_sdiv__bar_Good (g : 𝓡) :
      Acc ring_sdiv g
    → ∀l, Idl ⌞l⌟ ≡₁ ring_div g 
    → bar LD l.
  Proof.
    induction 1 as [ g _ IHg ]; intros l Hl.
    constructor 2; intros x.
    destruct (princ (x::l)) as (e & He).
    destruct (div_wdec g e) as [ Hge | Hge ].
    + constructor; constructor.
      apply Hl, ring_div_trans with (1 := Hge), He.
      constructor 1; eauto.
    + apply (IHg e); auto; split; auto.
      apply He, Idl_mono with ⌞l⌟; auto.
      apply Hl, ring_div_refl.
  Qed.

  Hypothesis (sdiv_wf : @well_founded 𝓡 ring_sdiv).

  (* Hence since 0ᵣ is Acc(essible), the
     list [] generating the ideal {0ᵣ} 
     is eventually becoming LD *)

  Theorem wf_principal_noetherian : noetherian 𝓡.
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

  Variable (𝓡 : ring)
           (rel : 𝓡 → 𝓡 → Prop)
           (rel_ovr : req ⊆₂ rel) 
           (rel_eqv : Equivalence rel)
           (rel_ext : ring_eq_ext op_a op_m iv_a rel).

  Notation 𝓚 := (@quotient_ring _ rel rel_ovr rel_eqv rel_ext).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓚_is_ring : (is_ring 𝓚).

  Hint Constructors Idl : core.

  Fact quotient_Idl : @Idl 𝓡 ⊆₂ @Idl 𝓚.
  Proof.
    intros I.
    induction 1 as [ | x y H _ IH | | | ]; eauto.
    + revert IH; now apply Idl_req, rel_ovr.
    + change (@un_a 𝓡) with (@un_a 𝓚); auto.
    + change (@op_a 𝓡 x y) with (@op_a 𝓚 x y); auto.
    + change (@op_m 𝓡 a x) with (@op_m 𝓚 a x); auto.
  Qed.

  Hint Resolve quotient_Idl : core.
  Hint Constructors Good : core.

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

