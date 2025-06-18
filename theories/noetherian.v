(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Ring Setoid Utf8.

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

  (* Typical inversion lemma *)
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

  (* Another characterization (FO) *)
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

    Variables (P : list X → X → Prop)
              (P_app_middle : ∀ l m r x, P (l++r) x → P (l++m++r) x).

    Fact Good_app_middle l m r : Good P (l++r) → Good P (l++m++r).
    Proof. induction l; simpl; eauto; intros []%Good_inv; auto. Qed.

    Fact bar_Good_app_middle l m r : bar (Good P) (l++r) → bar (Good P) (l++m++r).
    Proof. apply bar_app_middle, Good_app_middle. Qed.

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

(** bar LD l can be read as l is bound to become linearly dependent 
    after finitely many steps, however it is extended by adding 
    elements (on the lhs) 
    
    Hence bar LD [] means that whichever way you build a list,
    it is bound to become LD after finitely many steps. *) 
    
Definition noetherian (R : ring) := bar (@linearly_dependent R) [].

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

  (* If R is a principal ring where 
      a) divisibility is weakly decidable,
      b) strict divisibility is well-founded
     then R is (constructivelly) Noetherian

     This is enough to show that Z (the integers)
     is constructivelly Noetherian. *)

  Notation ring_sdiv := (λ x y, x |ᵣ y ∧ ¬ y |ᵣ x).

  Variables (R : ring) (HR : principal R)
            (HR1 : ∀ x y : R, x |ᵣ y ∨ ¬ x |ᵣ y).

  Add Ring R_is_ring : (is_ring R).

  (* If g is Acc(essible) for strict divisibility
     then any list l generating the same ideal as g
     is eventually extended in a non-strictly increasing way *)  
  Local Lemma Acc_sdiv__bar_Good (g : R) :
      Acc ring_sdiv g
    → ∀l, Idl ⌞l⌟ ≡₁ ring_div g 
    → bar linearly_dependent l.
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

  (* Hence since 0ᵣ is Acc(essible), the
     list [] generating the ideal {0ᵣ} 
     is eventually becoming LD *)
     
  Hypothesis (HR2 : @well_founded R ring_sdiv).

  Theorem wf_principal_noetherian : noetherian R.
  Proof.
    apply Acc_sdiv__bar_Good with 0ᵣ; auto.
    intros x; rewrite Idl_iff_lc__list; split.
    + intros <-%lc_inv; apply ring_div_refl.
    + intros (k & ->); constructor; ring.
  Qed.

End wf_strict_divisibility_principal_noetherian.

Check wf_principal_noetherian.

(** How can we show that Q (the field of rationals) is
    Noetherian. Trivial because Idl ⌞l⌟ is either {0} or the whole Q *)

Section fields.

  Variables (R : ring)
            (HR : ∀x : R, x ∼ᵣ 0ᵣ ∨ ∃y, y *ᵣ x ∼ᵣ 1ᵣ).

  Add Ring R_is_ring : (is_ring R).

  Local Fact req_list_choose l : (∃ x y : R, x ∈ l ∧ y *ᵣ x ∼ᵣ 1ᵣ) ∨ ∀ x : R, x ∈ l → x ∼ᵣ 0ᵣ.
  Proof.
    destruct list_choice
      with (Q := fun x : R => ∃y, op_m y x ∼ᵣ un_m)
           (P := fun x : R => x ∼ᵣ un_a)
           (l := l)
      as [ | (? & ? & []) ]; eauto.
  Qed.

  Theorem field_principal : principal R.
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

  Theorem field_noetherian : noetherian R.
  Proof.
    constructor 2; intros x.
    destruct (HR x) as [ Hx | (z & Hz) ].
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
