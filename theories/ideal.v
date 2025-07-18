(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Ring Setoid Utf8.

Require Import utils ring.

Import ListNotations.

Set Implicit Arguments.

(** The definition of an ideal in a ring *)

Definition ring_ideal {𝓡 : ring} (𝓘 : 𝓡 → Prop) :=
   (∀ x y, x ∼ᵣ y → 𝓘 x → 𝓘 y)
 ∧ 𝓘 0ᵣ
 ∧ (∀ x y, 𝓘 x → 𝓘 y → 𝓘 (x −ᵣ y))
 ∧ (∀ x y, 𝓘 y → 𝓘 (x *ᵣ y)).

(** Idl P is the ideal generated by P, ie the smallest ideal containing P *)
Inductive Idl {𝓡 : ring} (P : 𝓡 → Prop) : 𝓡 → Prop :=
  | Idl_stop x    : P x → Idl P x
  | Idl_req x y   : x ∼ᵣ y → Idl P x → Idl P y 
  | Idl_un        : Idl P 0ᵣ
  | Idl_sub x y   : Idl P x → Idl P y → Idl P (x −ᵣ y)
  | Idl_scal a x  : Idl P x → Idl P (a *ᵣ x).

#[global] Hint Constructors Idl : core.

Add Parametric Morphism (𝓡 : ring) (P : 𝓡 → Prop): (Idl P) with signature (req) ==> (iff) as Idl_morph.
Proof. intros ? ? E; split; apply (@Idl_req _ P); now rewrite E. Qed.

(** An alternate definition for finitely generated ideals using l(inear) c(ombinations) 

    lc l x means (inductively) that x can be obtained as a linear combination of the members of l *)

Inductive lc {𝓡 : ring} : list 𝓡 → 𝓡 → Prop :=
  | lc_nil  x : 0ᵣ ∼ᵣ x → lc [] x
  | lc_cons a x l z y : a *ᵣ x +ᵣ z ∼ᵣ y → lc l z → lc (x::l) y.

#[global] Hint Constructors lc : core.

Fact lc_req_closed (𝓡 : ring) (l : list 𝓡) x y : x ∼ᵣ y → lc l x → lc l y.
Proof.
  intros H1 H2; revert H2 y H1.
  induction 1 as [ x E | a x l r y E H IH ]; intros z H1.
  + constructor 1; now rewrite E.
  + constructor 2 with a r; auto.
    now rewrite <- H1.
Qed.

Add Parametric Morphism (𝓡 : ring) (l : list 𝓡) : (lc l) with signature (req) ==> (iff) as lc_equiv.
Proof. intros ? ? E; split; apply lc_req_closed; now rewrite E. Qed.

Section ring_ideal.

  Variable (𝓡 : ring).

  Implicit Type (x : 𝓡) (l : list 𝓡) (P Q 𝓘 𝓙 : 𝓡 → Prop).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Fact ring_ideal_equiv 𝓘 𝓙 : 𝓘 ≡₁ 𝓙 → ring_ideal 𝓘 → ring_ideal 𝓙.
  Proof.
    intros E (H1 & H2 & H3 & H4); split right.
    2: now apply E.
    all: intros ? ?; rewrite <- !E; eauto.
  Qed.

  Fact ring_ideal_eq 𝓘 x y : ring_ideal 𝓘 → x ∼ᵣ y → 𝓘 x → 𝓘 y.
  Proof. intros (H & _); apply H. Qed.

  Fact ring_ideal_iv_a 𝓘 x : ring_ideal 𝓘 → 𝓘 x → 𝓘 (iv_a x).
  Proof.
    intros (H0 & H1 & H2 & H3) ?.
    apply H0 with (x := 0ᵣ −ᵣ x); [ ring | auto ].
  Qed.

  Fact ring_ideal_op_a 𝓘 : ring_ideal 𝓘 → ∀ x y, 𝓘 x → 𝓘 y → 𝓘 (x +ᵣ y).
  Proof.
    intros H x y ? ?.
    apply ring_ideal_eq with (x := op_a x (iv_a (iv_a y))); ring || auto.
    apply H; auto. 
    repeat apply ring_ideal_iv_a; auto.
  Qed.

  Fact Idl_ring_ideal P : ring_ideal (Idl P).
  Proof. split right; eauto. Qed.

  Hint Resolve Idl_ring_ideal : core.

  Fact Idl_op_a P x y : Idl P x → Idl P y → Idl P (x +ᵣ y).
  Proof. apply ring_ideal_op_a; auto. Qed.
  
  Fact Idl_iv_a P x : Idl P x → Idl P (-ᵣ x).
  Proof. apply ring_ideal_iv_a; auto. Qed.
  
  (** Idl P is the smallest ideal containing P *)

  Fact Idl_smallest P : ∀𝓘, ring_ideal 𝓘 → P ⊆₁ 𝓘 → Idl P ⊆₁ 𝓘.
  Proof. intros ? (? & ? & ? & ?) ?; induction 1; eauto. Qed.

  Fact Idl_mono P Q : P ⊆₁ Q → Idl P ⊆₁ Idl Q.
  Proof. intro; apply Idl_smallest; auto. Qed.

  Fact Idl_substract P x y : Idl P x → Idl P (y −ᵣ x) → Idl P y.
  Proof. intros H1 H2; apply Idl_req with (2 := Idl_op_a H1 H2); ring. Qed.

  Hint Resolve Idl_mono : core.
  
  Fact Idl_idem P : Idl (Idl P) ⊆₁ Idl P.
  Proof. apply Idl_smallest; auto. Qed.

  Fact Idl_stable x l : Idl ⌞l⌟ x → Idl ⌞x::l⌟ ⊆₁ Idl ⌞l⌟.
  Proof.
    intros H; apply Idl_smallest; auto.
    intros ? [ <- | ]; eauto.
  Qed.

  (** Another characterization of Idl ⌞l⌟ *)

  #[local] Hint Resolve in_eq in_cons : core.

  Fact lc__Idl l x : lc l x → Idl ⌞l⌟ x.
  Proof.
    induction 1 as [ x E | a x l r y E _ IH ]; eauto.
    constructor 2 with (1 := E).
    apply Idl_op_a; eauto.
    revert IH; apply Idl_mono; eauto.
  Qed.

  Fact lc_inv l z :
      lc l z
    → match l with
      | nil  => 0ᵣ ∼ᵣ z
      | x::l => ∃ a y, lc l y ∧ a *ᵣ x +ᵣ y ∼ᵣ z
      end.
  Proof. destruct 1; eauto. Qed.

  Fact lc_inv_1 x z : lc [x] z ↔ ∃ a, a *ᵣ x ∼ᵣ z.
  Proof.
     split.
     + intros (u & v & E%lc_inv & F)%lc_inv.
       exists u; rewrite <- F, <- E; ring.
     + intros (a & <-).
       constructor 2 with a un_a; try ring.
       constructor; auto.
  Qed.

  Fact lc_inv_2 x y z : lc [x;y] z ↔ ∃ a b, a *ᵣ x +ᵣ b *ᵣ y ∼ᵣ z.
  Proof.
     split.
     + intros (u & v & (a & E)%lc_inv_1 & F)%lc_inv.
       exists u, a; rewrite <- F, <- E; ring.
     + intros (a & b & <-).
       constructor 2 with a (op_m b y); try ring.
       constructor 2 with b un_a; try ring.
       constructor; auto.
  Qed.

  Fact lc_un_a l : lc l 0ᵣ.
  Proof.
    induction l as [ | x l IHl ].
    + constructor 1; reflexivity.
    + constructor 2 with (a := (op_m un_a x)) (x := x) (z := un_a); auto || ring.
  Qed.

  Hint Resolve lc_un_a : core.

  Fact lc_op_a l x y : lc l x → lc l y → lc l (x +ᵣ y).
  Proof.
    induction 1 as [ x E | a x l r z E H IH ] in y |- *.
    + intros F%lc_inv.
      rewrite <- E, <- F.
      constructor 1; ring.
    + intros (a' & r' & ? & <-)%lc_inv.
      constructor 2 with (a := op_a a a') (z := op_a r r'); auto.
      rewrite <- E; ring.
  Qed.

  Fact lc_iv_a l x : lc l x → lc l (iv_a x).
  Proof.
    induction 1 as [ x E | a x l r z E H IH ].
    + constructor 1.
      rewrite <- E; ring.
    + constructor 2 with (a := iv_a a) (z := iv_a r); auto.
      rewrite <- E; ring.
  Qed.

  Fact lc_op_m l a x : lc l x → lc l (a *ᵣ x).
  Proof.
    induction 1 as [ x E | b x l r z E H IH ].
    + constructor 1.
      rewrite <- E; ring.
    + constructor 2 with (a := op_m a b) (z := op_m a r); auto.
      rewrite <- E; ring.
  Qed.

  Fact lc_incr l x : x ∈ l → lc l x.
  Proof.
    revert x; induction l as [ | y l IHl ]; intros x []; subst.
    + constructor 2 with (a := un_m) (z := un_a); auto; ring.
    + apply IHl in H.
      constructor 2 with (a := un_a) (z := x); auto; ring.
  Qed.

  Theorem Idl__lc l x : Idl ⌞l⌟ x → lc l x.
  Proof.
    induction 1 as [ x E | x y E | | x y H1 IH1 H2 IH2 | a x H IH ]; auto.
    + now apply lc_incr.
    + now rewrite <- E.
    + apply lc_op_a; auto.
      apply lc_iv_a; auto.
    + now apply lc_op_m.
  Qed.

  (** We have two equivalent definition of the ideal generated
      by a list l,
      + Idl ⌞l⌟ x: by induction on the structure of x
      + lc l x: by induction on l
    *)

  Theorem Idl_iff_lc__list l : Idl ⌞l⌟ ≡₁ lc l.
  Proof.
    split.
    + apply Idl__lc.
    + apply lc__Idl.
  Qed.

  Hint Resolve in_or_app lc_op_m : core.

  (** More generally, the Idl P is the union of lc l for ⌞l⌟ ⊆₁ P *)
  Theorem Idl_iff_lc P x : Idl P x ↔ ∃l, lc l x ∧ ⌞l⌟ ⊆₁ P.
  Proof.
    split.
    + revert x; apply Idl_smallest; [ split right | ].
      * intros x y E (l & H1 & H2); exists l.
        rewrite <- E; auto.
      * exists []; simpl; split; auto; tauto.
      * intros x y (l & H1 & H2) (m & H3 & H4).
        exists (l++m); split.
        - apply Idl_iff_lc__list in H1, H3.
          apply Idl_iff_lc__list.
          constructor 4.
          ++ revert H1; apply Idl_mono; eauto.
          ++ revert H3; apply Idl_mono; eauto.
        - intros ? []%in_app_iff; eauto.
      * intros ? ? (l & []); exists l; eauto.
      * intros x ?; exists [x]; split; eauto.
        - apply Idl_iff_lc__list; constructor 1; eauto.
        - intros ? [ <- | [] ]; auto.
    + intros (l & H1%Idl_iff_lc__list & H2).
      revert H1; now apply Idl_mono.
  Qed.

  Lemma Idl_compact P l : ⌞l⌟ ⊆₁ Idl P → ∃m, ⌞m⌟ ⊆₁ P ∧ ⌞l⌟ ⊆₁ Idl ⌞m⌟.
  Proof.
    induction l as [ | x l IHl ].
    + exists []; split; now simpl.
    + intros H.
      cut (Idl P x); eauto.
      intros (lx & H1 & H2)%Idl_iff_lc.
      destruct IHl as (ll & H3 & H4); eauto.
      exists (lx++ll); split.
      * intros ? []%in_app_iff; auto.
      * intros y  [ <- | Hy%H4 ].
        - apply Idl_iff_lc; eauto.
        - revert Hy; apply Idl_mono.
          intro; rewrite in_app_iff; auto.
  Qed.

  Inductive update : list 𝓡 → list 𝓡 → Prop :=
    | update_stop l x y : lc l (y −ᵣ x) → update (x::l) (y::l)
    | update_skip x l m : update l m → update (x::l) (x::m).

  Hint Constructors update : core.

  Remark update_sym l m : update l m → update m l.
  Proof.
    induction 1 as [ l x y H%Idl_iff_lc__list%Idl_iv_a | ]; auto.
    constructor; apply Idl_iff_lc__list.
    revert H; apply Idl_req; ring.
  Qed.

  Lemma Idl_update_closed l m x : update l m → Idl ⌞l⌟ x → Idl ⌞m⌟ x.
  Proof.
    rewrite !Idl_iff_lc__list.
    intros H1; revert H1 x.
    induction 1 as [ l x y H1 | x l m _ IH ];
      intros u (a & z & H3 & <-)%lc_inv;
      rewrite <- Idl_iff_lc__list in *.
    + apply Idl_op_a.
      2: revert H3; apply Idl_mono; auto.
      apply Idl_scal.
      apply Idl_req with (y −ᵣ (y −ᵣ x)); try ring.
      apply Idl_sub; auto.
      revert H1; apply Idl_mono; auto.
    + apply Idl_op_a.
      * apply Idl_scal; constructor 1; now left.
      * apply Idl_iff_lc__list, IH, Idl_iff_lc__list in H3.
        revert H3; apply Idl_mono; auto.
  Qed.

  Hint Resolve update_sym Idl_update_closed : core.
  
  Remark Idl_update_invariant l m : update l m → Idl ⌞l⌟ ≡₁ Idl ⌞m⌟.
  Proof. split; eauto. Qed.

End ring_ideal.

Arguments ring_ideal {_}.
Arguments update {_}.

(*
#[local] Hint Resolve ring_homo_congr ring_homo_un_a ring_homo_sub_a ring_homo_op_m : core.
*)

Definition ring_sub_homo {𝓡 𝓣 : ring} (f : 𝓡 → 𝓣) :=
   (∀ x y, x ∼ᵣ y → f x ∼ᵣ f y)
 ∧ (∀ x y, f (x −ᵣ y) ∼ᵣ f x −ᵣ f y)
 ∧ (∀ x y, f (x *ᵣ y) ∼ᵣ f x *ᵣ f y)
 ∧ (f 0ᵣ ∼ᵣ 0ᵣ).

Fact Idl_sub_homo (𝓡 𝓣 : ring) (f : 𝓡 → 𝓣) :
    ring_sub_homo f
  → ∀ (P : 𝓡 → Prop) x, Idl P x → Idl (λ y, ∃x, y = f x ∧ P x) (f x).
Proof. intros (? & ? & []); induction 1; eauto. Qed.
