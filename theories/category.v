(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Setoid Utf8.

Require Import utils ring.

#[local] Hint Resolve ring_homo_id ring_homo_compose : core.

Section characteristic_property_of_the_polynomial_ring.

  Variable (R : ring).

  Add Ring R_is_ring : (is_ring R).

  (** This is the initiality property for the polynomial ring:
      it is initial in the category of pointed rings which extend R *)

  (** A pointed extension of R is ring T, a homomorphism R → T and
      a singled-out value in T 

      Beware that what we call pe_embed is not necessarily an
      embedding of rings (ie injective): it is just a homomorphism.
      But for the initial object in the category of pointed extensions,
      by definition, the polynomial ring, pe_embed is actually injective. *)
  Record ring_pointed_ext := 
    { pe_ring :> ring;
      pe_embed : R → pe_ring;
      pe_embed_homo : ring_homo pe_embed;
      pe_point : pe_ring }.

  (** A homomorphism of pointed extensions is:
      - is a homomorphism of rings
      - preserves the pe_point
      - commutes with pe_embed *)
  Definition pe_homo {Rx Tx : ring_pointed_ext} (γ : Rx → Tx) :=
      ring_homo γ
    ∧ γ (pe_point Rx) ∼ᵣ pe_point Tx
    ∧ ∀r, γ (pe_embed Rx r) ∼ᵣ pe_embed Tx r.

  (** Pointed extensions of R form a category *)

  Fact pe_homo_id (Rx : ring_pointed_ext) : pe_homo (λ p : Rx, p).
  Proof. split right; auto. Qed. 

  Fact pe_homo_comp (Rx Tx Kx : ring_pointed_ext) (f : Rx → Tx) (g : Tx → Kx) :
    pe_homo f → pe_homo g → pe_homo (λ p, g (f p)).
  Proof.
    intros (H1 & H2 & H3) (G1 & G2 & G3); split right; auto.
    + rewrite <- G2; now apply G1.
    + intro; rewrite <- G3; now apply G1.
  Qed.

  Hint Resolve pe_homo_id pe_homo_comp : core.

  (** And "the" poly(nomial) ring over R is the initial
      object in the category of pointed extensions of R *)
  Definition is_poly_ring (Rx : ring_pointed_ext) :=
    ∀ Tx : ring_pointed_ext, 
        (∃α : Rx → Tx, pe_homo α)
      ∧ (∀ α β : Rx → Tx, pe_homo α → pe_homo β → ∀p, α p ∼ᵣ β p).

  Section unicity.

  (** The poly(nomial) ring is unique up to isomorphism 

      This should allow an easy proof of isomorphism of
          (R{X})[x] and R{option X}

      where R{X} is the polynomial extension over
      an arbitrary type X of undeterminates (see below).

      But we need to build the arbitrary polynomial
      extension and its own characteristic property.
      For this, consider the quotient (in the setoid
      sense) of polynomial expressions by an inductively
      defined ring congruence.

      Then we can show that
        R[fin (S n)} is isomorphic to
        R{option (fin n)} isomorphic to
        R{fin n}[x]
      and then generalize the HBT
      by induction on n:

      if R is Noetherian then R{fin n} is Noetherian for any n *)

    Variables (Rx₁ Rx₂ : ring_pointed_ext).

    Add Ring Rx1_ring : (is_ring Rx₁).
    Add Ring Rx2_ring : (is_ring Rx₂).

    Theorem poly_ring_unique :
         is_poly_ring Rx₁
       → is_poly_ring Rx₂
       → ∃ (f : Rx₁ → Rx₂) (g : Rx₂ → Rx₁),
             ring_isomorphism f g
           ∧ f (pe_point Rx₁) ∼ᵣ pe_point Rx₂
           ∧ g (pe_point Rx₂) ∼ᵣ pe_point Rx₁.
    Proof.
      intros H1 H2.
      destruct (H1 Rx₂) as ((f & Hf) & H3).
      destruct (H2 Rx₁) as ((g & Hg) & H4).
      exists f, g; split right.
      + split right.
        * apply Hf.
        * apply Hg.
        * intro; apply (proj2 (H2 _) (λ p, f (g p)) (λ p, p)); auto.
        * intro; apply (proj2 (H1 _) (λ p, g (f p)) (λ p, p)); auto.
      + apply Hf.
      + apply Hg.
    Qed.

  End unicity.

End characteristic_property_of_the_polynomial_ring.

Arguments pe_ring {_}.
Arguments pe_embed {_}.
Arguments pe_embed_homo {_}.
Arguments pe_point {_}.

Section characteristic_property_of_multivariate_rings.

  (** The categorical notion of polynomial ring can be easily
      generalized to multivariate rings, where unknowns are
      indexed by an arbitrary type X *)

  (** We define what it is to be isomorphic to R{X}
      which is the ring of multi(nomials) over R with
      indeterminates in the type X *)

  Variables (X : Type) (R : ring).

  Add Ring R_is_ring : (is_ring R).

  (** A multi-extension of a ring R *)
  Record ring_multi_ext := 
    { me_ring :> ring;
      me_embed : R → me_ring;
      me_embed_homo : ring_homo me_embed;
      me_points : X → me_ring }.

  (** A homomorphism of multi-extensions *)
  Definition me_homo {RX TX : ring_multi_ext} (γ : RX → TX) :=
      ring_homo γ
    ∧ (∀x, γ (me_points RX x) ∼ᵣ me_points TX x)
    ∧ (∀r, γ (me_embed RX r) ∼ᵣ me_embed TX r).

  (** This is the initiality property for the polynomial ring:
      it is initial in the category of pointed rings which extend R *)

  Definition is_multi_ring (RX : ring_multi_ext) :=
    ∀ TX : ring_multi_ext, 
        (∃α : RX → TX, me_homo α)
      ∧ (∀ α β : RX → TX, me_homo α → me_homo β → ∀p, α p ∼ᵣ β p).

  Fact me_homo_id (RX : ring_multi_ext) : me_homo (λ p : RX, p).
  Proof. split right; auto. Qed.

  Fact me_homo_comp (RX TX KX : ring_multi_ext) (f : RX → TX) (g : TX → KX) :
    me_homo f → me_homo g → me_homo (λ p, g (f p)).
  Proof.
    intros (H1 & H2 & H3) (G1 & G2 & G3); split right; auto.
    + intro; rewrite <- G2; now apply G1.
    + intro; rewrite <- G3; now apply G1.
  Qed.

  Hint Resolve me_homo_id me_homo_comp : core.

  Section unicity.

    Variables (RX₁ RX₂ : ring_multi_ext).

    Add Ring RX1_ring : (is_ring RX₁).
    Add Ring RX2_ring : (is_ring RX₂).

    Theorem multi_ring_unique :
         is_multi_ring RX₁
       → is_multi_ring RX₂
       → ∃ (f : RX₁ → RX₂) (g : RX₂ → RX₁),
             ring_isomorphism f g
           ∧ (∀x, f (me_points RX₁ x) ∼ᵣ me_points RX₂ x)
           ∧ (∀x, g (me_points RX₂ x) ∼ᵣ me_points RX₁ x).
    Proof.
      intros H1 H2.
      destruct (H1 RX₂) as ((f & Hf) & H3).
      destruct (H2 RX₁) as ((g & Hg) & H4).
      exists f, g; split right.
      + split right.
        * apply Hf.
        * apply Hg.
        * intro; apply (proj2 (H2 _) (λ p, f (g p)) (λ p, p)); auto.
        * intro; apply (proj2 (H1 _) (λ p, g (f p)) (λ p, p)); auto.
      + apply Hf.
      + apply Hg.
    Qed.

  End unicity.

End characteristic_property_of_multivariate_rings.

Arguments me_ring {_ _}.
Arguments me_embed {_ _}.
Arguments me_embed_homo {_ _}.
Arguments me_points {_ _}.

(** R[X] is (isomorphic to) R{unit} *)
Fact poly_ring__multi_ring R (Rx : ring_pointed_ext R) :
    is_poly_ring R Rx
  → is_multi_ring unit R 
          {| me_ring := Rx; 
             me_embed := pe_embed Rx; 
             me_embed_homo := pe_embed_homo Rx; 
             me_points := (λ _ : unit, pe_point Rx) |}.
Proof.
  destruct Rx as [ Rx f Hf x ]; simpl.
  intros H TX.
  destruct (H {| pe_ring := TX; 
                 pe_embed := me_embed TX; 
                 pe_embed_homo := me_embed_homo TX; 
                 pe_point := me_points TX tt |})
    as ((g & Hg) & H1); simpl in *; split.
  + exists g; split right; try apply Hg.
    intros []; simpl; apply Hg.
  + intros a b Ha Hb; apply H1.
    * split right; apply Ha.
    * split right; apply Hb.
Qed.

(** (R{U}){V} is R{U+V} *)
Fact multi_ring_compose {U V R RU RUV} :
    @is_multi_ring U R RU
  → @is_multi_ring V RU RUV
  → @is_multi_ring (U+V) R 
       {| me_ring := RUV; 
          me_embed := λ x, me_embed RUV (me_embed RU x); 
          me_embed_homo := ring_homo_compose (me_embed_homo RU) (me_embed_homo RUV); 
          me_points := λ x, match x with inl u => me_embed RUV (me_points RU u) | inr v => me_points RUV v end
       |}.
Proof.
  destruct RU as [ RU phi Hphi f ];
    destruct RUV as [ RUV psi Hpsi g ]; simpl in *.
  intros HU HUV TUV.
  destruct (HU {| me_ring := TUV; 
                  me_embed := me_embed TUV;
                  me_embed_homo := me_embed_homo TUV; 
                  me_points := λ u, me_points TUV (inl u) |})
    as ((al & Hal) & H1); simpl in *.
  destruct (HUV {| me_ring := TUV; 
                  me_embed := al;
                  me_embed_homo := proj1 Hal; 
                  me_points := λ v, me_points TUV (inr v) |})
    as ((be & Hbe) & H2); simpl in *.
  split.
  + destruct Hal as (F1 & F2 & F3).
    destruct Hbe as (G1 & G2 & G3). 
    simpl in *.
    exists be; split right; simpl; auto.
    * intros []; simpl; auto; now rewrite G3.
    * intro; now rewrite G3.
  + destruct Hal as (U1 & U2 & H3).
    intros a b (F1 & F2 & F3) (G1 & G2 & G3) p; simpl in *.
    generalize (λ u, F2 (inl u)) (λ v, F2 (inr v)); clear F2; intros F2 F4.
    generalize (λ u, G2 (inl u)) (λ v, G2 (inr v)); clear G2; intros G2 G4.
    apply H2; auto; split right; simpl; auto; apply H1; split right; auto.
Qed.

Definition bijection {U V} (f : U → V) (g : V → U) :=
    (∀v, f (g v) = v) ∧ (∀u, g (f u) = u).

(** If R{U} and U is in bijection with V then R{V}.
    To be used to show that R{X}[x] is R{X}{unit}
    and then R{option X} *)
Fact multi_ring_bijection U V f g R RU :
    @bijection U V f g 
  → @is_multi_ring U R RU
  → @is_multi_ring V R
      {| me_ring := RU; 
         me_embed := me_embed RU; 
         me_embed_homo := me_embed_homo RU; 
         me_points := (λ v, me_points RU (g v)) 
      |}. 
Proof.
  intros (H1 & H2).
  destruct RU as [ RU phi Hphi h ]; simpl.
  intros G RV.
  destruct (G {| me_ring := RV; 
                 me_embed := me_embed RV; 
                 me_embed_homo := me_embed_homo RV; 
                 me_points := (λ u, me_points RV (f u))
              |})
    as ((a & G1 & G2 & G3) & H); split; simpl in *.
  + exists a; split right; auto.
    intro; simpl; now rewrite G2, H1.
  + intros b c (F1 & F2 & F3) (F4 & F5 & F6); simpl in *; apply H.
    * split right; simpl; auto.
      intro; now rewrite <- F2, H2.
    * split right; simpl; auto.
      intro; now rewrite <- F5, H2.
Qed.
