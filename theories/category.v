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

  Variable (𝓡 : ring).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  (** This is the initiality property for the polynomial ring:
      it is initial in the category of pointed rings which extend 𝓡 *)

  (** A pointed extension of 𝓡 is ring 𝓣, a homomorphism 𝓡 → 𝓣 and
      a singled-out value in 𝓣 

      Beware that what we call pe_embed is not necessarily an
      embedding of rings (ie injective): it is just a homomorphism.
      But for the initial object in the category of pointed extensions,
      by definition, the polynomial ring, pe_embed is actually injective. *)
  Record ring_pointed_ext := 
    { pe_ring :> ring;
      pe_embed : 𝓡 → pe_ring;
      pe_embed_homo : ring_homo pe_embed;
      pe_point : pe_ring }.

  (** A homomorphism of pointed extensions is:
      - is a homomorphism of rings
      - preserves the pe_point
      - commutes with pe_embed *)
  Definition pe_homo {𝓡x 𝓣x : ring_pointed_ext} (γ : 𝓡x → 𝓣x) :=
      ring_homo γ
    ∧ γ (pe_point 𝓡x) ∼ᵣ pe_point 𝓣x
    ∧ ∀r, γ (pe_embed 𝓡x r) ∼ᵣ pe_embed 𝓣x r.

  (** Pointed extensions of 𝓡 form a category *)
  
  Fact pe_homo_id (𝓡x : ring_pointed_ext) : pe_homo (λ p : 𝓡x, p).
  Proof. split right; auto. Qed. 

  Fact pe_homo_comp (𝓡x 𝓣x 𝓚x : ring_pointed_ext) (f : 𝓡x → 𝓣x) (g : 𝓣x → 𝓚x) :
    pe_homo f → pe_homo g → pe_homo (λ p, g (f p)).
  Proof.
    intros (H1 & H2 & H3) (G1 & G2 & G3); split right; auto.
    + rewrite <- G2; now apply G1.
    + intro; rewrite <- G3; now apply G1.
  Qed.

  Hint Resolve pe_homo_id pe_homo_comp : core.

  (** And "the" poly(nomial) ring over 𝓡 is the initial
      object in the category of pointed extensions of 𝓡  *)
  Definition is_poly_ring (𝓡x : ring_pointed_ext) :=
    ∀ 𝓣x : ring_pointed_ext, 
        (∃α : 𝓡x → 𝓣x, pe_homo α)
      ∧ (∀ α β : 𝓡x → 𝓣x, pe_homo α → pe_homo β → ∀p, α p ∼ᵣ β p).

  Section unicity.

  (** The poly(nomial) ring is unique up to isomorphism 

      This should allow an easy proof of isomorphism of
          (𝓡{X})[x] and 𝓡{option X}

      where 𝓡{X} is the polynomial extension over
      an arbitrary type X of undeterminates (see below).

      But we need to build the arbitrary polynomial
      extension and its own characteristic property.
      For this, consider the quotient (in the setoid
      sense) of polynomial expressions by an inductively
      defined ring congruence.

      Then we can show that 𝓡[fin (S n)} is isomorphic
      to 𝓡{option (fin n)} isomorphic to 𝓡{fin n}[x]
      and then generalize the HBT
      by induction on n:

      if 𝓡 is Noetherian then 𝓡{fin n} is Noetherian for any n *)

    Variables (𝓡x₁ 𝓡x₂ : ring_pointed_ext).

    Add Ring 𝓡x1_ring : (is_ring 𝓡x₁).
    Add Ring 𝓡x2_ring : (is_ring 𝓡x₂).

    Theorem poly_ring_unique :
         is_poly_ring 𝓡x₁
       → is_poly_ring 𝓡x₂
       → ∃ (f : 𝓡x₁ → 𝓡x₂) (g : 𝓡x₂ → 𝓡x₁),
             ring_isomorphism f g
           ∧ f (pe_point 𝓡x₁) ∼ᵣ pe_point 𝓡x₂
           ∧ g (pe_point 𝓡x₂) ∼ᵣ pe_point 𝓡x₁.
    Proof.
      intros H1 H2.
      destruct (H1 𝓡x₂) as ((f & Hf) & H3).
      destruct (H2 𝓡x₁) as ((g & Hg) & H4).
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
      indexed by an arbitrary type A *)

  (** We define what it is to be isomorphic to 𝓡{A}
      which is the ring of multi(nomials) over 𝓡 with
      indeterminates in the type A *)

  Variables (A : Type) (𝓡 : ring).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  (** A multi-extension of a ring 𝓡 *)
  Record ring_multi_ext := 
    { me_ring :> ring;
      me_embed : 𝓡 → me_ring;
      me_embed_homo : ring_homo me_embed;
      me_points : A → me_ring }.

  (** A homomorphism of multi-extensions *)
  Definition me_homo {𝓡A 𝓣A : ring_multi_ext} (γ : 𝓡A → 𝓣A) :=
      ring_homo γ
    ∧ (∀a, γ (me_points 𝓡A a) ∼ᵣ me_points 𝓣A a)
    ∧ (∀r, γ (me_embed 𝓡A r) ∼ᵣ me_embed 𝓣A r).

  (** This is the initiality property for the polynomial ring:
      it is initial in the category of pointed rings which extend R *)

  Definition is_multi_ring (𝓡A : ring_multi_ext) :=
    ∀ 𝓣A : ring_multi_ext, 
        (∃α : 𝓡A → 𝓣A, me_homo α)
      ∧ (∀ α β : 𝓡A → 𝓣A, me_homo α → me_homo β → ∀p, α p ∼ᵣ β p).

  Fact me_homo_id (𝓡A : ring_multi_ext) : me_homo (λ p : 𝓡A, p).
  Proof. split right; auto. Qed.

  Fact me_homo_comp (𝓡A 𝓣A 𝓚A : ring_multi_ext) (f : 𝓡A → 𝓣A) (g : 𝓣A → 𝓚A) :
    me_homo f → me_homo g → me_homo (λ p, g (f p)).
  Proof.
    intros (H1 & H2 & H3) (G1 & G2 & G3); split right; auto.
    + intro; rewrite <- G2; now apply G1.
    + intro; rewrite <- G3; now apply G1.
  Qed.

  Hint Resolve me_homo_id me_homo_comp : core.

  Section unicity.

    Variables (𝓡A₁ 𝓡A₂ : ring_multi_ext).

    Add Ring 𝓡A1_ring : (is_ring 𝓡A₁).
    Add Ring 𝓡A2_ring : (is_ring 𝓡A₂).

    Theorem multi_ring_unique :
         is_multi_ring 𝓡A₁
       → is_multi_ring 𝓡A₂
       → ∃ (f : 𝓡A₁ → 𝓡A₂) (g : 𝓡A₂ → 𝓡A₁),
             ring_isomorphism f g
           ∧ (∀x, f (me_points 𝓡A₁ x) ∼ᵣ me_points 𝓡A₂ x)
           ∧ (∀x, g (me_points 𝓡A₂ x) ∼ᵣ me_points 𝓡A₁ x).
    Proof.
      intros H1 H2.
      destruct (H1 𝓡A₂) as ((f & Hf) & H3).
      destruct (H2 𝓡A₁) as ((g & Hg) & H4).
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

(** 𝓡[X] is (isomorphic to) 𝓡{unit} *)
Fact poly_ring__multi_ring 𝓡 (𝓡x : ring_pointed_ext 𝓡) :
    is_poly_ring 𝓡 𝓡x
  → is_multi_ring unit 𝓡 
          {| me_ring := 𝓡x; 
             me_embed := pe_embed 𝓡x; 
             me_embed_homo := pe_embed_homo 𝓡x; 
             me_points := (λ _ : unit, pe_point 𝓡x) |}.
Proof.
  destruct 𝓡x as [ Rx f Hf x ]; simpl.
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

(** (𝓡{U}){V} is 𝓡{U+V} *)
Fact multi_ring_compose {U V 𝓡 𝓡U 𝓡UV} :
    @is_multi_ring U 𝓡 𝓡U
  → @is_multi_ring V 𝓡U 𝓡UV
  → @is_multi_ring (U+V) 𝓡 
       {| me_ring := 𝓡UV; 
          me_embed := λ x, me_embed 𝓡UV (me_embed 𝓡U x); 
          me_embed_homo := ring_homo_compose (me_embed_homo 𝓡U) (me_embed_homo 𝓡UV); 
          me_points := λ x, match x with inl u => me_embed 𝓡UV (me_points 𝓡U u) | inr v => me_points 𝓡UV v end
       |}.
Proof.
  destruct 𝓡U as [ RU phi Hphi f ];
    destruct 𝓡UV as [ RUV psi Hpsi g ]; simpl in *.
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

(** If 𝓡{U} and U is in bijection with V then 𝓡{V}.
    To be used to show that 𝓡{X}[x] is 𝓡{X}{unit}
    and then 𝓡{option X} *)
Fact multi_ring_bijection U V f g 𝓡 𝓡U :
    @bijection U V f g 
  → @is_multi_ring U 𝓡 𝓡U
  → @is_multi_ring V 𝓡
      {| me_ring := 𝓡U; 
         me_embed := me_embed 𝓡U; 
         me_embed_homo := me_embed_homo 𝓡U; 
         me_points := (λ v, me_points 𝓡U (g v)) 
      |}. 
Proof.
  intros (H1 & H2).
  destruct 𝓡U as [ RU phi Hphi h ]; simpl.
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
