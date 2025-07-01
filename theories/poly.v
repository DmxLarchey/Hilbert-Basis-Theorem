(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Wellfounded Setoid Utf8.

Require Import utils ring ideal measure.

Import ListNotations.

#[local] Hint Resolve ring_homo_id ring_homo_compose : core.

Section characteristic_property_of_the_polynomial_ring.

  Variable (R : ring).

  Add Ring R_is_ring : (is_ring R).

  (** This is the initiality property for the polynomial ring:
      it is initial in the category of pointed rings which extend R *)

  (** A pointed extension of R *)
  Record ring_pointed_ext := 
    { pe_ring :> ring;
      pe_embed : R → pe_ring;
      pe_embed_homo : ring_homo pe_embed;
      pe_point : pe_ring }.

  (** A homomorphism of pointed extensions *)
  Definition pe_homo {Rx Tx : ring_pointed_ext} (γ : Rx → Tx) :=
      ring_homo γ
    ∧ γ (pe_point Rx) ∼ᵣ pe_point Tx
    ∧ ∀r, γ (pe_embed Rx r) ∼ᵣ pe_embed Tx r.

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

  Definition is_poly_ring (Rx : ring_pointed_ext) :=
    ∀ Tx : ring_pointed_ext, 
        (∃α : Rx → Tx, pe_homo α)
      ∧ (∀ α β : Rx → Tx, pe_homo α → pe_homo β → ∀p, α p ∼ᵣ β p).

  Section unicity.

  (** The polynomial ring is unique up to isomorphism 

      This should allow an easy proof of isomorphism of 
          (R{X})[x] and R{option X}

      where R{X} is the polynomial extension over 
      an arbitrary type X of undeterminates.

      But we need to build the arbitrary polynomial
      extension and its own characteristic property.
      For this, consider the quotient (in the setoid
      sense) of polynomial expressions by and inductively
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

  (** We define what it is to be isomorphic to R{X}
      which is the ring of polynomials over R with
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

(** R[X] is R{unit} *)
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

(** R{U}{V} is R{U+V} *)
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

(** if R{U} and V is in bijection with V then R{V} and iso ? 
    to be used to show that R{X}[x] is R{X}{unit} and then R{option X} *)
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

#[local] Hint Constructors is_last : core.

Section polynomial_ring.

  Variable (R : ring).

  Add Ring ring_is_ring : (is_ring R).

  Implicit Type (x : R).

  (* We use this non-canonical representation
     of polynomials:
     a₀+...+aₙXⁿ = [a₀;...;aₙ]
     X = 0+1.X = [0ᵣ;1ᵣ] 

     Notice that [] = [un_a] = [un_a;...;un_a] !!

     The degree of a polynomial is not computable
     unless one can computably decide inequality
     over the base ring R 

     Indeed, degree [a₀;...;aₙ] < n iff
     aₙ ~ᵣ 0ᵣ 

     degree [a -ᵣ b] is < 0 iff a ~ᵣ b *)

  Notation poly := (list R).

  Implicit Type l : poly.

  Notation poly_zero := (Forall (req un_a)).

  Fact poly_zero_inv l :
      poly_zero l
    → match l with
      | []   => True
      | x::m => 0ᵣ ∼ᵣ x ∧ poly_zero m
      end.
  Proof. now intros []. Qed.

  Reserved Notation "l ∼ₚ m" (at level 70, no associativity, format "l  ∼ₚ  m").

  Fixpoint poly_eq (l m : poly) :=
    match l, m with
    | [], _      => poly_zero m
    | _,  []     => poly_zero l
    | x::l, y::m => x ∼ᵣ y ∧ l ∼ₚ m
    end
  where "l ∼ₚ m" := (poly_eq l m).

  Fact poly_zero_left l : poly_zero l → l ∼ₚ [].
  Proof. destruct l; simpl; auto. Qed.

  Fact poly_zero_left_inv l : l ∼ₚ [] → poly_zero l.
  Proof. destruct l; simpl; auto. Qed.

  Hint Resolve poly_zero_left poly_zero_left_inv : core.

  Fact poly_eq_iff_poly_zero l : poly_zero l ↔ [] ∼ₚ l.
  Proof. split; auto. Qed.

  Section poly_eq_ind.

    Variables (P : poly → poly → Prop)
              (HP0 : ∀m, poly_zero m → P [] m)
              (HP1 : ∀l, poly_zero l → P l [])
              (HP2 : ∀ x l y m, x ∼ᵣ y → P l m → P (x::l) (y::m)).

    Theorem poly_eq_ind l m : l ∼ₚ m → P l m.
    Proof.
      double list induction l m as ? ? ?; eauto.
      intros []; eauto.
    Qed.

  End poly_eq_ind.

  Add Parametric Morphism: cons with signature (req) ==> (poly_eq) ==> (poly_eq) as cons_morph.
  Proof. now constructor. Qed.

  Fact poly_eq_app__length l1 l2 m1 m2 :
     ⌊l1⌋ = ⌊l2⌋ → l1 ∼ₚ l2 → m1 ∼ₚ m2 → l1++m1 ∼ₚ l2++m2.
  Proof.
    double length induction l1 l2 as x y IH; simpl; auto.
    intros []; split; auto.
  Qed.

  Fact poly_eq_refl l : l ∼ₚ l.
  Proof. induction l; simpl; constructor; auto; reflexivity. Qed.

  Hint Resolve poly_eq_refl : core.

  Fact poly_eq_sym l m : l ∼ₚ m → m ∼ₚ l.
  Proof. induction 1 using poly_eq_ind; simpl; auto. Qed.

  Fact poly_zero_poly_eq_closed l m : l ∼ₚ m → poly_zero l → poly_zero m.
  Proof.
    induction 1 using poly_eq_ind; simpl; auto.
    intros []%poly_zero_inv; constructor; eauto.
  Qed.

  Fact poly_zero__poly_eq l m : poly_zero l → poly_zero m → l ∼ₚ m.
  Proof.
    double list induction l m as ? ? ?; eauto.
    intros []%poly_zero_inv []%poly_zero_inv; split; eauto.
  Qed.

  Hint Resolve poly_eq_refl poly_eq_sym
               poly_zero_poly_eq_closed 
               poly_zero__poly_eq : core.

  Fact poly_eq_trans l m k : l ∼ₚ m → m ∼ₚ k → l ∼ₚ k.
  Proof.
    revert m k; induction l as [ | x l IHl ]; intros [ | y m ] [ | z k ];
        simpl; auto.
    + intros (<- & H)%poly_zero_inv (E & G); constructor; auto.
      revert H; now apply poly_zero_poly_eq_closed.
    + intros []%poly_zero_inv []%poly_zero_inv; split; eauto.
    + intros (E & H) (F & G)%poly_zero_inv; constructor; auto.
      * now rewrite E.
      * revert G; apply poly_zero_poly_eq_closed; auto.
    + intros [] []; split; eauto.
  Qed.

  Hint Resolve poly_eq_trans : core.

  Add Parametric Relation: poly poly_eq 
      reflexivity proved by poly_eq_refl
      symmetry proved by poly_eq_sym
      transitivity proved by poly_eq_trans
  as poly_eq_is_equivalence.

  Add Parametric Morphism: poly_zero with signature (poly_eq) ==> (iff) as poly_zero_morph.
  Proof. split; eauto. Qed.

  Reserved Notation "l +ₚ m" (at level 30, right associativity, format "l  +ₚ  m").

  (** We define 
          [a₀;...;aₙ] +ₚ [b₀;...;bₙ] = [a₀+b₀;...;aₙ+bₙ]
      If the list have different length, simply ignore
      the addition *)
  Fixpoint poly_a l m :=
    match l with
    | []      => m
    | x::l'   =>
      match m with 
      | []    => l
      | y::m' => (x +ᵣ y)::(l' +ₚ m')
      end
    end
  where "l +ₚ m" := (poly_a l m).

  Fact poly_a_length l m : ⌊l +ₚ m⌋ = max ⌊l⌋ ⌊m⌋.
  Proof. revert m; induction l; intros []; simpl; f_equal; auto. Qed.

  Fact poly_a_app__length l₁ l₂ m₁ m₂ :
     ⌊l₁⌋ = ⌊l₂⌋ → poly_a (l₁++m₁) (l₂++m₂) = poly_a l₁ l₂ ++ poly_a m₁ m₂.
  Proof. double length induction l₁ l₂ as ? ? ?; simpl; f_equal; auto. Qed.

  Fact is_last_poly_a__length l m a b :
      ⌊l⌋ = ⌊m⌋
    → is_last a l
    → is_last b m
    → is_last (op_a a b) (l +ₚ m).
  Proof.
    revert m; induction l as [ | x [] IHl ]; intros [ | y [] ]; simpl; try discriminate.
    + now intros _ ?%is_last_inv.
    + intros _ ->%is_last_inv ->%is_last_inv.
      constructor 1 with (l := []).
    + intros ? ?%is_last_inv ?%is_last_inv.
      apply is_last_cons, (IHl (_::_)); auto.
  Qed.
 
  Fact poly_a_neutral l m : poly_zero l → l +ₚ m ∼ₚ m.
  Proof.
    intros H; revert H m.
    induction 1 as [ | ? ? E]; intros []; simpl; auto.
    rewrite <- E; split; auto; ring.
  Qed.

  Hint Resolve poly_a_neutral : core.

  Fact poly_a_poly_zero l m : poly_zero l → poly_zero m → poly_zero (l +ₚ m).
  Proof. 
    induction 1 as [ | x l E ] in m |- *; induction 1; simpl; auto.
    constructor; auto.
    rewrite <- E; ring_simplify; auto.
  Qed.

  Hint Resolve poly_a_poly_zero : core.

  Fact poly_a_comm l m : l +ₚ m ∼ₚ m +ₚ l.
  Proof. revert m; induction l; intros []; simpl; constructor; auto; ring. Qed.

  Fact poly_a_assoc l m k : l +ₚ m +ₚ k ∼ₚ (l +ₚ m) +ₚ k.
  Proof. revert m k; induction l; intros [] []; simpl; constructor; auto; ring. Qed.

  Add Parametric Morphism: poly_a with signature (poly_eq) ==> (poly_eq) ==> (poly_eq) as poly_a_morph.
  Proof.
    intros l; induction l as [ | x l IHl ]; intros [ | y m ]; simpl; auto.
    + intros (E & H1)%poly_zero_inv [ | z k ] [ | u p ]; auto.
      * intros H; apply poly_eq_trans with (1 := H); simpl; split.
        - rewrite <- E; ring.
        - apply poly_zero_inv in H; auto.
      * intros (G & H2); split.
        - rewrite <- E, G; ring.
        - apply poly_eq_trans with (1 := H2); auto.
    + intros (E & H1)%poly_zero_inv [ | z k ] [ | u p ]; auto.
      * intros (F & H2)%poly_zero_inv; simpl; constructor; auto.
        rewrite <- E, <- F; ring.
      * intros (F & H2); constructor; eauto.
        rewrite <- E, F; ring.
    + intros (E & H1) [ | z k ] [ | u p ]; simpl; eauto.
      * intros (F & H2)%poly_zero_inv; split; auto.
        - rewrite <- E, <- F; ring.
        - apply poly_eq_trans with (1 := H1),
                poly_eq_trans with (2 := poly_a_comm _ _); eauto.
      * intros (F & H2)%poly_zero_inv; split; auto.
        - rewrite E, <- F; ring.
        - apply poly_eq_trans with (2 := H1),
                poly_eq_trans with (1 := poly_a_comm _ _); eauto.
      * intros (F & H2); split; auto.
        rewrite E, F; ring.
  Qed.

  (** Scalar product 
           a.[b₀;...;bₙ] = [a.b₀;...;a.bₙ] *)
  Definition poly_s a l := map (fun x => a *ᵣ x) l.

  Fact poly_s_length a l : ⌊poly_s a l⌋ = ⌊l⌋.
  Proof. apply length_map. Qed.

  Fact poly_s_neutral l : poly_s 1ᵣ l ∼ₚ l.
  Proof. induction l; simpl; constructor; auto; ring. Qed.

  Fact poly_s_poly_zero_r a l : poly_zero l → poly_zero (poly_s a l).
  Proof. induction 1 as [ | ? ? E ]; simpl; constructor; auto; rewrite <- E; ring. Qed.

  Hint Resolve poly_s_neutral poly_s_poly_zero_r : core.

  Add Parametric Morphism: poly_s with signature (req) ==> (poly_eq) ==> (poly_eq) as poly_s_morph.
  Proof.
    intros a b Hab.
    induction 1 as [ | | ? ? ? ? E ] using poly_eq_ind; simpl; eauto; split; auto.
    rewrite Hab, E; auto.
  Qed.

  Fact poly_s_poly_zero_l a l : 0ᵣ ∼ᵣ a → poly_s a l ∼ₚ [].
  Proof. intros <-; apply poly_eq_sym; induction l; simpl; constructor; auto; ring. Qed.

  Fact poly_s_poly_a_distr a l m : poly_s a (l +ₚ m) ∼ₚ poly_s a l +ₚ poly_s a m.
  Proof. revert m; induction l; intros []; simpl; auto; split; auto; ring. Qed.

  Fact poly_s_comp a b l : poly_s (a *ᵣ b) l ∼ₚ poly_s a (poly_s b l).
  Proof. induction l; simpl; constructor; auto; ring. Qed.

  Reserved Notation "l *ₚ m" (at level 28, right associativity, format "l  *ₚ  m").

  (** Definition using the identities 
      - 0*m = m
      - (x+Xl)*m = x*m + X(lm) *)
  Fixpoint poly_m (l m : poly) : poly :=
    match l with
    | []   => []
    | x::l => poly_s x m +ₚ (0ᵣ::l *ₚ m)
    end
  where "l *ₚ m" := (poly_m l m).

  Fact poly_m_poly_zero_r l m : poly_zero m → poly_zero (l *ₚ m).
  Proof. revert m; induction l; simpl; auto. Qed.

  Hint Resolve poly_m_poly_zero_r : core.

  (* This one involves a stronger induction.
     This is a bit odd *)
  Lemma poly_m_comm l m : l *ₚ m ∼ₚ m *ₚ l.
  Proof.
    induction on l m as IH with measure (@length R l + @length R m).
    revert l m IH; intros [ | x l ] [ | y m ] IH; simpl; constructor; auto; try ring.
    rewrite IH; simpl; try lia.
    rewrite poly_a_assoc,
           (poly_a_comm (poly_s x _)),
         <- poly_a_assoc.
    apply poly_a_morph; auto.
    rewrite <- IH; simpl; try lia.
    change (poly_a (poly_s x m) (un_a :: poly_m l m))
      with (poly_m (x::l) m).
    apply IH; simpl; lia.
  Qed.

  Fact poly_zero_poly_m l m : poly_zero l → poly_zero (l *ₚ m).
  Proof.
    intros H; revert H m.
    induction 1 as [ | x l E H IH ]; intros m; simpl; auto.
    rewrite <- E, poly_s_poly_zero_l; try ring.
    now constructor.
  Qed.

  Hint Resolve poly_zero_poly_m : core.

  Fact poly_eq_poly_m l m k : l ∼ₚ m → l *ₚ k ∼ₚ m *ₚ k.
  Proof.
    induction 1 as [ | | x l y m E IH ] using poly_eq_ind; auto.
    simpl; rewrite E.
    apply poly_a_morph; auto.
    apply cons_morph; auto; ring.
  Qed.

  Add Parametric Morphism: poly_m with signature (poly_eq) ==> (poly_eq) ==> (poly_eq) as poly_m_morph.
  Proof.
    intros l m H1 k p H2.
    rewrite poly_eq_poly_m with (1 := H1),
           (poly_m_comm m),
            poly_eq_poly_m with (1 := H2),
           (poly_m_comm p); auto.
  Qed.

  Fact poly_s_poly_m_assoc a l m : (poly_s a l) *ₚ m ∼ₚ poly_s a (l *ₚ m).
  Proof.
    induction l; simpl; auto.
    rewrite poly_s_poly_a_distr.
    apply poly_a_morph; simpl; [ | split; auto; ring ].
    apply poly_s_comp.
  Qed. 

  Fact poly_m_neutral l m : m ∼ₚ [1ᵣ] → m *ₚ l ∼ₚ l.
  Proof.
    intros ->.
    induction l; simpl; constructor; auto; try ring.
    rewrite poly_a_comm, poly_a_neutral; auto.
  Qed.

  Fact poly_m_poly_a_distr k l m : k *ₚ (l +ₚ m) ∼ₚ k *ₚ l +ₚ k *ₚ m.
  Proof.
    revert l m; induction k as [ | x k IH ]; intros l m; simpl; auto.
    rewrite !poly_s_poly_a_distr, <- !poly_a_assoc.
    apply poly_a_morph; auto.
    rewrite poly_a_comm, IH.
    setoid_replace (@un_a R) with (@op_a R un_a un_a) at 1 by ring.
    change (op_a un_a un_a :: k *ₚ l +ₚ k *ₚ m) with ((un_a::k *ₚ l) +ₚ (un_a::k *ₚ m)).
    rewrite <- poly_a_assoc.
    apply poly_a_morph; auto.
    apply poly_a_comm.
  Qed.

  Fact cons_un_a_poly_m l m : (0ᵣ::l) *ₚ m ∼ₚ 0ᵣ::l *ₚ m.
  Proof. induction l; simpl; rewrite poly_s_poly_zero_l; auto. Qed.

  Fact poly_m_assoc l m k : l *ₚ (m *ₚ k) ∼ₚ (l *ₚ m) *ₚ k.
  Proof. 
    revert m k; induction l as [ | x l IH ]; intros m k; simpl; auto.
    rewrite (poly_m_comm (_ +ₚ _)  k),
             poly_m_poly_a_distr,
           !(poly_m_comm k).
    apply poly_a_morph.
    + rewrite poly_s_poly_m_assoc; auto.
    + rewrite IH, cons_un_a_poly_m; auto.
  Qed.

  Definition poly_i := poly_s (iv_a 1ᵣ).

  Fact poly_i_length l : ⌊poly_i l⌋ = ⌊l⌋.
  Proof. apply poly_s_length. Qed.

  Theorem poly_is_ring : @ring_theory poly [] [un_m] poly_a poly_m (λ l m, poly_a l (poly_i m)) poly_i poly_eq.
  Proof.
    constructor.
    + intro; apply poly_a_neutral; auto.
    + intros; apply poly_a_comm.
    + intros; apply poly_a_assoc.
    + intro; apply poly_m_neutral; auto.
    + intros; apply poly_m_comm.
    + intros; apply poly_m_assoc.
    + intros l m k.
      rewrite (poly_m_comm _ k),
               poly_m_poly_a_distr,
             !(poly_m_comm k); auto.
    + reflexivity.
    + intros l.
      apply poly_eq_sym; simpl.
      induction l; simpl; constructor; auto; ring.
  Qed.

  (* Construction of the polynomial ring R[X] is finished 
     but we need to establish its initiality to confirm
     that we have built the "right" ring, see below. *)

  Definition poly_ring : ring.
  Proof.
    exists poly [] poly_a poly_i [un_m] poly_m poly_eq.
    + constructor; eauto.
    + apply poly_is_ring.
    + constructor.
      * intros ? ? ? ? ? ?; apply poly_a_morph; auto.
      * intros ? ? ? ? ? ?; apply poly_m_morph; auto.
      * intros ? ? ?; apply poly_s_morph; auto.
  Defined.

  Add Ring poly_ring : (is_ring poly_ring).

  (* Now we establish the eliminating of the
     head coefficient by linear combination,
     which is critical in the HBT *)

  Fact poly_shift_poly_m n q :
      repeat 0ᵣ n++q ∼ₚ (repeat 0ᵣ n++[1ᵣ]) *ₚ q.
  Proof.
    induction n as [ | n IHn ].
    + simpl; rewrite poly_s_neutral, poly_a_comm, poly_a_neutral; auto.
    + simpl repeat; simpl app.
      rewrite cons_un_a_poly_m, IHn; auto.
  Qed.

  Fact poly_shift_scal a n p :
      (repeat 0ᵣ n ++ [a]) *ₚ p ∼ₚ repeat 0ᵣ n ++ poly_s a p.
  Proof.
    induction n as [ | n IHn ].
    + simpl; rewrite poly_a_comm, poly_a_neutral; auto.
    + simpl repeat; simpl app; simpl poly_m.
      rewrite poly_s_poly_zero_l, poly_a_neutral; auto.
      apply cons_morph; auto.
  Qed.
 
  Fact poly_zero_repeat n x : 0ᵣ ∼ᵣ x → poly_zero (repeat x n).
  Proof. intro; induction n; simpl; auto. Qed.

  Hint Resolve poly_zero_repeat : core.

  (* Elimination of the head coefficient:
     given a linear combination x of their head coefficients,
     we can form a linear combination the polynomials q₁,...,qₙ
     with head being x and of arbitrary length/degree provided
     it is greater than (all) the degrees of q₁,...,qₙ:

       if * the "degrees" ⌊q₁⌋,...,⌊qₙ⌋ are lesser than 1+d
          * [a₁;...;aₙ] are the head coefficients of [q₁;...;qₙ]
          * x is a linear combination of a₁;...;aₙ (in R)
       then there is a polynomial p with
          * ⌊p⌋ = 1+d
          * x is the head coefficient of p
          * p is a linear combination of q₁,...,qₙ (in poly R)
 
       Idea, multiply/shift each qᵢ with i in [1;...;n]
       so that the degre matches 1+d and use the same
       coefficients as the original linear combination

        if x = r₁a₁ + ... + rₙaₙ then
           p = r₁q₁.Xᵖ¹ + ... + rₙqₙ.Xᵖⁿ 

        where pᵢ = 1+d-⌊qᵢ⌋ for i in [1;...;n] *)

  Lemma lc_lead_coef d (a : list R) x (q : list poly_ring) :
      lc a x
    → Forall2 is_last a q
    → Forall (λ l, ⌊l⌋ ≤ 1+d) q
    → ∃ p y, ⌊p⌋ = 1+d ∧ is_last y p ∧ x ∼ᵣ y ∧ lc q p.
  Proof.
    induction 1 as [ x H1 | a x l c r H1 H2 IH2 ] in q |- *.
    + intros ->%Forall2_nil_inv_l _.
      exists (repeat un_a d++[x]), x; repeat split; auto.
      * rewrite length_app, repeat_length; simpl; lia.
      * constructor 1.
        simpl.
        apply Forall_app.
        rewrite <- H1; simpl; auto.
    + intros (_ & q' & [u] & H3 & ->)%Forall2_cons_inv_l
             (H4 & H5)%Forall_cons_iff.
      destruct (IH2 _ H3 H5) as (p & y & G1 & G2 & G3 & G4).
      exists ((repeat un_a (d-⌊u⌋) ++ (poly_s a (u++[x]))) +ₚ p), (op_a (op_m a x) y).
      assert (⌊repeat un_a (d-⌊u⌋) ++ poly_s a (u ++ [x])⌋ = 1+d) as E.
      1:{ rewrite length_app, poly_s_length, repeat_length.
          rewrite length_app in H4 |- *; simpl in *; lia. }
      repeat split.
      * rewrite poly_a_length, E; lia.
      * apply is_last_poly_a__length; auto.
        - rewrite E; auto.
        - apply is_last_app, is_last_map; auto.
      * rewrite <- H1, <- G3; ring.
      * constructor 2 with (repeat un_a (d-⌊u⌋)++[a]) p; auto.
        unfold op_a, op_m, req; simpl.
        rewrite poly_shift_scal; auto.
  Qed.

  Theorem update_lead_coef (a : list R) x v p :
      lc a x
    → Forall2 is_last a v
    → Forall (λ q, ⌊q⌋ ≤ 1+⌊p⌋) v
    → ∃q : poly_ring, ⌊q⌋ ≤ ⌊p⌋ ∧ update (q::v) ((p++[x])::v).
  Proof.
    intros H1 H2 H3.
    destruct lc_lead_coef
      with (1 := H1) (2 := H2) (3 := H3)
      as (q & y & G1 & G2 & G3 & G4).
    destruct G2 as [q].
    rewrite length_app in G1; simpl in G1.
    exists (poly_a p (poly_i q)).
    assert (⌊p +ₚ poly_i q⌋ = ⌊p⌋) as E.
    1: rewrite poly_a_length, poly_i_length; lia.
    split; try lia.
    constructor 1 with (1 := G4).
    unfold op_a; simpl.
    rewrite <- (app_nil_r (p +ₚ _)),
             poly_a_app__length; try lia.
    apply poly_eq_app__length; simpl; auto.
    + rewrite !poly_a_length, poly_i_length; lia.
    + change ((@op_a poly_ring p (@iv_a poly_ring q)) +ᵣ q ∼ᵣ p).
      ring.
  Qed.

  (** Now we show that initiality of R[X], that it is
      the initial object in the category of pointed
      rings embedding R. *)

  Definition poly_unknown : poly_ring := [0ᵣ;1ᵣ].
  Definition poly_embed (x : R) := [x].
  
  Notation 𝓧 := poly_unknown.
  Notation φ := poly_embed. 

  Fact poly_embed_homo : @ring_homo R poly_ring φ.
  Proof.
    split right; auto.
    + simpl; constructor; auto.
    + simpl; constructor; auto; ring.
  Qed.

  Fact poly_m_poly_unknown l : 𝓧 *ₚ l ∼ₚ 0ᵣ::l.
  Proof.
    simpl.
    rewrite poly_s_poly_zero_l; auto.
    simpl; split; auto.
    rewrite poly_a_comm, poly_s_neutral.
    rewrite poly_zero_left with (l := [@un_a R]); auto.
  Qed.

  Section poly_ring_rect.

    Variables (P : poly_ring → Type)
              (HP0 : ∀ p q, p ∼ᵣ q → P p → P q)
              (HP1 : P 𝓧)
              (HP2 : ∀ x, P (φ x))
              (HP3 : ∀ p q, P p → P q → P (p +ᵣ q))
              (HP4 : ∀ p q, P p → P q → P (p *ᵣ q)).

    Theorem poly_ring_rect p : P p.
    Proof.
      induction p as [ | x l IHl ].
      + apply HP0 with [un_a].
        * constructor; auto.
        * apply HP2.
      + apply HP0 with (poly_embed x +ₚ poly_unknown *ₚ l); auto.
        rewrite poly_m_poly_unknown.
        simpl; split; auto; ring.
    Qed.

  End poly_ring_rect.

  Section poly_extends.

    Variables (K : ring)
              (f : R → K) (Hf : ring_homo f)
              (k : K).

    Add Ring K_is_ring : (is_ring K).

    (* We proceed by induction on the list, ie
       the canonical repr. of the polynomial *) 
    Fixpoint poly_extends (l : poly_ring) : K :=
      match l with
      | []   => 0ᵣ
      | x::l => f x +ᵣ k *ᵣ (poly_extends l)
      end.

    Notation ψ := poly_extends.

    Add Parametric Morphism: ψ with signature (poly_eq) ==> (req) as poly_extends_is_morph.
    Proof.
      apply poly_eq_ind.
      + intro m; induction m; auto.
        intros (E & ?%IHm)%Forall_cons_iff; simpl; auto.
        rewrite <- H; simpl.
        apply Hf in E.
        rewrite <- E, ring_homo_un_a; auto; ring.
      + intros l; induction l; simpl; auto.
        intros (E%Hf & ?%IHl)%Forall_cons_iff.
        rewrite <- E, H, ring_homo_un_a; simpl; auto; ring.
      + intros x l y m; simpl.
        intros ->%Hf ->; auto.
    Qed.

    Fact poly_extends_poly_a l m : ψ (l +ₚ m) ∼ᵣ ψ l +ᵣ ψ m.
    Proof.
      double list induction l m as x y IH.
      + simpl; ring. 
      + rewrite poly_a_comm; simpl; ring.
      + simpl; rewrite IH.
        destruct Hf as (_ & H2 & _).
        rewrite H2; ring.
    Qed.

    Fact poly_extends_poly_s a l : ψ (poly_s a l) ∼ᵣ f a *ᵣ ψ l.
    Proof.
      destruct Hf as (_ & _ & Hf3 & _).
      induction l as [ | x l IHl ]; simpl.
      + ring.
      + rewrite Hf3, IHl; ring.
    Qed.

    Fact poly_extends_un_m : ψ [1ᵣ] ∼ᵣ 1ᵣ.
    Proof.
      destruct Hf as (_ & _ & _ & H).
      simpl; rewrite H; ring.
    Qed.

    (* This one is easier to prove by induction on the
       (non-canonical) ring structure of l, rather the canonical list structure *)
    Lemma poly_extends_poly_m l m : ψ (l *ₚ m) ∼ᵣ ψ l *ᵣ ψ m.
    Proof.
      destruct Hf as (Hf1 & Hf2 & Hf3 & Hf4).
      revert m.
      induction l as 
        [ p q E | |
        | p q IHp IHq 
        | p q IHp IHq ] using poly_ring_rect; intros m.
      + now rewrite <- E.
      + simpl poly_m.
        rewrite poly_extends_poly_a.
        unfold poly_unknown; simpl.
        rewrite poly_s_poly_zero_l; auto; simpl.
        rewrite Hf4, poly_extends_poly_a; simpl.
        rewrite ring_homo_un_a with (1 := Hf).
        rewrite poly_s_neutral.
        ring.
      + unfold poly_embed; simpl.
        rewrite poly_extends_poly_a.
        rewrite poly_extends_poly_s.
        simpl.
        rewrite ring_homo_un_a with (1 := Hf).
        ring.
      + rewrite poly_extends_poly_a.
        rewrite poly_m_comm, 
                poly_m_poly_a_distr,
              !(poly_m_comm m).
        rewrite poly_extends_poly_a, IHp, IHq; ring.
      + unfold op_m at 1; simpl.
        rewrite <- poly_m_assoc, IHp, IHq, IHp; ring.
    Qed.

    Theorem poly_extends_homo : ring_homo ψ.
    Proof.
      split right; auto.
      + exact poly_extends_is_morph.
      + exact poly_extends_poly_a.
      + exact poly_extends_poly_m.
      + exact poly_extends_un_m.
    Qed.

    Theorem poly_extends_unknown : ψ 𝓧 ∼ᵣ k.
    Proof.
      destruct Hf as (_ & _ & _ & Hf4).
      unfold poly_extends; simpl.
      rewrite Hf4, ring_homo_un_a with (1 := Hf).
      ring.
    Qed.

    Theorem poly_extends_poly_embed x : ψ (φ x) ∼ᵣ f x.
    Proof. simpl; ring. Qed.

    Hypothesis (h : poly_ring → K)
               (h_homo : ring_homo h)
               (h_k : h 𝓧 ∼ᵣ k)
               (h_embed : ∀x, h (φ x) ∼ᵣ f x).

    (* By induction on the ring structure of p *)
    Theorem poly_extends_uniq p : h p ∼ᵣ ψ p.
    Proof.
      destruct Hf as (Hf1 & Hf2 & Hf3 & Hf4).
      destruct h_homo as (Hh1 & Hh2 & Hh3 & Hh4). 
      induction p as 
        [ p q E | | x
        | p q IHp IHq 
        | p q IHp IHq ] using poly_ring_rect.
      + now rewrite <- Hh1 with (1 := E),
                <- poly_extends_is_morph with (1 := E).
      + rewrite h_k, poly_extends_unknown; auto.
      + rewrite poly_extends_poly_embed, h_embed; ring.
      + rewrite Hh2, IHp, IHq, poly_extends_poly_a; ring.
      + rewrite Hh3, IHp, IHq, poly_extends_poly_m; ring.
    Qed.

  End poly_extends.

  (** We show that the poly_ring extension satisfies its
      characteristic property. *)
  Theorem poly_ring_correct :
    is_poly_ring R 
      {| pe_ring := poly_ring;
         pe_embed := poly_embed;
         pe_embed_homo := poly_embed_homo;
         pe_point := poly_unknown |}.
  Proof.
    intros Tx.
    split; simpl.
    + exists (poly_extends Tx (pe_embed Tx) (pe_point Tx)); split right.
      * apply poly_extends_homo, pe_embed_homo.
      * destruct Tx as [ Tx f Hf x ]; simpl.
        rewrite ring_homo_un_a, ring_homo_un_m, ring_op_m_un_a, ring_op_a_un_a, ring_un_a_op_a, ring_op_m_un_m; auto.
      * intro; simpl; rewrite ring_op_m_un_a, ring_op_a_un_a; auto.
    + intros al be (H1 & H2 & H3) (H4 & H5 & H6) p.
      generalize (pe_embed_homo Tx).
      intro; rewrite poly_extends_uniq with (h := be); eauto.
      apply poly_extends_uniq; auto.
  Qed.

End polynomial_ring.

Arguments poly_unknown {_}.
Arguments poly_embed {_}.
Arguments poly_extends {_ _}.

Check poly_extends_homo.
Check poly_extends_unknown.
Check poly_extends_poly_embed.
Check poly_extends_uniq.
Check poly_ring_correct.
Check poly_ring_unique.

