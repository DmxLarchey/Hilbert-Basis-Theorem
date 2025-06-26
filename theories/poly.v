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

  Definition is_polynomial_ring (Rx : ring) (φ : R → Rx) (x : Rx) :=
      ring_homo φ
   ∧ (∀ (T : ring) (γ : R → T) (t : T),
          ring_homo γ 
       → (∃ α : Rx → T, ring_homo α ∧ α x ∼ᵣ t ∧ ∀r, α (φ r) ∼ᵣ γ r)
       ∧ (∀ α β : Rx → T,
              ring_homo α → α x ∼ᵣ t → (∀r, α (φ r) ∼ᵣ γ r)
            → ring_homo β → β x ∼ᵣ t → (∀r, β (φ r) ∼ᵣ γ r)
            → ∀p, α p ∼ᵣ β p)).

  (** unicity up to isomorphism *)

  Variables (Rx₁ : ring) (φ₁ : R → Rx₁) (x₁ : Rx₁)
            (Rx₂ : ring) (φ₂ : R → Rx₂) (x₂ : Rx₂).

  Add Ring Rx1_ring : (is_ring Rx₁).
  Add Ring Rx2_ring : (is_ring Rx₂).

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

  Theorem poly_ring_unique :
       is_polynomial_ring Rx₁ φ₁ x₁
     → is_polynomial_ring Rx₂ φ₂ x₂
     → ∃ (f : Rx₁ → Rx₂) (g : Rx₂ → Rx₁),
         ring_isomorphism f g ∧ f x₁ ∼ᵣ x₂ ∧ g x₂ ∼ᵣ x₁.
  Proof.
    intros (H1 & H2) (H3 & H4).
    destruct (H2 _ _ x₂ H3) as ((f & Hf1 & Hf2 & Hf3) & G1).
    destruct (H4 _ _ x₁ H1) as ((g & Hg1 & Hg2 & Hg3) & G2).
    exists f, g; repeat (split; auto).
    + intros p.
      apply (proj2 (H4 _ _ x₂ H3) (λ p, f (g p)) (λ p, p)); auto.
      * rewrite <- Hf2 at 2; now apply Hf1.
      * intro; rewrite <- Hf3 at 2; apply Hf1; auto.
    + intros p.
      apply (proj2 (H2 _ _ x₁ H1) (λ p, g (f p)) (λ p, p)); auto.
      * rewrite <- Hg2 at 2; now apply Hg1.
      * intro; rewrite <- Hg3 at 2; apply Hg1; auto.
  Qed.

End characteristic_property_of_the_polynomial_ring.

Section characteristic_property_of_multivariate_rings.

  (** We define what it is to be isomorphic to R{X}
      which is the ring of polynomials over R with
      indeterminates in the type X *)

  Variables (X : Type) (R : ring).

  Add Ring R_is_ring : (is_ring R).

  (** This is the initiality property for the polynomial ring:
      it is initial in the category of pointed rings which extend R *)

  Definition is_multivariate_ring (RX : ring) (φ : R → RX) (f : X → RX) :=
      ring_homo φ
   ∧ (∀ (T : ring) (γ : R → T) (g : X → T),
          ring_homo γ 
       → (∃ α : RX → T, ring_homo α ∧ (∀k, α (f k) ∼ᵣ g k) ∧ ∀r, α (φ r) ∼ᵣ γ r)
       ∧ (∀ α β : RX → T,
              ring_homo α → (∀k, α (f k) ∼ᵣ g k) → (∀r, α (φ r) ∼ᵣ γ r)
            → ring_homo β → (∀k, β (f k) ∼ᵣ g k) → (∀r, β (φ r) ∼ᵣ γ r)
            → ∀p, α p ∼ᵣ β p)).

  (** unicity up to isomorphism *)

  Variables (RX₁ : ring) (φ₁ : R → RX₁) (f₁ : X → RX₁)
            (RX₂ : ring) (φ₂ : R → RX₂) (f₂ : X → RX₂).

  Add Ring RX1_ring : (is_ring RX₁).
  Add Ring RX2_ring : (is_ring RX₂).

  (** The multivariate ring is unique up to isomorphism *)

  Theorem multivariate_ring_unique :
       is_multivariate_ring RX₁ φ₁ f₁
     → is_multivariate_ring RX₂ φ₂ f₂
     → ∃ (f : RX₁ → RX₂) (g : RX₂ → RX₁),
         ring_isomorphism f g 
       ∧ (∀k, f (f₁ k) ∼ᵣ f₂ k) 
       ∧ (∀k, g (f₂ k) ∼ᵣ f₁ k).
  Proof.
    intros (H1 & H2) (H3 & H4).
    destruct (H2 _ _ f₂ H3) as ((f & Hf1 & Hf2 & Hf3) & G1).
    destruct (H4 _ _ f₁ H1) as ((g & Hg1 & Hg2 & Hg3) & G2).
    exists f, g; repeat (split; auto).
    + intros p.
      apply (proj2 (H4 _ _ f₂ H3) (λ p, f (g p)) (λ p, p)); auto.
      * intros; rewrite <- Hf2 at 2; now apply Hf1.
      * intros; rewrite <- Hf3 at 2; apply Hf1; auto.
    + intros p.
      apply (proj2 (H2 _ _ f₁ H1) (λ p, g (f p)) (λ p, p)); auto.
      * intros; rewrite <- Hg2 at 2; now apply Hg1.
      * intros; rewrite <- Hg3 at 2; apply Hg1; auto.
  Qed.

End characteristic_property_of_multivariate_rings.

(** R[X] is R{unit} *)
Fact poly_ring__multivariate_ring R Rx φ x :
    @is_polynomial_ring R Rx φ x
  → @is_multivariate_ring unit R Rx φ (λ _ : unit, x).
Proof.
  intros (H1 & H2); split; auto.
  intros T ga g Hga.
  destruct (H2 T ga (g tt) Hga)
    as ((al & H3 & H4 & H5) & H6).
  split; eauto.
  exists al; split right; auto.
  now intros [].
Qed.

(** R{U}{V} is R{U+V} *)
Fact multivariate_ring_compose {U V R RU φ f RUV γ g} :
    @is_multivariate_ring U R RU φ f
  → @is_multivariate_ring V RU RUV γ g
  → @is_multivariate_ring (U+V) R RUV (λ x, γ (φ x)) (λ x, match x with inl u => γ (f u) | inr v => g v end).
Proof.
  intros (H1 & H2) (H3 & H4); split; auto.
  intros T ga h Hga.
  destruct (H2 T ga (λ u, h (inl u)))
    as ((al & F1 & F2 & F3) & F4); auto.
  destruct (H4 _ al (λ v, h (inr v)))
    as ((be & G1 & G2 & G3) & G4); auto.
  split.
  + exists be; split right; auto.
    * intros []; auto; rewrite G3, F2; auto.
    * intros; now rewrite G3.
  + intros p q K1 K2 K4 K5 K6 K8 r.
    generalize (λ u, K2 (inl u)) (λ v, K2 (inr v)); clear K2; intros K2 K3.
    generalize (λ u, K6 (inl u)) (λ v, K6 (inr v)); clear K6; intros K6 K7.
    apply G4; auto; apply F4; auto.
Qed.

Definition bijection {U V} (f : U → V) (g : V → U) :=
  (∀v, f (g v) = v)
∧ (∀u, g (f u) = u).

(** if R{U} and V is in bijection with V then R{V} and iso ? 
    to be used to show that R{X}[x] is R{X}{unit} and then R{option X} *)
Fact multivariate_ring_bijection U V f g R RU φ h :
    @bijection U V f g 
  → @is_multivariate_ring U R RU φ h
  → @is_multivariate_ring V R RU φ (λ v, h (g v)).
Proof.
  intros (H1 & H2) (G1 & G2); split; auto.
  intros T ga k Hga.
  destruct (G2 _ _ (fun u => k (f u)) Hga)
    as ((al & F1 & F2 & F3) & F4); split.
  + exists al; split right; auto.
    intro; rewrite F2, H1; auto.
  + clear al F1 F2 F3.
    intros al be P1 P2 P3 P4 P5 P6.
    apply F4; auto.
    * intro; rewrite <- P2, H2; auto.
    * intro; rewrite <- P5, H2; auto.
Qed.

Section list_utils.

  Variables (X : Type).

  Implicit Type l : list X.

  Definition list_repeat x : nat → list X :=
    fix loop n :=
      match n with
      | 0   => []
      | S n => x::loop n
      end.

  Fact list_repeat_length x n : ⌊list_repeat x n⌋ = n.
  Proof. induction n; simpl; f_equal; auto. Qed.

  (** This allows to isolate the lead coefficient of a polynomial
      a₀+...+aₙXⁿ = [a₀;...;aₙ] *)
  Inductive is_last x : list X → Prop :=
    is_last_intro l : is_last x (l++[x]).

  Fact is_last_inv x l :
      is_last x l
    → match l with
      | []   => False
      | y::m => 
        match m with 
        | [] => x = y
        | _  => is_last x m
        end
      end.
  Proof.
    destruct 1 as [ [ | ? l ] ]; simpl; auto.
    destruct l; constructor.
  Qed.

  Fact is_last_cons x y l : is_last x l → is_last x (y::l).
  Proof. intros []; constructor 1 with (l := _::_). Qed.

  Fact is_last_app l r x : is_last x r → is_last x (l++r).
  Proof. intros [ r' ]; rewrite app_assoc; constructor. Qed.

End list_utils.

Arguments list_repeat {_}.

Hint Constructors is_last : core.

Arguments is_last {_}.

Fact is_last_map X Y (f : X → Y) x l :
  is_last x l → is_last (f x) (map f l).
Proof. intros []; rewrite map_app; simpl; auto. Qed.

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
      list_repeat 0ᵣ n++q ∼ₚ (list_repeat 0ᵣ n++[1ᵣ]) *ₚ q.
  Proof.
    induction n as [ | n IHn ].
    + simpl; rewrite poly_s_neutral, poly_a_comm, poly_a_neutral; auto.
    + simpl list_repeat; simpl app.
      rewrite cons_un_a_poly_m, IHn; auto.
  Qed.

  Fact poly_shift_scal a n p :
      (list_repeat 0ᵣ n ++ [a]) *ₚ p ∼ₚ list_repeat 0ᵣ n ++ poly_s a p.
  Proof.
    induction n as [ | n IHn ].
    + simpl; rewrite poly_a_comm, poly_a_neutral; auto.
    + simpl list_repeat; simpl app; simpl poly_m.
      rewrite poly_s_poly_zero_l, poly_a_neutral; auto.
      apply cons_morph; auto.
  Qed.
 
  Fact poly_zero_list_repeat n x : 0ᵣ ∼ᵣ x → poly_zero (list_repeat x n).
  Proof. intro; induction n; simpl; auto. Qed.

  Hint Resolve poly_zero_list_repeat : core.

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
      exists (list_repeat un_a d++[x]), x; repeat split; auto.
      * rewrite length_app, list_repeat_length; simpl; lia.
      * constructor 1.
        simpl.
        apply Forall_app.
        rewrite <- H1; simpl; auto.
    + intros (_ & q' & [u] & H3 & ->)%Forall2_cons_inv_l
             (H4 & H5)%Forall_cons_iff.
      destruct (IH2 _ H3 H5) as (p & y & G1 & G2 & G3 & G4).
      exists ((list_repeat un_a (d-⌊u⌋) ++ (poly_s a (u++[x]))) +ₚ p), (op_a (op_m a x) y).
      assert (⌊list_repeat un_a (d-⌊u⌋) ++ poly_s a (u ++ [x])⌋ = 1+d) as E.
      1:{ rewrite length_app, poly_s_length, list_repeat_length.
          rewrite length_app in H4 |- *; simpl in *; lia. }
      repeat split.
      * rewrite poly_a_length, E; lia.
      * apply is_last_poly_a__length; auto.
        - rewrite E; auto.
        - apply is_last_app, is_last_map; auto.
      * rewrite <- H1, <- G3; ring.
      * constructor 2 with (list_repeat un_a (d-⌊u⌋)++[a]) p; auto.
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
  Theorem poly_ring_correct : is_polynomial_ring R poly_ring poly_embed poly_unknown.
  Proof.
    split.
    + apply poly_embed_homo.
    + intros T ga t Hga; split.
      * exists (poly_extends T ga t); split right.
        - now apply poly_extends_homo.
        - now apply poly_extends_unknown.
        - apply poly_extends_poly_embed.
      * intros al be H1 H2 H3 H4 H5 H6 p.
        rewrite poly_extends_uniq with (h := be); eauto.
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

