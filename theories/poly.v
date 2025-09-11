(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Wellfounded Setoid Utf8.

Require Import utils ring ideal category measure.

Import ListNotations.

#[local] Hint Constructors is_last : core.

Section polynomial_ring.

  Variable (𝓡 : ring).

  Add Ring 𝓡_is_ring : (is_ring 𝓡).

  Notation poly := (list 𝓡).

  Implicit Types (x : 𝓡) (l : poly).

  (* We use this non-canonical representation
     of polynomials:
     a₀+...+aₙXⁿ = [a₀;...;aₙ]
     X = 0+1.X = [0ᵣ;1ᵣ] 

     Notice that several representations might
     be equivalent for the same polynomial, ie
         [] ~ₚ [0ᵣ] ~ₚ [0ᵣ;...;0ᵣ]

     Hence polynomials are equivalence classes
     of representations.

     Representations have a computable length but 
     the notion of degree of a polynomial is not 
     computable unless one can computably decide 
     inequality over the base ring R

     Indeed, degree [a₀;...;aₙ] < n iff
     aₙ ~ᵣ 0ᵣ 

     degree [a -ᵣ b] is < 0 iff a ~ᵣ b *)

  Notation poly_zero := (Forall (req un_a)).

  Fact poly_zero_inv l :
      poly_zero l
    → match l with
      | []   => True
      | x::m => 0ᵣ ∼ᵣ x ∧ poly_zero m
      end.
  Proof. now intros []. Qed.

  Reserved Notation "l ∼ₚ m" (at level 70, no associativity, format "l  ∼ₚ  m").

  (* Equivalence between two poly *)
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

    (* Induction principle for the poly-equivalence *)

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

  Fact poly_eq_app__length l₁ l₂ m₁ m₂ :
     ⌊l₁⌋ = ⌊l₂⌋ → l₁ ∼ₚ l₂ → m₁ ∼ₚ m₂ → l₁++m₁ ∼ₚ l₂++m₂.
  Proof.
    double length induction l₁ l₂ as x y IH; simpl; auto.
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
    + intros (<- & H)%poly_zero_inv []; constructor; auto.
      revert H; now apply poly_zero_poly_eq_closed.
    + intros []%poly_zero_inv []%poly_zero_inv; split; eauto.
    + intros (E & ?) (? & G)%poly_zero_inv; constructor; auto.
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
      by pattern matching on l and m. Notice that they
      might have unequal length. If one of those is the empty 
      list, the other one serves as the result *)
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

  (* The value of the head coefficient, assuming equal length *)
  Fact is_last_poly_a__length l m a b :
      ⌊l⌋ = ⌊m⌋
    → is_last a l
    → is_last b m
    → is_last (a +ᵣ b) (l +ₚ m).
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

  (** Before we define multiplication of representations
      of polynomials, we define the scalar product *)

  (* Scalar product: a.[b₀;...;bₙ] = [a.b₀;...;a.bₙ] *)
  Definition poly_s a l := map (λ x, a *ᵣ x) l.

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

  (** We can now define multiplication *)

  Reserved Notation "l *ₚ m" (at level 28, right associativity, format "l  *ₚ  m").

  (** Definition using the identities 
                  0*m = 0
        and  (x+Xl)*m = x*m + X(lm) *)
  Fixpoint poly_m (l m : poly) : poly :=
    match l with
    | []   => []
    | x::l => poly_s x m +ₚ (0ᵣ::l *ₚ m)
    end
  where "l *ₚ m" := (poly_m l m).

  Fact poly_m_poly_zero_r l m : poly_zero m → poly_zero (l *ₚ m).
  Proof. revert m; induction l; simpl; auto. Qed.

  Hint Resolve poly_m_poly_zero_r : core.

  (* This one involves a mutual induction on l and m *)
  Lemma poly_m_comm l m : l *ₚ m ∼ₚ m *ₚ l.
  Proof.
    revert l m; apply list_mutual_rect; simpl; auto.
    intros x l y m IH0 IH1 IH2; simpl; constructor; try ring.
    now rewrite <- IH1, IH2, IH0, !poly_a_assoc, (poly_a_comm (poly_s x m)).
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
    setoid_replace (@un_a 𝓡) with (@op_a 𝓡 un_a un_a) at 1 by ring.
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

  (** The polynomial inverse for addition *)

  Definition poly_i := poly_s (iv_a 1ᵣ).

  Fact poly_i_length l : ⌊poly_i l⌋ = ⌊l⌋.
  Proof. apply poly_s_length. Qed.
  
  Fact poly_i_app l m : poly_i (l++m) = poly_i l++poly_i m.
  Proof. apply map_app. Qed.

  Fact poly_shift_poly_m n q : repeat 0ᵣ n++q ∼ₚ (repeat 0ᵣ n++[1ᵣ]) *ₚ q.
  Proof.
    induction n as [ | n IHn ].
    + simpl; rewrite poly_s_neutral, poly_a_comm, poly_a_neutral; auto.
    + simpl repeat; simpl app.
      rewrite cons_un_a_poly_m, IHn; auto.
  Qed.

  Fact poly_shift_scal a n p : (repeat 0ᵣ n++[a]) *ₚ p ∼ₚ repeat 0ᵣ n++poly_s a p.
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

  (** Construction of the polynomial ring R[X] is finished
      but we need to establish its initiality to confirm
      that we have built the "right" pointed extension 
      of ring R, ie, the initial one in this category; see below. 

      But before that, we show the critical theorem
      "update_lead_coef" that allows to combine
      head coefficients of polynomials representations
      to diminish the length by updating *)

  Add Ring poly_ring_s_ring : (is_ring poly_ring).

  (* Now we establish the eliminating of the
     head coefficient by linear combination,
     which is critical in the HBT *)

  (* Linear combination of head coefficients:

       if * the lengths ⌊m₁⌋,...,⌊mₙ⌋ are lesser than d+1
          * m₁,...,mₙ have head coefficients h₁,...,hₙ  (in poly_ring)
          * x is a linear combination of h₁,...,hₙ      (in R)
       then there is a representation of a polynomial p st
          * p is a linear combination of m₁,...,mₙ      (in poly_ring)
          * the length ⌊p⌋ of p is d+1
          * x is the head coefficient of p
 
     Idea: multiply with Xʰ/shift each mᵢ with i in 1,...,n
           so that the degre matches d+1 and use the same
           coefficients as the original linear combination, ie

            if x = r₁h₁ + ... + rₙhₙ then
               p := r₁m₁.Xʰ¹ + ... + rₙmₙ.Xʰⁿ 

               where hᵢ = d+1-⌊mᵢ⌋ for i in 1,...,n *)

  Lemma lc_lead_coef d (h : list 𝓡) x (m : list poly_ring) :
      lc h x                       (* x is a linear combination of [h₁;...;hₙ] *)
    → Forall2 is_last h m          (* [h₁;...;hₙ] are the heads of [m₁;...;mₙ] *) 
    → Forall (λ q, ⌊q⌋ ≤ d+1) m    (* d+1 is greater the all the length ⌊m₁⌋,...,⌊mₙ⌋ *)
    → ∃ p y,
         ⌊p⌋ = d+1                 (* p has length d+1 *)
       ∧ is_last y p ∧ x ∼ᵣ y      (* p has head y ~ᵣ x *)
       ∧ lc m p                    (* p is a linear combination of [m₁;...;mₙ] *)
    .
  Proof.
    induction 1 as [ x H1 | a x l c r H1 H2 IH2 ] in m |- *.
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
      assert (⌊repeat un_a (d-⌊u⌋) ++ poly_s a (u++[x])⌋ = d+1) as E.
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

  Theorem update_lead_coef (p : poly_ring) (m : list poly_ring) :
      Forall (λ q, ⌊q⌋ ≤ ⌊p⌋) m
    → (∃ x h, is_last x p ∧ Forall2 is_last h m ∧ lc h x)
    → ∃q : poly_ring, ⌊q⌋ < ⌊p⌋ ∧ lc m (p −ᵣ q).
  Proof.
    intros H3 (x & h & Hp & H2 & H1).
    induction Hp as [ p ].
    destruct lc_lead_coef
      with (1 := H1) (2 := H2) (d := ⌊p⌋)
      as (q & y & G1 & G2 & G3 & G4).
    1: revert H3; apply Forall_impl; intro; rewrite length_app; simpl; lia.
    destruct G2 as [q].
    rewrite length_app in G1; simpl in G1.
    exists ((p : poly_ring) +ᵣ (poly_i q)).
    assert (⌊(p : poly_ring) +ᵣ poly_i q⌋ = ⌊p⌋) as E.
    1: rewrite poly_a_length, poly_i_length; lia.
    split; [ simpl in *; rewrite length_app; simpl; lia | ].
    revert G4; apply lc_req_closed.
    unfold op_a; simpl.
    rewrite <- (app_nil_r (poly_i _)).
    rewrite poly_a_app__length.
    2: now rewrite poly_i_length.
    apply poly_eq_app__length; auto.
    + rewrite poly_a_length, poly_i_length; simpl in E; rewrite E; lia.
    + change ((q : poly_ring) ∼ᵣ (p : poly_ring) −ᵣ ((p : poly_ring) −ᵣ (q : poly_ring))); ring.
    + simpl; split; auto.
  Qed.

  (** Now we show that initiality of R[X], that it is
      the initial object in the category of pointed
      extensions of the ring R. *)

  Definition poly_unknown : poly_ring := [0ᵣ;1ᵣ].
  Definition poly_embed (x : 𝓡) := [x].

  Notation X := poly_unknown.
  Notation φ := poly_embed. 

  Fact poly_embed_homo : @ring_homo 𝓡 poly_ring φ.
  Proof.
    split right; auto.
    + simpl; constructor; auto.
    + simpl; constructor; auto; ring.
  Qed.

  Fact poly_m_poly_unknown l : X *ₚ l ∼ₚ 0ᵣ::l.
  Proof.
    simpl.
    rewrite poly_s_poly_zero_l; auto.
    simpl; split; auto.
    rewrite poly_a_comm, poly_s_neutral.
    rewrite poly_zero_left with (l := [@un_a 𝓡]); auto.
  Qed.

  Section poly_ring_rect.

    Variables (P : poly_ring → Type)
              (HP0 : ∀ p q, p ∼ᵣ q → P p → P q)
              (HP1 : P X)
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

    Variables (𝓚 : ring)
              (f : 𝓡 → 𝓚) (Hf : ring_homo f)
              (k : 𝓚).

    Add Ring 𝓚_is_ring : (is_ring 𝓚).

    (* We proceed by induction on the list, ie
       the canonical repr. of the polynomial *) 
    Fixpoint poly_extends (l : poly_ring) : 𝓚 :=
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

    Theorem poly_extends_unknown : ψ X ∼ᵣ k.
    Proof.
      destruct Hf as (_ & _ & _ & Hf4).
      unfold poly_extends; simpl.
      rewrite Hf4, ring_homo_un_a with (1 := Hf).
      ring.
    Qed.

    Theorem poly_extends_poly_embed x : ψ (φ x) ∼ᵣ f x.
    Proof. simpl; ring. Qed.

    Hypothesis (h : poly_ring → 𝓚)
               (h_homo : ring_homo h)
               (h_k : h X ∼ᵣ k)
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
    is_poly_ring 𝓡
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

