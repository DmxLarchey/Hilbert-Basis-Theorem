(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import PeanoNat Lia List Permutation Utf8.

Import ListNotations.

#[global] Notation "l ≈ₚ m" := (@Permutation _ l m) (at level 70).

#[global] Notation "⌊ l ⌋" := (length l) (at level 1, format "⌊ l ⌋").   (* length *)
#[global] Notation "x ∈ l" := (In x l) (at level 70, format "x  ∈  l").  (* membership *)
#[global] Notation "⌞ l ⌟" := (λ x, x ∈ l) (at level 1, format "⌞ l ⌟"). (* carrier of l *)

#[global] Notation "P ⊆₁ Q" := (∀x, P x → Q x) (at level 70).            (* inclusion *)
#[global] Notation "P ⊆₂ Q" := (∀x y, P x y → Q x y) (at level 70).      (* inclusion *)
#[global] Notation "P ≡₁ Q" := (∀x, P x ↔ Q x) (at level 70).            (* equivalence *)

#[global] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

(** Tactic for splitting goal ... |- A₁ ∧ ... ∧ Aₙ *)

Ltac right_split_rec := try (split; [ | right_split_rec ]).
Tactic Notation "split" "right" := right_split_rec.

(** Induction on two lists *)

Section list_double_rect.

  Variables (X : Type)
            (P : list X → list X → Type)
            (HP0 : ∀m, P [] m)
            (HP1 : ∀l, P l [])
            (HP2 : ∀ x l y m, P l m → P (x::l) (y::m)).

  Theorem list_double_rect l m : P l m.
  Proof. revert m; induction l; intros []; eauto. Qed.

End list_double_rect.

Tactic Notation "double" "list" "induction" hyp(l) hyp(m) "as" simple_intropattern(x) simple_intropattern(y) simple_intropattern(IH) :=
  pattern l, m; revert l m; apply list_double_rect;
    [ intros m | intros l | intros x l y m IH ].

Section list_eq_length_rect.

  Variables (X : Type)
            (P : list X → list X → Type)
            (HP0 : P [] [])
            (HP1 : ∀ x l y m, P l m → P (x::l) (y::m)).

  Theorem list_eq_length_rect l m : ⌊l⌋ = ⌊m⌋ → P l m.
  Proof. revert m; induction l; intros []; discriminate || auto. Qed.

End list_eq_length_rect.

Tactic Notation "double" "length" "induction" hyp(l) hyp(m)
  "as" simple_intropattern(x) simple_intropattern(y) simple_intropattern(IH) :=
  let H := fresh
  in intro H; pattern l, m; revert l m H; apply list_eq_length_rect;
    [ | intros x l y m IH ].

(** Finite choice principle on lists *)

#[local] Hint Resolve incl_nil_l incl_cons
               in_eq in_cons incl_tl
               incl_refl incl_tran in_or_app : core.

Section list_choice.

  (** Finite weakly decidable choice over a list
      code duplicated from Kruskal-Finite
        in https://dmxlarchey.github.io/Coq-Kruskal/ *)

  Variables (X : Type) (P Q : X → Prop).

  Fact list_choice l :
      (∀x, x ∈ l → P x ∨ Q x)
    → (∀x, x ∈ l → P x) ∨ ∃ x, x ∈ l ∧ Q x.
  Proof.
    induction l as [ | x l IHl ]; intros Hl.
    + left; now simpl.
    + destruct (Hl x) as []; eauto.
      destruct IHl as [ | (? & []) ]; eauto.
      left; intros ? [ <- | ]; eauto.
  Qed.

End list_choice.

(** Maximum of a list of nat *)

Definition lmax := fold_right Nat.max 0.

Fact lmax_in l x : x ∈ l → x ≤ lmax l.
Proof.
  revert x; rewrite <- Forall_forall.
  induction l as [ | n l IHl ]; simpl; constructor; try lia.
  revert IHl; apply Forall_impl; lia.
Qed.

Fact lmax_find l : l = [] ∨ lmax l ∈ l.
Proof.
  induction l as [ | x l [ -> | IHl ]]; auto; right; simpl.
  + lia.
  + destruct (Nat.max_spec x (lmax l)) as [ (_ & ->) | (_ & ->) ]; auto.
Qed.

(** Reverse finite prefix of a sequence of type f : nat → X
      pfx_rev f n = [f (n-1);...;f 0] *)

Section pfx_rev.

  Variables (X : Type).

  Implicit Type (f : nat → X).

  Definition pfx_rev f :=
    fix loop n :=
      match n with
      | 0   => []
      | S n => f n :: loop n
      end.

  Fact in_pfx_rev f n x : x ∈ pfx_rev f n ↔ ∃k, k < n ∧ f k = x.
  Proof.
    induction n as [ | n IHn ]; simpl.
    + split; [ easy | ]; now intros (? & ? & _).
    + rewrite IHn; split.
      * intros [ <- | (k & ? & <-) ]; [ exists n | exists k ]; split; auto; lia.
      * intros (k & H1 & H2).
        destruct (Nat.eq_dec n k) as [ <- | ]; auto; right; exists k; split; auto; lia.
  Qed.
  
  Fact pfx_rev_ext f g n : (∀i, i < n → f i = g i) → pfx_rev f n = pfx_rev g n.
  Proof.
    induction n as [ | n IHn ]; intros Hn; simpl; auto.
    f_equal.
    + apply Hn; lia.
    + apply IHn; intros; apply Hn; lia.
  Qed.

  Fact pfx_rev_add f a b : pfx_rev f (a+b) = pfx_rev (λ n, f (n+b)) a ++ pfx_rev f b.
  Proof. induction a; simpl; f_equal; auto. Qed.
  
  Fact pfx_rev_S f n : pfx_rev f (1+n) = pfx_rev (λ n, f (1+n)) n ++ [f 0].
  Proof.
    rewrite Nat.add_comm, pfx_rev_add; f_equal; auto.
    apply pfx_rev_ext; intros; f_equal; lia.
  Qed.

End pfx_rev.

Arguments pfx_rev {X}.

(** Inductive predicate for the extends relations between lists *)

Section extends.

  Variables (X : Type).

  Implicit Type (l : list X).

  Inductive extends l : list X → Prop :=
    | extends_intro x : extends l (x::l).

  Hint Constructors extends : core.

  Fact extends_inv l m :
      extends l m
    → match m with
      | []   => False
      | _::m => l = m
      end.
  Proof. now destruct 1. Qed.

  Fact hd_extends {l m} : extends l m → { x : X | m = x::l }.
  Proof.
    destruct m as [ | x m ]; intros H%extends_inv.
    + easy.
    + now exists x; subst.
  Qed.

  (* extends-sequences are sequences of n-prefixes *)
  Fact extends_pfx_rev_init (α : nat → list X) (l₀ : list X) :
      α 0 = l₀ 
    → (∀n, extends (α n) (α (S n)))
    → { ρ | ∀n, α n = pfx_rev ρ n ++ l₀ }.
  Proof.
    intros H1 H2.
    exists (λ n, proj1_sig (hd_extends (H2 n))).
    intros n.
    induction n as [ | n IHn ].
    + now simpl.
    + simpl.
      rewrite <- IHn.
      exact (proj2_sig (hd_extends _)).
  Qed.

  Fact extends_pfx_rev (α : nat → list X) :
      α 0 = [] 
    → (∀n, extends (α n) (α (S n)))
    → { ρ | ∀n, α n = pfx_rev ρ n }.
  Proof.
    intros H1 H2.
    destruct extends_pfx_rev_init 
      with (1 := H1) as (r & Hr); auto.
    exists r; intro; now rewrite Hr, app_nil_r.
  Qed.

End extends.

Arguments extends {X}.
Arguments pfx_rev {X}.
Arguments extends {X}.
Arguments extends_pfx_rev {X}.

(** Extra results for Forall2, ie finitary conjunction over two lists *)

Fact Forall2_right_Forall X Y (P : Y → Prop) (l : list X) m :
    Forall2 (λ _ y, P y) l m ↔ Forall P m ∧ ⌊l⌋ = ⌊m⌋.
Proof.
  split.
  + induction 1 as [ | ? ? ? ? ? ? [] ]; simpl; eauto.
  + intros (H1 & H2); revert H1 l H2.
    induction 1; intros []; simpl; now eauto.
Qed.

Section Forall2_extra.

  Variables (X Y : Type).
  
  Implicit Types (R T : X → Y → Prop).

  Fact reif_Forall2 R l : (∀x, x ∈ l → ∃y, R x y) → ∃m, Forall2 R l m.
  Proof.
    induction l as [ | x l IHl ]; intros Hl.
    + exists nil; constructor.
    + destruct (Hl x); auto.
      destruct IHl; eauto.
  Qed.

  Fact Forall2_conj R T l m : Forall2 (λ x y, R x y ∧ T x y) l m ↔ Forall2 R l m ∧ Forall2 T l m.
  Proof.
    split.
    + induction 1; split; constructor; tauto.
    + intros [H1 H2]; revert H1 H2.
      induction 1 as [ | x ll y mm H1 H2 IH ]; intros H; auto.
      apply Forall2_cons_iff in H; constructor; tauto.
  Qed.

  Fact Forall2_length R l m : Forall2 R l m → ⌊l⌋ = ⌊m⌋.
  Proof. induction 1; simpl; f_equal; auto. Qed.

  Fact Forall2_nil_inv_l R l : Forall2 R [] l → l = [].
  Proof. now inversion 1. Qed.

  Fact Forall2_cons_inv_l R x l m : Forall2 R (x::l) m → { y : _ & { m' | R x y ∧ Forall2 R l m' ∧ m = y::m' } }.
  Proof. 
    intros H; destruct m as [ | y m ].
    + exfalso; inversion H.
    + apply Forall2_cons_iff in H as []; eauto.
  Qed.
  
  Fact Forall2_cons_inv_r R l y m : Forall2 R l (y::m) → { x : _ & { l' | R x y ∧ Forall2 R l' m ∧ l = x::l' } }.
  Proof.
    intros H; destruct l as [ | x l ].
    + exfalso; inversion H.
    + apply Forall2_cons_iff in H as []; eauto.
  Qed.

  (* The version of Forall2_app_inv_r from Coq.List is Prop-bounded. This one is stronger, Type-bounded *)
  Fact Forall2_app_inv_r R l m₁ m₂ : Forall2 R l (m₁++m₂) → { l₁ : _ & { l₂ | Forall2 R l₁ m₁ ∧ Forall2 R l₂ m₂ ∧ l = l₁++l₂ } }.
  Proof.
    revert m₂ l; induction m₁ as [ | y m1 IH ]; simpl; intros m2 l H.
    + exists nil, l; repeat split; auto.
    + apply Forall2_cons_inv_r in H as (x & l' & ? & (l1 & l2 & ? & ? & ->)%IH & ->).
      exists (x::l1), l2; eauto.
  Qed.

  Fact Forall2_middle_inv_l R l x r m : Forall2 R (l++x::r) m → ∃ l' y r', Forall2 R l l' ∧ R x y ∧ Forall2 R r r' ∧ m = l'++y::r'.
  Proof.
    intros (l' & m' & ? & (y & r' & ? & [])%Forall2_cons_inv_l & ?)%Forall2_app_inv_l; subst.
    exists l', y, r'; auto.
  Qed.

  Fact Forall2_in_inv_l R l m x : Forall2 R l m → x ∈ l → ∃y, y ∈ m ∧ R x y.
  Proof.
    intros H (u & v & ->)%in_split.
    apply Forall2_middle_inv_l in H as (l' & y & r' & ? & ? & ? & ?); subst; eauto.
  Qed.

  Fact Forall2_special_inv_r R k l y₁ m y₂ r :
      Forall2 R k (l++y₁::m++y₂::r)
    → ∃ l' x₁ m' x₂ r',
        Forall2 R l' l
      ∧ R x₁ y₁
      ∧ Forall2 R m' m
      ∧ R x₂ y₂
      ∧ Forall2 R r' r
      ∧ k = l'++x₁::m'++x₂::r'.
  Proof.
    intros H.
    apply Forall2_app_inv_r in H as (u & l1 & Ha & H & ?); subst.
    apply Forall2_cons_inv_r in H as (x1 & l2 & H1 & H & ?); subst.
    apply Forall2_app_inv_r in H as (v & l3 & Hb & H & ?); subst.
    apply Forall2_cons_inv_r in H as (x2 & w & H2 & H & ?); subst.
    exists u, x1, v, x2, w; split; auto.
  Qed.

End Forall2_extra.

(** Relational morphisms to transfer Accessibility and Well-foundedness *)

Section wf_rel_morph.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (f : X → Y → Prop)
            (f_surj : ∀y, ∃x, f x y)
            (f_morph : ∀ x₁ x₂ y₁ y₂, f x₁ y₁ → f x₂ y₂ → T y₁ y₂ → R x₁ x₂).

  Theorem Acc_rel_morph x y : f x y → Acc R x → Acc T y.
  Proof.
    intros H1 H2; revert H2 y H1.
    induction 1 as [ x _ IH ]; intros y ?.
    constructor; intros z ?.
    destruct (f_surj z); eauto.
  Qed.

  Hint Resolve Acc_rel_morph : core.

  Corollary wf_rel_morph : well_founded R → well_founded T.
  Proof. intros ? y; destruct (f_surj y); eauto. Qed.

End wf_rel_morph.

Tactic Notation "wf" "rel" "morph" uconstr(g) :=
  apply wf_rel_morph with (f := g).


