(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

Require Import utils bar noetherian.

Import ListNotations.

Fact cons_inj X (x y : X) l m : x::l = y::m → x = y ∧ l = m.
Proof. now inversion 1. Qed.

Fact map_split_pair_inv X Y (f : X → Y) ll l' y₁ m' y₂ r' :
    map f ll = l'++y₁::m'++y₂::r'
  → ∃ l x₁ m x₂ r,
        ll = l++x₁::m++x₂::r
      ∧ map f l = l' ∧ f x₁ = y₁
      ∧ map f m = m' ∧ f x₂ = y₂
      ∧ map f r = r'.
Proof.
  intros H.
  apply map_eq_app  in H as (l & mm & -> & ? & H).
  apply map_eq_cons in H as (x & ll & -> & ? & H).
  apply map_eq_app  in H as (m & mm & -> & ? & H).
  apply map_eq_cons in H as (y & r & -> & ? & H).
  exists l, x, m, y, r; split; auto.
Qed.

Section bar_good_middle.

  Variables (X : Type) (R : X → X → Prop).

  Definition good := Good (λ l x, ∃y, y ∈ l ∧ R y x).

  Hint Constructors Good : core.

  Hint Resolve in_or_app : core.

  Fact good_monotone x l : good l → good (x::l).
  Proof. now constructor 2. Qed.

  Fact good_nil_inv : good [] → False.
  Proof. now intros ?%Good_inv. Qed.

  Fact good_cons_inv x l : good (x::l) ↔ good l ∨ ∃ y, In y l ∧ R y x.
  Proof.
    split.
    + intros []%Good_inv; eauto.
    + intros [ | ]; [ now constructor 2 | now constructor 1 ].
  Qed.

  Fact good_app_left l r : good r → good (l++r).
  Proof. apply Good_app_left. Qed.

  Fact good_app_right l r : good l → good (l++r).
  Proof. revert l; apply Good_app_right; intros ? ? (? & []); eauto. Qed.

  Hint Resolve good_app_left good_app_right : core.

  Fact good_iff_split p : good p ↔ ∃ l x m y r, p = l++x::m++y::r ∧ R y x.
  Proof.
    unfold good; rewrite Good_split; split.
    + intros (l & x & ? & -> & y & (m & r & ->)%in_split & ?); simpl.
      now exists l, x, m, y, r.
    + intros (l & x & m & y & r & -> & ?); exists l, x, (m++y::r); split; auto.
      exists y; rewrite in_app_iff; simpl; eauto.
  Qed.

  Fact good_app_inv l r : good (l++r) ↔ good l ∨ good r ∨ ∃ x y, x ∈ l ∧ y ∈ r ∧ R y x.
  Proof.
    split.
    + induction l as [ | x l IHl ]; simpl; eauto.
      intros [ (y & [ H1 | H1 ]%in_app_iff & H2) | [ | [ | (u & v & ? & []) ] ]%IHl ]%Good_inv; eauto.
      * left; constructor 1; eauto.
      * do 2 right; exists x, y; auto.
      * left; now constructor 2.
      * do 2 right; exists u, v; eauto.
    + intros [ | [ | (x & y & (l' & m & ->)%in_split & ? & ?) ] ]; eauto.
      rewrite <- app_assoc; simpl.
      apply Good_app_left; constructor 1; exists y; eauto.
  Qed.

  Fact bar_good_middle l m r : bar good (l++r) → bar good (l++m++r).
  Proof.
    revert l r; apply bar_app_middle.
    intros l r [ | [ | (x & y & ?  & [])] ]%good_app_inv; apply good_app_inv; eauto.
    do 2 right; exists x, y; split right; auto.
  Qed.

  Fact bar_good_app_head l r : bar good r → bar good (l++r).
  Proof. apply bar_good_middle with (l := []). Qed.

  Fact bar_good_skip_app x m r : bar good (x::r) → bar good (x::m++r).
  Proof. apply bar_good_middle with (l := [_]). Qed.

  Fact bar_good_skip_cons x y r : bar good (x::r) → bar good (x::y::r).
  Proof. apply bar_good_skip_app with (m := [_]). Qed.

End bar_good_middle.

Arguments good {_}.

Section intercalate.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Type (l : list X).

  Inductive intercalate : list X → list (list X) → list X → Prop :=
    | intercal_stop x : intercalate [x] [] [x]
    | interca_next x l m mm r : intercalate l mm r → intercalate (x::l) (m::mm) (x::m++r).

  Hint Resolve incl_refl incl_cons incl_tl incl_appl incl_appr in_or_app : core.

  Fact intercalate_incl_left l mm r : intercalate l mm r → incl l r.
  Proof. induction 1; eauto; apply incl_cons; simpl; eauto. Qed.

  Fact intercalate_incl_right l mm r : intercalate l mm r → incl (concat mm) r.
  Proof. induction 1; simpl; eauto; apply incl_app; eauto. Qed.

  Fact good_intercalate l mm r : intercalate l mm r → good R l → good R r.
  Proof.
    induction 1 as [ | x l m mm r H IH ]; auto.
    intros [ | (y & H1 & H2) ]%good_cons_inv.
    + apply good_app_left with (l := _::_); auto.
    + apply intercalate_incl_left with (1 := H) in H1.
      constructor 1; exists y; split; auto.
  Qed. 

End intercalate.

Section ramsey.

  Variables (X Y : Type) (R : X → X → Prop) (S : Y → Y → Prop).

  Let T : X*Y → X*Y → Prop := (λ '(x₁,y₁) '(x₂,y₂), R x₁ x₂ ∧ S y₁ y₂).

  Let phi lx ly l := good R lx ∨ good S ly ∨ good T l
                   ∨ (∃ x z, x ∈ lx ∧ z ∈ l ∧ R (fst z) x)
                   ∨ (∃ y z, y ∈ ly ∧ z ∈ l ∧ S (snd z) y).

  Hint Resolve good_monotone : core.

  Local Fact phi3_monotone lx ly z l : phi lx ly l → phi lx ly (z::l).
  Proof.
    intros [ | [ | [ | [ (x & u & ? & ? & ?) | (y & u & ? & ? & ?) ] ] ] ]; red; eauto.
    + do 3 right; left; simpl; exists x, u; auto.
    + do 4 right; simpl; exists y, u; auto.
  Qed.

  Local Fact bar_phi3 : bar (phi [] []) [] → bar (good T) [].
  Proof.
    apply bar_mono.
    intros l [ []%good_nil_inv | [ []%good_nil_inv | [ | [H|H]] ] ]; auto.
    all: simpl in H; now destruct H as (? & ? & ? & _).
  Qed.

  Hypothesis (HR : bar (good R) []) (HS : bar (good S) []).
  
  Local Fact toto lx ly z :
      bar (phi (fst z::lx) ly) []
    → bar (phi lx (snd z::ly)) []
    → bar (phi lx ly) [z].
  Admitted.

  Local Fact bar_compose lx ly : bar (good R) lx → bar (good S) ly → bar (phi lx ly) [].
  Proof.
    induction 1 as [ | lx Hlx IHlx ] in ly |- *.
    1: constructor 1; red; auto.
    induction 1 as [ | ly Hly IHly ].
    1: constructor 1; red; auto.
    constructor 2; intros z.
    apply toto; auto.
    apply IHlx; now constructor 2.
  Qed.

  Theorem ramsey : bar (good T) [].
  Proof. now apply bar_phi3, bar_compose. Qed.

End ramsey.
     
  

  


