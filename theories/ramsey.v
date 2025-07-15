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

  Hint Resolve in_or_app in_eq : core.

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

  Fact good_sg_inv x : good [x] → False.
  Proof. intros [ []%good_nil_inv | (? & [] & _) ]%good_cons_inv. Qed.

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

  Fact good_snoc_inv l x : good (l++[x]) ↔ good l ∨ ∃y, y ∈ l ∧ R x y.
  Proof.
    rewrite good_app_inv; split.
    + intros [ | [ []%good_sg_inv | (? & ? & ? & [ <- | [] ] & ?) ] ]; eauto.
    + intros [ | (y & ? & ?) ]; eauto.
      do 2 right; exists y, x; auto.
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

#[local] Hint Resolve in_map in_or_app : core.

Fact good_map X Y (f : X → Y) (R : X → X → Prop) (T : Y → Y → Prop) :
    (∀ x y, R x y → T (f x) (f y))
  → (∀ l, good R l → good T (map f l)).
Proof.
  intros H.
  induction 1 as [ ? ? (? & []) | ]; simpl.
  + constructor 1; eauto.
  + now constructor 2.
Qed.

Fact good_map_inv X Y (f : X → Y) (R : X → X → Prop) (T : Y → Y → Prop) :
    (∀ x y, T (f x) (f y) → R x y)
  → (∀ l, good T (map f l) → good R l ).
Proof.
  intros ? ? (? & ? & ? & ? & ? & (l & x & m & y & r & -> & <- & <- & <- & <- & <-)%map_split_pair_inv & ?)%good_iff_split.
  apply good_iff_split; exists l, x, m, y, r; auto.
Qed.

#[local] Reserved Notation "l '<sl' m" (at level 70, no associativity, format "l  <sl  m").

Section intercalate.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Type (l : list X).

  Hint Resolve incl_refl incl_cons incl_tl incl_appl incl_appr in_or_app incl_nil_l in_eq good_app_left : core.

(*
  Inductive intercalate : list X → list (list X) → list X → Prop :=
    | intercal_stop m : intercalate [] [m] m
    | interca_next x l m mm r : intercalate l mm r → intercalate (x::l) (m::mm) (m++x::r).

 

  Fact intercalate_incl_left l mm r : intercalate l mm r → incl l r.
  Proof. induction 1; eauto; apply incl_cons; simpl; eauto. Qed.

  Fact intercalate_incl_right l mm r : intercalate l mm r → incl (concat mm) r.
  Proof. induction 1; simpl; eauto; apply incl_app; eauto. Qed.

  Fact intercalate_head l mm h r : intercalate l mm r → exists mm', intercalate l mm' (h++r).
  Proof.
    induction 1 as [ m | x l m mm r H _ ].
    + exists [h++m]; constructor.
    + exists ((h++m)::mm); simpl.
      rewrite app_assoc; now constructor.
  Qed.

  Fact intercalate_sg x : intercalate [x] [[];[]] [x].
  Proof. constructor 2 with (m := []); constructor. Qed.

  Fact good_intercalate l mm r : intercalate l mm r → good R l → good R r.
  Proof.
    induction 1 as [ | x l m mm r H IH ].
    1: now intros ?%good_nil_inv.
    intros [ | (y & H1 & H2) ]%good_cons_inv.
    + replace (m++x::r) with ((m++[x])++r) by now rewrite <- app_assoc.
      apply good_app_left; auto.
    + apply intercalate_incl_left with (1 := H) in H1.
      apply good_app_left.
      constructor 1; exists y; split; auto.
  Qed.
  
  *)

  Inductive sublist : list X → list X → Prop :=
    | sublist_nil : [] <sl []
    | sublist_hd x l m : l <sl m  → x::l <sl x::m
    | sublist_tl x l m : l <sl m  → l <sl x::m
  where "l <sl m" := (sublist l m).

  Hint Constructors sublist : core.

  Fact sublist_mono l m : l <sl m → incl l m.
  Proof. induction 1; eauto. Qed.

  Fact sublist_app_l l h m : l <sl m → l <sl h++m.
  Proof. induction h; simpl; eauto. Qed.
  
  Hint Resolve good_monotone in_cons in_eq : core.
  Hint Constructors Good : core.
  
  Fact sublist_Good P :
      (∀ l m x, l <sl m → P l x → P m x)
    → (∀ l m, l <sl m → @Good X P l → Good P m).
  Proof. induction 2; eauto; intros []%Good_inv; eauto. Qed.

  Fact sublist_good l m : l <sl m → good R l → good R m.
  Proof.
    revert l m; apply sublist_Good.
    intros l m x.
    induction 1 as [ | y l m H IH | y l m H IH ]; eauto.
    + intros (z & [ <- | Hz ] & ?); eauto.
      destruct IH as (? & []); eauto.
    + intros (? & [])%IH; eauto.
  Qed.
  
End intercalate.

Arguments sublist {_}.
#[local] Infix "<sl" := sublist.

Section bar_double_ind.

  Check bar_ind.

  Variables (X Y : Type) (P : list X -> Prop) (Q : list Y -> Prop) 
            (K : list X -> list Y -> Prop)
            (HPK : forall l m, P l -> K l m) 
            (HQK : forall l m, Q m -> K l m)
            (HPQK : forall l m, (forall x, K (x::l) m) -> (forall y, K l (y::m)) -> K l m).

  Theorem bar_double_ind l m : bar P l -> bar Q m -> K l m.
  Proof.
    induction 1 as [ | l Hl IHl ] in m |- *; auto.
    induction 1 as [ | m Hm%bar_next IHm ]; auto.
  Qed.

End bar_double_ind.

Section ramsey.

  Variables (X Y : Type) (R : X → X → Prop) (S : Y → Y → Prop).

  Let T (a b : X*Y) := R (fst a) (fst b) ∧ S (snd a) (snd b).
  
  Inductive X_Y_XY : Type :=
    | inX  : X → X_Y_XY
    | inY  : Y → X_Y_XY
    | inXY : X*Y → X_Y_XY.
    
  Let K (a b : X_Y_XY) :=
    match a, b with
    | inX x, inX x' => R x x'
    | inY y, inY y' => S y y'
    | inX x, inXY (x',_) => R x x'
    | inY y, inXY (_,y') => S y y'
    | inXY a, inXY b => T a b
    | _, _ => False
    end.

  Let phi lx ly l := good R lx ∨ good S ly ∨ good T l
                   ∨ (∃ x z, x ∈ lx ∧ z ∈ l ∧ R x (fst z))  (** l ++ map inX lx ++ map inY ly is good *)
                   ∨ (∃ y z, y ∈ ly ∧ z ∈ l ∧ S y (snd z)).
                   
  Local Fact R_K x x' : R x x' → K (inX x) (inX x').   Proof. now simpl. Qed.
  Local Fact S_K y y' : S y y' → K (inY y) (inY y').   Proof. now simpl. Qed.
  Local Fact T_K a b : T a b → K (inXY a) (inXY b).    Proof. now simpl. Qed.

  Local Fact K_R x x' : K (inX x) (inX x') → R x x'.   Proof. now simpl. Qed.
  Local Fact K_S y y' : K (inY y) (inY y') → S y y'.   Proof. now simpl. Qed.
  Local Fact K_T a b :  K (inXY a) (inXY b) → T a b.   Proof. now simpl. Qed.
  
  Hint Resolve R_K S_K T_K K_R K_S K_T good_map good_app_left good_app_right good_map_inv : core. 

  Local Fact phi_iff lx ly l : phi lx ly l ↔ good K (map inXY l++map inX lx++map inY ly).
  Proof.
    split.
    + intros [ | [ | [ | [ (x & (x' & y') & ? & []) | (y & (x' & y') & ? & []) ] ] ] ]; eauto.
      * apply good_app_inv; do 2 right.
        exists (inXY (x',y')), (inX x); simpl; split right; eauto.
      * apply good_app_inv; do 2 right.
        exists (inXY (x',y')), (inY y); simpl; split right; eauto.
    + intros [ H | [ [ H | [ H | H ] ]%good_app_inv | H ] ]%good_app_inv; red; eauto.
      * right; eauto.
      * destruct H as (? & ? & (x & <- & ?)%in_map_iff & (y & <- & ?)%in_map_iff & []).
      * destruct H as (? & ? & ((x' & y') & <- & ?)%in_map_iff & [(x & <- & ?)%in_map_iff|(y & <- & ?)%in_map_iff]%in_app_iff & ?); simpl in *.
        - do 3 right; left; exists x, (x',y'); auto.
        - do 4 right; exists y, (x',y'); auto.
  Qed.
  
  Check bar_app_iff.

  Hint Resolve good_monotone : core.

  Local Fact bar_phi_good : bar (phi [] []) [] → bar (good T) [].
  Proof.
    apply bar_mono.
    intros l; rewrite phi_iff; simpl; rewrite app_nil_r; eauto.
  Qed.

  Hypothesis (HR : bar (good R) []) (HS : bar (good S) []).

  Hint Resolve good_app_right in_or_app in_eq sublist_good sublist_mono sublist_app_l : core.
  
  Hint Constructors sublist : core.

  Section oto.

    Variables (lx : list X) (ly : list Y) (z : X*Y)
              (B1 : bar (phi (fst z::lx) ly) [])
              (B2 : bar (phi lx (snd z::ly)) []).

    Local Fact titi h m :
         z ∈ m
      → (∀ a u b, R (fst z) (fst u) → bar (phi lx ly) (a++u::b++m))
      → bar (phi (fst z :: lx) ly) h → bar (phi lx ly) (h++m).
    Proof.
      intros G3 G4.
      induction 1 as [ h Hh | h _ IHh ].
      2: constructor 2; auto.
      destruct Hh as [ [ | (x & [])]%good_cons_inv | [ | [ | [Hh|Hh] ] ] ].
      1,2,3,4,6: constructor 1; red; auto.
      + do 3 right; left.
        exists x, z; split right; auto.
      + destruct Hh as (y & u & ? & []).
        do 4 right; exists y, u; eauto.
      + destruct Hh as (x & u & [ <- | H3 ] & H4 & H5).
        * apply in_split in H4 as (a & b & ->).
          rewrite <- app_assoc; simpl; auto.
        * constructor 1; red; do 3 right; left.
          exists x, u; eauto.
    Qed.

    Local Fact tutu l :
        bar (phi lx (snd z::ly)) l
      → Forall (λ u, R (fst z) (fst u)) l
      → ∀ m, l++[z] <sl m → bar (phi lx ly) m.
    Proof.
      intros H1 H2 m Hm.
      
      induction 1 as [ l Hl | l Hl IHl ].
      + intros H1 m H2.
        constructor 1.
        destruct Hl as [ Hl | [ Hl | [ Hl | [ Hl | Hl ] ] ] ]; red; eauto.
        * apply good_cons_inv in Hl as [ | (y & [])]; eauto.
          do 4 right; exists y, z; split right; eauto.
          eapply sublist_mono; eauto.
        * do 2 right; left; eauto.
        * destruct Hl as (x & u & ? & []).
          do 3 right; left; exists x, u; split right; eauto.
          eapply sublist_mono; eauto.
        * destruct Hl as (y & u & [ <- | H3 ] & H4 & H5).
          - rewrite Forall_forall in H1.
            specialize (H1 _ H4).
            do 2 right; left.
            apply sublist_good with (1 := H2), good_snoc_inv. 
            right; exists u; split right; auto.
          - do 4 right; exists y, u; split right; eauto.
            eapply sublist_mono; eauto.
      + intros H1 m H2.
        apply titi with (h := []); auto.
        * eapply sublist_mono; eauto.
        * intros a u b h; apply (IHl u); simpl; eauto.
    Qed.

    Local Fact toto : bar (phi lx ly) [z].
    Proof. apply tutu with (l := []); simpl; auto. Qed.

  End oto.

  Local Fact bar_compose lx ly : bar (good R) lx → bar (good S) ly → bar (phi lx ly) [].
  Proof.
    intros H1 H2; pattern lx, ly; revert lx ly H1 H2.
    apply bar_double_ind.
    + constructor 1; red; auto.
    + constructor 1; red; auto.
    + constructor 2; intro; apply toto; auto.
  Qed.

  Theorem ramsey : bar (good T) [].
  Proof. now apply bar_phi_good, bar_compose. Qed.

End ramsey.

Check ramsey.
Print Assumptions ramsey.


  


