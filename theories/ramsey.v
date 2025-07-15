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
  
  Definition lowered l x := ∃y, y ∈ l ∧ R y x.
  
  Fact lowered_incl l m x : incl l m → lowered l x → lowered m x.
  Proof. intros H (? & ?%H & ?); red; eauto. Qed.
  
  Hint Resolve in_or_app : core.
  
  Fact lowered_app_left l r x : lowered r x → lowered (l++r) x.
  Proof. apply lowered_incl; red; eauto. Qed.
  
  Fact lowered_app_right l r x : lowered l x → lowered (l++r) x.
  Proof. apply lowered_incl; red; eauto. Qed.
  
  Fact lowered_cons_inv y l x : lowered (y::l) x → R y x ∨ lowered l x.
  Proof. intros (? & [ <- | ] & ?); auto; right; red; eauto. Qed.  

  Definition good := Good lowered.

  Hint Constructors Good : core.

  Hint Resolve in_or_app in_eq : core.

  Fact good_monotone x l : good l → good (x::l).
  Proof. now constructor 2. Qed.

  Fact good_nil_inv : good [] → False.
  Proof. now intros ?%Good_inv. Qed.

  Fact good_cons_inv x l : good (x::l) ↔ good l ∨ lowered l x.
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
  Proof. revert l; apply Good_app_right; intros ? ? (? & []); red; eauto. Qed.

  Hint Resolve good_app_left good_app_right : core.

  Fact good_iff_split p : good p ↔ ∃ l x m y r, p = l++x::m++y::r ∧ R y x.
  Proof.
    unfold good; rewrite Good_split; split.
    + intros (l & x & ? & -> & y & (m & r & ->)%in_split & ?); simpl.
      now exists l, x, m, y, r.
    + intros (l & x & m & y & r & -> & ?); exists l, x, (m++y::r); split; auto.
      exists y; rewrite in_app_iff; simpl; eauto.
  Qed.
  
  Hint Resolve lowered_app_left lowered_app_right : core.

  Fact good_app_inv l r : good (l++r) ↔ good l ∨ good r ∨ ∃x, x ∈ l ∧ lowered r x.
  Proof.
    split.
    + induction l as [ | x l IHl ]; simpl; eauto.
      intros [ (y & [ H1 | H1 ]%in_app_iff & H2) | [ | [ | (u & v & ? & []) ] ]%IHl ]%Good_inv; eauto.
      * left; constructor 1; red; eauto.
      * do 2 right; exists x; split; auto; red; eauto.
      * left; now constructor 2.
      * do 2 right; exists u; split; auto; red; eauto.
    + intros [ | [ | (x & (l' & m & ->)%in_split & ?) ] ]; eauto.
      rewrite <- app_assoc; simpl.
      apply Good_app_left; constructor 1; eauto.
  Qed.

  Fact good_snoc_inv l x : good (l++[x]) ↔ good l ∨ ∃y, y ∈ l ∧ R x y.
  Proof.
    rewrite good_app_inv; split.
    + intros [ | [ []%good_sg_inv | (? & ? & ? & [ <- | [] ] & ?) ] ]; eauto.
    + intros [ | (y & ? & ?) ]; eauto.
      do 2 right; exists y; split; auto; red; eauto.
  Qed.

  Fact bar_good_middle l m r : bar good (l++r) → bar good (l++m++r).
  Proof.
    revert l r; apply bar_app_middle.
    intros l r [ | [ | (x & y & ?  & [])] ]%good_app_inv; apply good_app_inv; eauto.
    do 2 right; exists x; split; auto; red; eauto.
  Qed.

  Fact bar_good_app_head l r : bar good r → bar good (l++r).
  Proof. apply bar_good_middle with (l := []). Qed.

  Fact bar_good_skip_app x m r : bar good (x::r) → bar good (x::m++r).
  Proof. apply bar_good_middle with (l := [_]). Qed.

  Fact bar_good_skip_cons x y r : bar good (x::r) → bar good (x::y::r).
  Proof. apply bar_good_skip_app with (m := [_]). Qed.

End bar_good_middle.

Arguments lowered {_}.
Arguments good {_}.

#[local] Hint Resolve in_map in_or_app : core.

Fact good_map X Y (f : X → Y) (R : X → X → Prop) (T : Y → Y → Prop) :
    (∀ x y, R x y → T (f x) (f y))
  → (∀ l, good R l → good T (map f l)).
Proof.
  intros H.
  induction 1 as [ ? ? (? & []) | ]; simpl.
  + constructor 1; red; eauto.
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

Section sublist.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Type (l : list X).

  Hint Resolve incl_refl incl_cons incl_tl incl_appl incl_appr in_or_app incl_nil_l in_eq good_app_left : core.

  Inductive sublist : list X → list X → Prop :=
    | sublist_nil : [] <sl []
    | sublist_hd x l m : l <sl m  → x::l <sl x::m
    | sublist_tl x l m : l <sl m  → l <sl x::m
  where "l <sl m" := (sublist l m).

  Hint Constructors sublist : core.
  
  Fact sublist_nil_l l : [] <sl l.
  Proof. induction l; eauto. Qed.

  Fact sublist_mono l m : l <sl m → incl l m.
  Proof. induction 1; eauto. Qed.

  Fact sublist_app_l l h m : l <sl m → l <sl h++m.
  Proof. induction h; simpl; eauto. Qed.
  
  Fact sublist_app l l' m m' : l <sl m → l' <sl m' → l++l' <sl m++m'.
  Proof. induction 1; simpl; auto. Qed.
  
  Hint Resolve sublist_nil_l sublist_app_l : core.
  
  Fact In_sublist x l : x ∈ l → [x] <sl l.
  Proof. intros (? & ? & ->)%in_split; eauto. Qed.
  
  Hint Resolve In_sublist sublist_app : core.
  
  Fact sublist_cons_app x m l r : x ∈ l → m <sl r → x::m <sl l++r.
  Proof. intros; apply sublist_app with (l := [_]); eauto. Qed.
  
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
    + intros (z & [ <- | Hz ] & ?); red; eauto.
      destruct IH as (? & []); eauto; red; eauto.
    + intros (? & [])%IH; red; eauto.
  Qed.

End sublist.

Arguments sublist {_}.
#[local] Infix "<sl" := sublist.

Section bar_double_ind.

  Variables (X Y : Type) (P : list X → Prop) (Q : list Y → Prop) 
            (K : list X → list Y → Prop)
            (HPK : ∀ l m, P l → K l m) 
            (HQK : ∀ l m, Q m → K l m)
            (HPQK : ∀ l m, (∀x, K (x::l) m) → (∀y, K l (y::m)) → K l m).

  Theorem bar_double_ind l m : bar P l → bar Q m → K l m.
  Proof.
    induction 1 in m |- *; auto.
    induction 1 as [ | ? ?%bar_next ]; auto.
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
                   ∨ (∃z, z ∈ l ∧ lowered R lx (fst z))  (** l ++ map inX lx ++ map inY ly is good *)
                   ∨ (∃z, z ∈ l ∧ lowered S ly (snd z)).

  Local Fact R_K x x' : R x x' → K (inX x) (inX x').   Proof. now simpl. Qed.
  Local Fact S_K y y' : S y y' → K (inY y) (inY y').   Proof. now simpl. Qed.
  Local Fact T_K a b : T a b → K (inXY a) (inXY b).    Proof. now simpl. Qed.

  Local Fact K_R x x' : K (inX x) (inX x') → R x x'.   Proof. now simpl. Qed.
  Local Fact K_S y y' : K (inY y) (inY y') → S y y'.   Proof. now simpl. Qed.
  Local Fact K_T a b :  K (inXY a) (inXY b) → T a b.   Proof. now simpl. Qed.

  Hint Resolve R_K S_K T_K K_R K_S K_T good_map good_app_left good_app_right good_map_inv : core. 

  Local Remark phi_iff lx ly l : phi lx ly l ↔ good K (map inXY l++map inX lx++map inY ly).
  Proof.
    split.
    + intros [ | [ | [ | [ ((x' & y') & ? & x & []) | ((x' & y') & ? & y & []) ] ] ] ]; eauto.
      * apply good_app_inv; do 2 right.
        exists (inXY (x',y')); split; auto; exists (inX x); simpl; split right; eauto.
      * apply good_app_inv; do 2 right.
        exists (inXY (x',y'));split; auto; exists (inY y); simpl; split right; eauto.
    + intros [ H | [ [ H | [ H | H ] ]%good_app_inv | H ] ]%good_app_inv; red; eauto.
      * right; eauto.
      * destruct H as (? & (x & <- & ?)%in_map_iff & ? & (y & <- & ?)%in_map_iff & []).
      * destruct H as (? & ((x' & y') & <- & ?)%in_map_iff & ? & [(x & <- & ?)%in_map_iff|(y & <- & ?)%in_map_iff]%in_app_iff & ?); simpl in *.
        - do 3 right; left; exists (x',y'); split; auto; red; eauto.
        - do 4 right; exists (x',y'); split; auto; red; eauto.
  Qed.

  Hint Resolve good_monotone good_app_right
               in_or_app in_eq
               sublist_good
               sublist_mono
               sublist_app_l : core.

  Section nested_induction.

    Hint Constructors sublist : core.

    Variables (lx : list X) (ly : list Y) (z : X*Y).
    
    Local Lemma lem_ramsey_1 h m :
         z ∈ m
      → (∀ u h, R (fst z) (fst u) → u ∈ h → bar (phi lx ly) (h++m))
      → bar (phi (fst z::lx) ly) h → bar (phi lx ly) (h++m).
    Proof.
      intros G3 G4.
      induction 1 as [ h Hh | h _ IHh ].
      2: constructor 2; auto.
      destruct Hh as [ []%good_cons_inv | [ | [ | [Hh|Hh] ] ] ].
      1,2,3,4,6: constructor 1; red; auto.
      + do 3 right; left; eauto.
      + destruct Hh as (u & []).
        do 4 right; eauto.
      + destruct Hh as (u & ? & []%lowered_cons_inv); eauto.
        constructor 1; red. 
        do 3 right; left; eauto.
    Qed.

    Hypothesis (B1 : bar (phi (fst z::lx) ly) []).

    Local Lemma lemma_ramsey_2 l :
        bar (phi lx (snd z::ly)) l
      → Forall (λ u, R (fst z) (fst u)) l
      → ∀ m, l++[z] <sl m → bar (phi lx ly) m.
    Proof.
      induction 1 as [ l Hl | l _ IHl ].
      + intros H1 m H2.
        constructor 1.
        destruct Hl as [ Hl | [ Hl | [ Hl | [ Hl | Hl ] ] ] ]; red; eauto.
        * apply good_cons_inv in Hl as []; eauto.
          do 4 right; exists z; split right; eauto.
          eapply sublist_mono; eauto.
        * do 2 right; left; eauto.
        * destruct Hl as (u & []).
          do 3 right; left; exists u; split right; eauto.
          eapply sublist_mono; eauto.
        * destruct Hl as (u & Hu & []%lowered_cons_inv).
          - rewrite Forall_forall in H1.
            specialize (H1 _ Hu).
            do 2 right; left.
            apply sublist_good with (1 := H2).
            apply good_snoc_inv; right.
            exists u; split right; auto.
          - do 4 right; exists u; split right; eauto.
            eapply sublist_mono; eauto.
      + intros H1 m H2.
        apply lem_ramsey_1 with (h := []); eauto.
        * eapply sublist_mono; eauto.
        * intros u h Hu Hh.
          apply (IHl u); auto. 
          now apply sublist_cons_app.
    Qed.

    Hypothesis (B2 : bar (phi lx (snd z::ly)) []).

    Local Lemma lemma_ramsey_3 : bar (phi lx ly) [z].
    Proof. apply lemma_ramsey_2 with (l := []); simpl; auto. Qed.

  End nested_induction.

  Local Lemma bar_compose lx ly : bar (good R) lx → bar (good S) ly → bar (phi lx ly) [].
  Proof.
    intros H1 H2; pattern lx, ly; revert lx ly H1 H2; apply bar_double_ind.
    + constructor 1; red; auto.
    + constructor 1; red; auto.
    + constructor 2; intro; apply lemma_ramsey_3; auto.
  Qed.

  Local Fact bar_phi_good : bar (phi [] []) [] → bar (good T) [].
  Proof.
    apply bar_mono.
    intro; rewrite phi_iff; simpl; rewrite app_nil_r; eauto.
  Qed.

  Corollary ramsey : bar (good R) [] → bar (good S) [] → bar (good T) [].
  Proof. intros; now apply bar_phi_good, bar_compose. Qed.

End ramsey.

Check ramsey.
Print Assumptions ramsey.


  


