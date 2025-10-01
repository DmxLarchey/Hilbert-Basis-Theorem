(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

Require Import utils bar monotone_closure.

Import ListNotations.

(** This proof is a Rocq rework of the proof 
    of the constructive form of Ramsey's theorem that
    can be found in

     [1] "Higman's lemma in Type theory", D. Fridlender 
            in TYPES 1996 

    Notice that D. Fridlender proves that the direct
    product of two almost full binary relations
    ("AF R" is expressed as "bar (good R) []") is
    also almost full.

    The proof derived from Coquand's abstract outline 
    (unpublished) in

     [2] "Stop we you are almost full" (ITP 2012)

    works differently, by induction on the arity of
    the relations and show that the intersection of
    two AF relations is AF. That approach was not
    suitable to work out an adaptation to the context
    of Noetherian relations.

    See product_noetherian.v to review the conversion
    of the below proof to the context of Bar Noetherian
    rings. *)

Fact In_split_special X (x : X) l y r : y ∈ l++x::r ↔ x = y ∨ y ∈ l++r.
Proof. rewrite !in_app_iff; simpl; tauto. Qed. 

Section bar_good_middle.

  Notation MC := monotone_closure.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Types (P Q : X → Prop).

  Definition idl P x := ∃y, P y ∧ R y x.

  Fact idl_mono P Q : P ⊆₁ Q → idl P ⊆₁ idl Q.
  Proof. intros H ? (y & ?%H & ?); now exists y. Qed.

  Definition good := MC (λ l, idl ⌞l⌟).

  Hint Constructors MC : core.

  Hint Resolve in_or_app in_eq : core.

  Fact good_monotone x l : good l → good (x::l).
  Proof. now constructor 2. Qed.

  Fact good_nil_inv : good [] → False.
  Proof. now intros ?%MC_inv. Qed.

  Fact good_cons_inv x l : good (x::l) ↔ good l ∨ idl ⌞l⌟ x.
  Proof.
    split.
    + intros []%MC_inv; eauto.
    + intros [ | ]; [ now constructor 2 | now constructor 1 ].
  Qed.

  Fact good_sg_inv x : good [x] → False.
  Proof. intros [ []%good_nil_inv | (? & [] & _) ]%good_cons_inv. Qed.

  Fact good_app_inv l r : good (l++r) ↔ (∃ l' x m, l = l'++x::m ∧ idl ⌞m++r⌟ x) ∨ good r.
  Proof. apply MC_app_inv. Qed.

  Fact good_middle_inv l x r : 
       good (l++x::r)
    ↔ (∃ l' y m, l = l'++y::m ∧ idl ⌞m++x::r⌟ y) (* in l *)
    ∨ idl ⌞r⌟ x                                  (* at x *)
    ∨ good r                                       (* in r *)
    .
  Proof. rewrite good_app_inv, good_cons_inv; tauto. Qed.

  Fact good_special_inv l m x r :
       good (l++m++x::r)
    ↔ (∃ l₁ y l₂, l = l₁++y::l₂ ∧ idl ⌞l₂++m++x::r⌟ y) (* in l *)
    ∨ (∃ m₁ y m₂, m = m₁++y::m₂ ∧ idl ⌞m₂++x::r⌟ y)    (* in m *)
    ∨ idl ⌞r⌟ x                                        (* at x *)
    ∨ good r                                             (* in r*)
    .
  Proof. rewrite !good_app_inv, good_cons_inv; tauto. Qed.

  Fact good_app_left l r : good r → good (l++r).
  Proof. apply MC_app_left. Qed.

  Fact good_app_middle m : ∀ l r, good (l++r) → good (l++m++r).
  Proof.
    apply MC_app_middle.
    intros ? ? ?; apply idl_mono.
    intros ?; rewrite !in_app_iff; tauto.
  Qed.

  Fact good_app_right l r : good l → good (l++r).
  Proof.
    intros H.
    rewrite <- app_nil_r, <- app_assoc.
    apply good_app_middle.
    now rewrite app_nil_r.
  Qed.

  Hint Resolve good_app_left good_app_right good_monotone : core.

  Remark good_iff_split p : good p ↔ ∃ l x m y r, p = l++x::m++y::r ∧ R y x.
  Proof.
    unfold good; rewrite MC_split; split.
    + intros (l & x & ? & -> & y & (m & r & ->)%in_split & ?); simpl.
      now exists l, x, m, y, r.
    + intros (l & x & m & y & r & -> & ?); exists l, x, (m++y::r); split; auto.
      exists y; rewrite in_app_iff; simpl; eauto.
  Qed.

  Hint Resolve good_app_middle : core.

  Fact bar_good_app_middle l m r : bar good (l++r) → bar good (l++m++r).
  Proof. revert l r; apply bar_app_middle; auto. Qed.

  Fact bar_good_app_head l r : bar good r → bar good (l++r).
  Proof. apply bar_good_app_middle with (l := []). Qed.

  Fact bar_good_skip_app x m r : bar good (x::r) → bar good (x::m++r).
  Proof. apply bar_good_app_middle with (l := [_]). Qed.

  Fact bar_good_skip_cons x y r : bar good (x::r) → bar good (x::y::r).
  Proof. apply bar_good_skip_app with (m := [_]). Qed.

End bar_good_middle.

Arguments idl {_}.
Arguments good {_}.

#[local] Hint Resolve in_map in_or_app : core.

Fact good_mono X (R T : X → X → Prop) : R ⊆₂ T -> good R ⊆₁ good T.
Proof.
  intros H; apply MC_mono.
  intros ? ? (u & ? & ?); exists u; eauto.
Qed.

Fact good_map X Y (f : X → Y) (R : X → X → Prop) (T : Y → Y → Prop) :
    (∀ x y, R x y → T (f x) (f y))
  → (∀ l, good R l → good T (map f l)).
Proof.
  intros H.
  induction 1 as [ ? ? (? & []) | ]; simpl.
  + constructor 1; exists (f x); eauto.
  + now constructor 2.
Qed.

Fact good_map_inv X Y (f : X → Y) (R : X → X → Prop) (T : Y → Y → Prop) :
    (∀ x y, T (f x) (f y) → R x y)
  → (∀ l, good T (map f l) → good R l ).
Proof.
  intros ? ? (? & ? & ? & ? & ? & (l & x & m & y & r & -> & <- & <- & <- & <- & <-)%map_split_pair_inv & ?)%good_iff_split.
  apply good_iff_split; exists l, x, m, y, r; auto.
Qed.

Section ramsey.

  Variables (X Y : Type) (R : X → X → Prop) (S : Y → Y → Prop).

  Let T (a b : X*Y) := R (fst a) (fst b) ∧ S (snd a) (snd b).
  
  Inductive X_Y_XY : Type :=
    | inX  : X → X_Y_XY
    | inY  : Y → X_Y_XY
    | inXY : X*Y → X_Y_XY.

  Let RS (a b : X_Y_XY) :=
    match a, b with
    | inX x, inX x' => R x x'
    | inY y, inY y' => S y y'
    | inX x, inXY z => R x (fst z)
    | inY y, inXY z => S y (snd z)
    | inXY a, inXY b => T a b
    | _, _ => False
    end.

  Local Fact R_RS x x' : R x x' → RS (inX x) (inX x').   Proof. now simpl. Qed.
  Local Fact S_RS y y' : S y y' → RS (inY y) (inY y').   Proof. now simpl. Qed.
  Local Fact T_RS a b : T a b → RS (inXY a) (inXY b).    Proof. now simpl. Qed.

  Local Fact RS_R x x' : RS (inX x) (inX x') → R x x'.   Proof. now simpl. Qed.
  Local Fact RS_S y y' : RS (inY y) (inY y') → S y y'.   Proof. now simpl. Qed.
  Local Fact RS_T a b :  RS (inXY a) (inXY b) → T a b.   Proof. now simpl. Qed.

  Hint Resolve R_RS S_RS T_RS RS_R RS_S RS_T good_map good_map_inv good_app_left good_app_right : core.

  (** This is the over approximation proposed in [1] which does not
      have the shape good ? (combination of l, lx, ly)  *)

  Let θ lx ly l := good RS (map inXY l++map inX lx++map inY ly).

  Hint Resolve good_app_middle in_or_app : core.

  Local Fact θ_app_middle lx ly l m r : θ lx ly (l++r) → θ lx ly (l++m++r).
  Proof. 
    unfold θ.
    rewrite !map_app, <- !app_assoc.
    apply good_app_middle.
  Qed.

  Hint Resolve θ_app_middle : core.

  Local Fact bar_θ_middle lx ly l m r : bar (θ lx ly) (l++r) → bar (θ lx ly) (l++m++r).
  Proof. apply bar_app_middle; auto. Qed.

  Local Fact bar_θ_app_left lx ly l r : bar (θ lx ly) r → bar (θ lx ly) (l++r).
  Proof. apply bar_app_middle with (l := []); auto. Qed.

  Local Fact bar_θ_cons_middle lx ly x m r : bar (θ lx ly) (x::r) → bar (θ lx ly) (x::m++r).
  Proof. apply bar_app_middle with (l := [x]); auto. Qed.

  Hint Resolve good_monotone good_app_right
               in_or_app in_eq : core.
               
               
               (*
  Let phi lx ly m := map inXY m ++ map inX lx ++ map inY ly.
  
  Check phi.
               
  Theorem bar_ramsey : bar (good R) [] -> bar (good S) [] -> bar (fun m => good RS (phi [] [] m)) [].
  Proof.
    apply bar_ramsey.
    + intros lx ly z m; unfold phi; simpl; apply good_monotone.
    + intros lx ly; unfold phi; simpl.
      intro H; apply good_app_right.
      revert lx H; apply good_map; simpl; auto.
    + intros lx ly; unfold phi; simpl.
      intro H; apply good_app_left.
      revert ly H; apply good_map; simpl; auto.
    + intros x lx y ly m; unfold phi; simpl.
      intros [ H1 | H1 ]%good_cons_inv.
      * intros _.
        do 2 apply good_app_left.
        revert H1; apply good_map; simpl; eauto.
      * intros [(l1 & k & l2 & E & H2) | [H2|H2]]%good_split_inv.
        - apply map_split_inv in E as (m1 & z & m2 & ? & ? & ? & ?); subst.
        Search map eq cons app.
  Admitted.
  
  *)

  Section nested_induction.

    Variables (lx : list X) (ly : list Y) (x : X) (y : Y).
    
    (*
    
    Local Lemma lem_ramsey_9 l m :
  (*      (∀u, R x (fst u) → bar (θ lx ly) (u::l++[(x,y)])) *)
        bar (θ (x::lx) ly) l
      → bar (θ lx (y::ly)) m
      → bar (θ lx ly) (l++m++[(x,y)]).
    Proof.
      induction 1 as [ l Hl | l Hl IHl ] in m |- *.
      + rewrite θ_iff_good in Hl.
      intros H1 H2.
      rewrite bar_app_iff.
    Admitted.
    
    *)

    Local Lemma lem_ramsey_1 h l :
        (∀u, RS (inX x) (inXY u) → bar (θ lx ly) (u::l++[(x,y)]))
      → bar (θ (x::lx) ly) h
      → bar (θ lx ly) (h++l++[(x,y)]).
    Proof.
      intros G.
      induction 1 as [ h Hh | h _ IHh ].
      2: constructor 2; auto.
      red in Hh; simpl in Hh.
      apply good_middle_inv in Hh
        as [ (? & ? & ? & (h1 & z & h2 & -> & <- & <- & <-)%map_split_inv & ?) | [ | ] ].
      + destruct H as (k & [ <- | H ]%In_split_special & Hk).
        * rewrite <- app_assoc; simpl.
          now apply bar_θ_app_left, bar_θ_middle with (l := [_]), G.
        * constructor 1; red; rewrite !map_app, <- !app_assoc; simpl.
          apply good_app_left; constructor 1.
          exists k; split; auto.
          revert H; repeat (rewrite !in_app_iff; simpl); tauto.
      + constructor 1; red; rewrite !map_app, <- !app_assoc.
        do 2 apply good_app_left; constructor 1.
        destruct H as (k & H%in_app_iff & Hk); exists k; split; auto.
        destruct H as [ (x' & <- & H)%in_map_iff | (y' & <- & H)%in_map_iff ]; auto.
        destruct Hk.
      + constructor 1; red.
        now apply good_app_left.
    Qed.

    Hypothesis (B1 : bar (θ (x::lx) ly) []).

    Local Lemma lemma_ramsey_2 l :
        Forall (λ u, RS (inX x) (inXY u)) l
      → bar (θ lx (y::ly)) l
      → bar (θ lx ly) (l++[(x,y)]).
    Proof.
      intros H1 H2; revert H2 H1.
      induction 1 as [ l Hl | l _ IHl ].
      + clear B1.
        intros H1; rewrite Forall_forall in H1.
        constructor 1.
        red in Hl |- *; simpl in Hl.
        rewrite map_app, <- app_assoc; simpl.
        apply good_special_inv in Hl
          as [ (? & ? & ? & (l1 & k & l2 & -> & <- & <- & <-)%map_split_inv & Hl) | 
             [ (? & ? & ? & (lx1 & x' & lx2 & -> & <- & <- & <-)%map_split_inv & ?) | [] ] ].
        * rewrite map_app; simpl; rewrite <- !app_assoc; simpl.
          apply good_app_left; constructor 1.
          rewrite app_assoc in Hl.
          destruct Hl as (u & [<- | Hu ]%In_split_special & Hl).
          - exists (inXY (x,y)); split; eauto; split; simpl; auto.
            apply (H1 k); eauto.
          - exists u; split; auto.
            revert Hu; repeat (rewrite !in_app_iff; simpl); tauto.
        * destruct H as (u & [<- | Hu ]%In_split_special & H).
          - destruct H.
          - rewrite map_app; simpl; rewrite <- app_assoc.
            apply good_app_left, good_app_left with (l := [_]), good_app_left.
            simpl; constructor 1; exists u; split; auto.
        * apply good_app_left; constructor 1.
          destruct H as (? & (u & <- & ?)%in_map_iff & ?).
          exists (inY u); split; auto.
        * now apply good_app_left, good_app_left with (l := [_]), good_app_left.
      + intros H1; apply lem_ramsey_1 with (h := []); eauto.
    Qed.

    Hypothesis (B2 : bar (θ lx (y::ly)) []).

    Local Lemma lemma_ramsey_3 : bar (θ lx ly) [(x,y)].
    Proof. apply lemma_ramsey_2 with (l := []); simpl; auto. Qed.

  End nested_induction.

  Local Lemma bar_compose lx ly : bar (good R) lx → bar (good S) ly → bar (θ lx ly) [].
  Proof.
    double bar induction as ? ?.
    + constructor 1; red; simpl.
      apply good_app_right, good_map with (2 := H); auto.
    + constructor 1; red; simpl.
      apply good_app_left, good_map with (2 := H); auto.
    + constructor 2; intros []; apply lemma_ramsey_3; auto.
  Qed.

  Local Fact bar_phi_good : bar (θ [] []) [] → bar (good T) [].
  Proof.
    apply bar_mono.
    unfold θ; intro; simpl; rewrite app_nil_r; eauto.
  Qed.

  Corollary ramsey : bar (good R) [] → bar (good S) [] → bar (good T) [].
  Proof. intros; now apply bar_phi_good, bar_compose. Qed.

End ramsey.

Check ramsey.
Print Assumptions ramsey.


  


