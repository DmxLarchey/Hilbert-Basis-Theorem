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

Section bar_good_middle.

  Notation MC := monotone_closure.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Types (P Q : X → Prop).

  Definition idl P x := ∃y, P y ∧ R y x.

  Fact idl_mono P Q : P ⊆₁ Q → idl P ⊆₁ idl Q.
  Proof. intros H ? (y & ?%H & ?); now exists y. Qed.

  (* x is above some member of l *)
  Definition lowered l := idl ⌞l⌟.

  Fact lowered_incl l m : incl l m → lowered l ⊆₁ lowered m.
  Proof. apply idl_mono. Qed.

  Hint Resolve in_or_app : core.

  Fact lowered_app_left l r : lowered r ⊆₁ lowered (l++r).
  Proof. apply lowered_incl; red; eauto. Qed.

  Fact lowered_app_right l r : lowered l ⊆₁ lowered (l++r).
  Proof. apply lowered_incl; red; eauto. Qed.

  Fact lowered_cons_inv y l x : lowered (y::l) x → R y x ∨ lowered l x.
  Proof. intros (z & [ <- | ] & ?); auto; right; red; eauto; now exists z. Qed.

  Hint Resolve lowered_app_left lowered_app_right : core.

  Fact lowered_app_iff l r x : lowered (l++r) x ↔ lowered l x ∨ lowered r x.
  Proof. 
    split.
    + intros (z & []%in_app_iff & Hz); [ left | right ]; now exists z.
    + intros []; eauto.
  Qed.

  Definition good := MC lowered.

  Hint Constructors MC : core.

  Hint Resolve in_or_app in_eq : core.

  Fact good_monotone x l : good l → good (x::l).
  Proof. now constructor 2. Qed.

  Fact good_nil_inv : good [] → False.
  Proof. now intros ?%MC_inv. Qed.

  Fact good_cons_inv x l : good (x::l) ↔ good l ∨ lowered l x.
  Proof.
    split.
    + intros []%MC_inv; eauto.
    + intros [ | ]; [ now constructor 2 | now constructor 1 ].
  Qed.

  Fact good_sg_inv x : good [x] → False.
  Proof. intros [ []%good_nil_inv | (? & [] & _) ]%good_cons_inv. Qed.

  Fact good_app_left l r : good r → good (l++r).
  Proof. apply MC_app_left. Qed.

  Hint Resolve lowered_app_right : core.

  Fact good_app_right l r : good l → good (l++r).
  Proof. revert l; apply MC_app_right; eauto. Qed.

  Hint Resolve good_app_left good_app_right good_monotone : core.

  Fact good_iff_split p : good p ↔ ∃ l x m y r, p = l++x::m++y::r ∧ R y x.
  Proof.
    unfold good; rewrite MC_split; split.
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
      intros [ [ | [ | (z & []) ] ]%IHl | []%lowered_app_iff ]%good_cons_inv; eauto.
      * do 2 right; exists z; eauto.
      * left; now constructor 1.
      * do 2 right; exists x; eauto.
    + intros [ | [ | (x & (l' & m & ->)%in_split & ?) ] ]; eauto.
      rewrite <- app_assoc; simpl.
      apply MC_app_left; constructor 1; eauto.
  Qed.

  Fact good_split_inv l x r : good (l++x::r) 
                            ↔ (exists l' y m, l = l'++y::m /\ lowered (m++x::r) y)
                            \/ lowered r x
                            \/ good r.
  Proof.
    split.
    + induction l as [ | y l IHl ]; simpl.
      * intros [|]%good_cons_inv; eauto.
      * intros [[(l' & z & m & -> & H)|[]]%IHl|H]%good_cons_inv; eauto.
        - left; exists (y::l'), z, m; auto.
        - left; exists [], y, l; auto.
    + intros [ (l' & y & m & -> & H)| [] ].
      * rewrite <- app_assoc; simpl; apply good_app_left; now constructor 1.
      * apply good_app_left; now constructor 1.
      * apply good_app_left; now constructor 2.
  Qed.

  Fact good_snoc_inv l x : good (l++[x]) ↔ good l ∨ ∃y, y ∈ l ∧ R x y.
  Proof.
    rewrite good_app_inv; split.
    + intros [ | [ []%good_sg_inv | (? & ? & ? & [ <- | [] ] & ?) ] ]; eauto.
    + intros [ | (y & ? & ?) ]; eauto.
      do 2 right; exists y; split; eauto.
      exists x; eauto.
  Qed.
  
  Fact good_app_middle l m r : good (l++r) → good (l++m++r).
  Proof.
    intros [ | [ | (x & y & ?  & [])] ]%good_app_inv; apply good_app_inv; eauto.
    do 2 right; exists x; rewrite lowered_app_iff; split; auto; right; eexists; eauto.
  Qed.
  
  Hint Resolve good_app_middle : core.

  Fact bar_good_middle l m r : bar good (l++r) → bar good (l++m++r).
  Proof. revert l r; apply bar_app_middle; auto. Qed.

  Fact bar_good_app_head l r : bar good r → bar good (l++r).
  Proof. apply bar_good_middle with (l := []). Qed.

  Fact bar_good_skip_app x m r : bar good (x::r) → bar good (x::m++r).
  Proof. apply bar_good_middle with (l := [_]). Qed.

  Fact bar_good_skip_cons x y r : bar good (x::r) → bar good (x::y::r).
  Proof. apply bar_good_skip_app with (m := [_]). Qed.

End bar_good_middle.

Arguments idl {_}.
Arguments lowered {_}.
Arguments good {_}.

#[local] Hint Resolve in_map in_or_app : core.

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

  (** This is the over approximation proposed in [1] which does not
      have the shape good ? (combination of l, lx, ly)  *)

  Let θ lx ly l := good R lx ∨ good S ly ∨ good T l
                 ∨ (∃z, z ∈ l ∧ lowered R lx (fst z))
                 ∨ (∃z, z ∈ l ∧ lowered S ly (snd z))
                   .

  Hint Resolve good_app_middle in_or_app : core.

  Local Fact θ_app_middle lx ly l m r : θ lx ly (l++r) → θ lx ly (l++m++r).
  Proof.
    intros [ | [ | [ | [] ] ] ]; red; eauto.
    + destruct H as (z & []%in_app_iff & ?); do 3 right; left; exists z; split; eauto.
    + destruct H as (z & []%in_app_iff & ?); do 4 right; exists z; split; eauto.
  Qed.

  Hint Resolve θ_app_middle : core.

  Local Fact bar_θ_middle lx ly l m r : bar (θ lx ly) (l++r) → bar (θ lx ly) (l++m++r).
  Proof. apply bar_app_middle; auto. Qed.

  Local Fact bar_θ_app_left lx ly l r : bar (θ lx ly) r → bar (θ lx ly) (l++r).
  Proof. apply bar_app_middle with (l := []); auto. Qed.

  Local Fact bar_θ_cons_middle lx ly x m r : bar (θ lx ly) (x::r) → bar (θ lx ly) (x::m++r).
  Proof. apply bar_app_middle with (l := [x]); auto. Qed.

  (** We rework the shape of θ to give a more generic form *)

  Local Fact R_RS x x' : R x x' → RS (inX x) (inX x').   Proof. now simpl. Qed.
  Local Fact S_RS y y' : S y y' → RS (inY y) (inY y').   Proof. now simpl. Qed.
  Local Fact T_RS a b : T a b → RS (inXY a) (inXY b).    Proof. now simpl. Qed.

  Local Fact RS_R x x' : RS (inX x) (inX x') → R x x'.   Proof. now simpl. Qed.
  Local Fact RS_S y y' : RS (inY y) (inY y') → S y y'.   Proof. now simpl. Qed.
  Local Fact RS_T a b :  RS (inXY a) (inXY b) → T a b.   Proof. now simpl. Qed.

  Hint Resolve R_RS S_RS T_RS RS_R RS_S RS_T good_map good_app_left good_app_right good_map_inv : core.

  (** This equivalence is a *critical* observation when one wants to transfer
      the θ _ _ over-approximation of (good T) to ideals instead of relations 

      But it is not necessary for the proof of Ramsey below. *)

  Local Remark θ_iff_good lx ly l : θ lx ly l ↔ good RS (map inXY l++map inX lx++map inY ly).
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
        - do 3 right; left; exists (x',y'); split; auto; red; simpl; red; eauto.
        - do 4 right; exists (x',y'); split; auto; red; simpl; red; eauto.
  Qed.

  Hint Resolve good_monotone good_app_right
               in_or_app in_eq : core.
               
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
        apply map_split_inv in E as (m1 & z & m2 & ? & ? & ? & ?); subst.
        Search map eq cons app.
      admit.
    + intros x lx y ly m; unfold phi; simpl.
      admit.
  Admitted.

  Section nested_induction.

    Variables (lx : list X) (ly : list Y) (x : X) (y : Y).
    
    Local Lemma lem_ramsey_1' h l :
        (∀u, R x (fst u) → bar (θ lx ly) (u::l++[(x,y)]))
      → bar (θ (x::lx) ly) h
      → bar (θ lx ly) (h++l++[(x,y)]).
    Proof.
      intros H1 H2.
      rewrite bar_app_iff.
    Admitted.

    Local Lemma lem_ramsey_1 h l :
        (∀u, RS (inX x) (inXY u) → bar (θ lx ly) (u::l++[(x,y)]))
      → bar (θ (x::lx) ly) h
      → bar (θ lx ly) (h++l++[(x,y)]).
    Proof.
      intros G.
      induction 1 as [ h Hh | h _ IHh ].
      2: constructor 2; auto.
      destruct Hh as [ []%good_cons_inv | [ | [ | [Hh|(u & [])] ] ] ].
      1,2,3,4,6: constructor 1; red; auto.
      + do 3 right; left; eauto; exists (x,y); rewrite !in_app_iff; simpl; eauto.
      + do 4 right; eauto.
      + destruct Hh as (u & Hu & []%lowered_cons_inv); eauto.
        * apply in_split in Hu as (? & ? & ->).
          rewrite <- app_assoc; simpl.
          apply bar_θ_app_left, bar_θ_cons_middle; auto.
        * constructor 1; red.
          do 3 right; left; eauto.
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
        destruct Hl as [ | [ []%good_cons_inv | [ | [ (u & []) | (u & Hu & []%lowered_cons_inv) ] ] ] ]; red; eauto.
        * do 4 right; exists (x,y); split right; eauto.
        * do 3 right; left; exists u; split right; eauto.
        * specialize (H1 _ Hu).
          do 2 right; left.
          apply good_snoc_inv; right.
          exists u; split right; auto.
        * do 4 right; exists u; split right; eauto.
      + intros H1; apply lem_ramsey_1 with (h := []); eauto.
    Qed.

    Hypothesis (B2 : bar (θ lx (y::ly)) []).

    Local Lemma lemma_ramsey_3 : bar (θ lx ly) [(x,y)].
    Proof. apply lemma_ramsey_2 with (l := []); simpl; auto. Qed.

  End nested_induction.

  Local Lemma bar_compose lx ly : bar (good R) lx → bar (good S) ly → bar (θ lx ly) [].
  Proof.
    double bar induction as ? ?.
    + constructor 1; red; auto.
    + constructor 1; red; auto.
    + constructor 2; intros []; apply lemma_ramsey_3; auto.
  Qed.

  Local Fact bar_phi_good : bar (θ [] []) [] → bar (good T) [].
  Proof.
    apply bar_mono.
    intro; rewrite θ_iff_good; simpl; rewrite app_nil_r; eauto.
  Qed.

  Corollary ramsey : bar (good R) [] → bar (good S) [] → bar (good T) [].
  Proof. intros; now apply bar_phi_good, bar_compose. Qed.

End ramsey.

Check ramsey.
Print Assumptions ramsey.


  


