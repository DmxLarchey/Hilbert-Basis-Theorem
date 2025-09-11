(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Ring Setoid Utf8.

Require Import utils bar ring product category ideal noetherian.

Import ListNotations.

(** This proof was inspired by a Rocq rework of the proof
    of the constructive form of Ramsey's theorem 

     [1] "Higman's lemma in Type theory", D. Fridlender
            in TYPES 1996

   which is expressed there as "the direct product of two
   almost full binary relations is almost full"

   See file ramsey.v herein for the Rocq rework of that
   proof in [1]. *)

#[local] Notation PA := pauses.

Section product_noetherian.

  Variables (𝓡 𝓣 : ring).
 
  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓣_is_ring : (is_ring 𝓣).

  Let 𝓟 := product_ring 𝓡 𝓣.

  Implicit Types (lx : list 𝓡) (ly : list 𝓣) (l : list 𝓟).

  Add Ring 𝓟_is_ring : (is_ring 𝓟).

  Let φ (x : 𝓡) : 𝓟 := (x,0ᵣ).
  Let ψ (y : 𝓣) : 𝓟 := (0ᵣ,y).

  Let π₁ (z : 𝓟) : 𝓡 := fst z.
  Let π₂ (z : 𝓟) : 𝓣 := snd z.

  (** Mostly obvious observations about π₁, π₂, φ and ψ *)

  Local Fact φ_sub_homo : ring_sub_homo φ.
  Proof. split right; simpl; ring || split; (auto || ring). Qed.

  Local Fact ψ_sub_homo : ring_sub_homo ψ.
  Proof. split right; simpl; ring || split; (auto || ring). Qed.

  Local Fact π₁_sub_homo : ring_sub_homo π₁.
  Proof. split right; simpl; ring || auto || tauto. Qed.

  Local Fact π₂_sub_homo : ring_sub_homo π₂.
  Proof. split right; simpl; ring || auto || tauto. Qed.

  (* May be the least trivial observation, by induction on l *)
  Local Lemma idl_π₁_π₂ l x y : idl ⌞map π₁ l⌟ x → idl ⌞map π₂ l⌟ y → idl ⌞l⌟ (x,y).
  Proof.
    rewrite !idl_iff_lc__list.
    induction l as [ | (u,v) l IHl ] in x, y |- *; simpl.
    + intros ?%lc_inv ?%lc_inv; constructor; split; auto.
    + intros (a & u' & H1 & H2)%lc_inv (b & v' & H3 & H4)%lc_inv.
      specialize (IHl _ _ H1 H3).
      constructor 2 with (a,b) (u',v'); auto.
      simpl; split; auto.
  Qed.

  Hint Resolve in_map : core.

  (* φ (π₁ z) = (1ᵣ,0ᵣ) *ᵣ z *)
  Local Fact idl_φ l z : idl ⌞l⌟ z → idl ⌞l⌟ (φ (π₁ z)).
  Proof.
    unfold π₁.
    constructor 2 with (x := ((1ᵣ,0ᵣ) : 𝓟) *ᵣ z); auto.
    split; simpl; ring.
  Qed.

  Hint Resolve in_or_app in_eq in_cons : core.

  Local Corollary idl_φ_π₁ l z r : idl ⌞l++φ (π₁ z)::r⌟ ⊆₁ idl ⌞l++z::r⌟.
  Proof.
    apply idl_closed.
    intros ? [ | [ <- | ] ]%in_app_iff.
    2: apply idl_φ.
    all: constructor 1; eauto.
  Qed.

  (* ψ (π₂ z) = (0ᵣ,1ᵣ) *ᵣ z *)
  Local Fact idl_ψ l z : idl ⌞l⌟ z → idl ⌞l⌟ (ψ (π₂ z)).
  Proof.
    unfold π₂.
    constructor 2 with (x := ((0ᵣ,1ᵣ) : 𝓟) *ᵣ z); auto.
    split; simpl; ring.
  Qed.

  Local Corollary idl_ψ_π₂ l z r : idl ⌞l++ψ (π₂ z)::r⌟ ⊆₁ idl ⌞l++z::r⌟.
  Proof.
    apply idl_closed.
    intros ? [ | [ <- | ] ]%in_app_iff.
    2: apply idl_ψ.
    all: constructor 1; eauto.
  Qed.

  Local Fact idl_φ_iff l x : idl ⌞map π₁ l⌟ x ↔ idl ⌞l⌟ (φ x).
  Proof.
    split.
    + intro; apply idl_π₁_π₂; auto.
    + intros H.
      apply idl_sub_homo with (1 := π₁_sub_homo) in H.
      revert H; simpl; apply idl_mono.
      intros ? (? & -> & ?); auto.
  Qed.

  Local Corollary idl_ψ_iff l y : idl ⌞map π₂ l⌟ y ↔ idl ⌞l⌟ (ψ y).
  Proof.
    split.
    + intro; apply idl_π₁_π₂; auto.
    + intros H.
      apply idl_sub_homo with (1 := π₂_sub_homo) in H.
      revert H; simpl; apply idl_mono.
      intros ? (? & -> & ?); auto.
  Qed.

  Local Corollary idl_φ_ψ l : ∀z, idl ⌞l⌟ (φ (π₁ z)) → idl ⌞l⌟ (ψ (π₂ z)) → idl ⌞l⌟ z.
  Proof. intros [] ?%idl_φ_iff ?%idl_ψ_iff; now apply idl_π₁_π₂. Qed.

  Hint Resolve idl_φ idl_ψ : core.

  Local Remark idl_φ_ψ_iff l x y : idl ⌞l⌟ (x,y) ↔ idl ⌞l⌟ (φ x) ∧ idl ⌞l⌟ (ψ y).
  Proof.
    change y with (snd (x,y)) at 2.
    change x with (fst (x,y)) at 2.
    generalize (x,y).
    split; eauto.
    intros []; now apply idl_φ_ψ.
  Qed.

  (** Now comes the non-trivial aspect of this proof:

      we define the "critical" parameterized over-approximation of PA
      which needed to be adapted from the proof of the constructive
      form of Ramsey's theorem in [1] (see ramsey.v):

      θ lx ly over-approximates PA, and matches PA when lx = ly = [] 

      Notice that in ramsey.v (hence for relations, not ideals), 
      θ lx ly is defined as (equivalent to)

           good RS (map inXY l++map inX lx++map inY ly)

      where RS an "obvious" extension of R and S on the type X*Y+X+Y
      (see θ_iff_good in ramsey.v).

      This equivalent form "is not" made explicit in [1] and is 
      rather obfuscated by overly complex notations and unnecessary
      auxiliary functions and hypotheses. Getting this form, as an
      instance of the "good" predicate, was essential be able to 
      convert the over approximation from relations to ideals.

      Indeed, as good    := MC (λ l x, ∃y, y ∈ l ∧ R y x)
              and pauses := MC (λ l x, idl ⌞l⌟ x), 
      we get a clear similarity here but we inject 𝓡 (resp. 𝓣) 
      into 𝓡*𝓣 using φ (resp. ψ) instead of the canonical injections 
      X → X*Y+X+Y and Y → X*Y.X+Y. *)

  Let θ lx ly l := PA (l++map φ lx++map ψ ly).

  Local Fact θ_monotone lx ly : monotone (θ lx ly).
  Proof. intros ? ? ?; now apply PA_monotone. Qed.

  Local Fact bar_θ_monotone lx ly : monotone (bar (θ lx ly)).
  Proof. apply bar_monotone, θ_monotone. Qed.

  Local Proposition bar_θ_nil_nil_PA : bar (θ [] []) ⊆₁ bar PA.
  Proof. apply bar_mono; intro; unfold θ; simpl; now rewrite app_nil_r. Qed.

  Section Ramsey_nested_induction.

    (** This part, with nested induction, largely differs for
        the corresponding one in ramsey.v, and is in fact
        simpler to obtain (IMHO), once you understand that
        you first have the consider the difficult base case 
        in bar_bar_ramsey. *)

    Hint Resolve in_or_app in_eq in_cons : core.

    Variables (lx : list 𝓡) (ly : list 𝓣) (z : 𝓡*𝓣).

    (** First observation: when π₂ z is in the
        ideal generated by ly, then we can deal with
        the case where the pause in

            m++[φ (π₁ z)]++map φ lx++map ψ ly

        occurs at φ (π₁ z), the other cases being
        trivial. *)

    Local Proposition idl_θ_ramsey m :
        idl ⌞ly⌟ (π₂ z)
      → θ (π₁ z::lx) ly m
      → θ lx ly (m++[z]).
    Proof.
      unfold θ; simpl; rewrite <- !app_assoc.
      intros Hz [ (l & u & r & -> & Hu) | [] ]%PA_middle_inv.
      + (* The pause occurs inside m *)
        rewrite <- app_assoc.
        apply PA_app_left.
        simpl; constructor 1.
        now apply idl_φ_π₁ in Hu.
      + (* The pause occurs at φ (π₁ z) *)
        apply PA_app_left.
        simpl; constructor 1.
        apply idl_φ_ψ; auto.
        apply idl_ψ_iff.
        rewrite map_app, !map_map; simpl; rewrite map_id.
        revert Hz; apply idl_mono; eauto.
      + (* The pause occurs inside map φ lx++map ψ ly *)
        now do 2 apply PA_app_left.
    Qed.

    Local Corollary idl_bar_ramsey m :
        idl ⌞ly⌟ (π₂ z)
      → bar (θ (π₁ z::lx) ly) m
      → bar (θ lx ly) (m++[z]).
    Proof.
      intros Hz Hm.
      apply bar_app_iff.
      revert m Hm; apply bar_mono.
      intro; now apply idl_θ_ramsey.
    Qed.

    (** Now we can proceed by induction on 
          bar (θ lx (π₂ z::ly)) m 
        and the difficulty lies only
        in the base case when the pause
        occurs at (π₂ z), and we use
        idl_bar_ramsey *)
 
    Local Proposition bar_bar_ramsey m :
        bar (θ lx (π₂ z::ly)) m
      → bar (θ (π₁ z::lx) ly) m
      → bar (θ lx ly) (m++[z]).
    Proof.
      induction 1 as [ m Hm | m _ IHm ].
      + red in Hm; simpl in Hm.
        apply PA_special_inv in Hm
          as [ (l & u & r & -> & Hu) 
           | [ (l' & v & r' & ? & Hv)
           | [ Hm | Hm ] ] ].
        * (* the pause occurs inside m *)
          intros _. (* no nested recursion needed *)
          constructor 1; red; simpl.
          repeat (rewrite <- !app_assoc; simpl).
          apply PA_app_left; constructor 1.
          rewrite app_assoc in Hu; apply idl_ψ_π₂ in Hu.
          revert u Hu; apply idl_mono.
          intro; simpl; repeat (rewrite !in_app_iff; simpl); tauto.
        * (* the pause occurs in map φ lx *)
          intros _. (* no nested recursion needed *)
          constructor 1; red; simpl.
          apply PA_app_left.
          apply map_split_inv in H as (l & u & r & -> & <- & <- & <-).
          rewrite map_app; simpl; rewrite <- app_assoc; simpl.
          apply PA_app_left; constructor 1.
          rewrite <- idl_φ_iff in Hv |- *.
          revert u Hv.
          rewrite !map_app; simpl; rewrite !map_map; simpl; rewrite !map_id.
          apply idl_closed; intros ? [ | [ <- | ] ]%in_app_iff; eauto.
        * (* the pause occurs at π₂ z *)
          apply idl_bar_ramsey. (* we use nested recursion *)
          apply idl_ψ_iff in Hm; revert Hm.
          rewrite map_map; simpl; now rewrite map_id.
        * (* the pause occurs in map ψ ly *)
          intros _. (* no nested recursion needed *)
          constructor 1; red; simpl.
          now do 2 apply PA_app_left.
      + (* directly using the induction hypothesis,
           provided that bar (θ _ _) is monotone *)
        constructor 2; intro; apply IHm.
        now apply bar_θ_monotone.
    Qed.

    Hypothesis (B1 : bar (θ (π₁ z::lx) ly) []).
    Hypothesis (B2 : bar (θ lx (π₂ z::ly)) []).

    Local Proposition bar_ramsey : bar (θ lx ly) [z].
    Proof. apply bar_bar_ramsey with (m := []); auto. Qed.

  End Ramsey_nested_induction.

  Hint Resolve φ_sub_homo ψ_sub_homo : core.

  (* This proceeds by simultaneous induction on bar PA lx and bar PA ly,
     and the proof sketch is nearly the same as in [1], see file 
     ramsey.v herein *)
  Local Lemma bar_PA__bar_θ lx ly : bar PA lx → bar PA ly → bar (θ lx ly) [].
  Proof.
    double bar induction as Hlx Hly.
    + constructor 1; red; simpl.
      apply PA_app_right.
      revert Hlx; apply PA_sub_homo; auto.
    + constructor 1; red; simpl.
      apply PA_app_left.
      revert Hly; apply PA_sub_homo; auto.
    + constructor 2; intro; apply bar_ramsey; auto.
  Qed.

  Theorem product_noetherian : noetherian 𝓡 → noetherian 𝓣 → noetherian 𝓟.
  Proof. intros; now apply bar_θ_nil_nil_PA, bar_PA__bar_θ. Qed.

End product_noetherian.

Check product_ring.
Check product_ring_correct.
Print is_product_ring.
Check product_noetherian.


  


