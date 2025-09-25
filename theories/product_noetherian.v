(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
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
  
  Hint Resolve φ_sub_homo ψ_sub_homo idl__ideal : core.

  Theorem product_noetherian : noetherian 𝓡 → noetherian 𝓣 → noetherian 𝓟.
  Proof.
    unfold noetherian.
    intros H1 H2.
    set (phi lx ly l :=  l ++ map φ lx ++ map ψ ly).
    cut (bar (fun m => PA (phi [] [] m)) []).
    + apply bar_mono.
      intros m; unfold phi; simpl.
      now rewrite app_nil_r.
    + revert H1 H2; apply bar_ramsey.
      * intros ? ? ? ?; apply PA_monotone.
      * intros lx ly ?; unfold phi; simpl.
        rewrite <- app_nil_r, <- app_assoc.
        apply PA_app_middle.
        rewrite app_nil_r.
        apply PA_sub_homo; auto.
      * intros lx ly ?; unfold phi; simpl.
        apply PA_app_left, PA_sub_homo; auto.
      * intros x lx y ly m [H1|H1]%PA_cons_inv.
        - unfold phi; simpl; rewrite <- app_assoc.
          intros [ (m1 & z & m2 & -> & H2) | [ H2 | H2 ] ]%PA_middle_inv.
          ++ rewrite <- app_assoc; simpl.
             apply PA_app_left, PA_cons_inv; left.
             now apply idl_φ_π₁.
          ++ apply PA_app_left, PA_cons_inv; left.
             apply idl_φ_ψ_iff; split; auto.
             apply idl_mono with (P := ⌞map ψ ly⌟); eauto.
             apply idl_ψ_iff; now rewrite map_map, map_id.
          ++ now do 2 apply PA_app_left.
        - intros _.
          unfold phi.
          do 2 apply PA_app_left.
          apply PA_sub_homo; auto.
      * intros x lx y ly m; unfold phi; simpl.
        intros [ (m1 & z & m2 & -> & H1) | [ (m1 & z & m2 & (lx1 & x' & lx2 & ?)%map_split_inv & H1) | [ H1 | H1 ] ] ]%PA_special_inv.
        - left.
          rewrite <- !app_assoc; simpl.
          apply PA_app_left, PA_cons_inv; left.
          revert H1; apply idl_smallest.
          ++ apply idl__ideal.
          ++ intros k; simpl; rewrite !in_app_iff; simpl.
             intros [ | [ | [ <- | ] ] ]; eauto.
             ** constructor 1; repeat (rewrite in_app_iff; simpl); auto.
             ** apply idl_ψ_iff; constructor 1.
                rewrite map_app; simpl; eauto.
             ** constructor 1; repeat (rewrite in_app_iff; simpl); auto.
        - left.
          destruct H as (-> & <- & <- & <-).
          rewrite map_app, <- !app_assoc.
          do 3 apply PA_app_left; simpl.
          apply PA_cons_inv; left.
          rewrite <- ! idl_φ_iff in H1 |- *.
          rewrite map_app, map_map in H1 |- *.
          simpl in H1.
          revert x' H1.
          apply idl_smallest; auto.
          intro; rewrite in_app_iff; simpl.
          intros [ | [<- | ] ]; eauto.
        - right; apply PA_cons_inv; left.
          apply idl_ψ_iff in H1.
          now rewrite map_map, map_id in H1.
        - left; now do 2 apply PA_app_left.
  Qed.

End product_noetherian.

Check product_ring.
Check product_ring_correct.
Print is_product_ring.
Check product_noetherian.


  


