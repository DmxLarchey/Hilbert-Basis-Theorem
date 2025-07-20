(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Ring Setoid Utf8.

Require Import utils bar ring product category ideal principal noetherian.

Import ListNotations.

#[local] Notation LD := linearly_dependent.

Section product_noetherian.

  Variables (𝓡 𝓣 : ring).
 
  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓣_is_ring : (is_ring 𝓣).

  Let 𝓟 := product_ring 𝓡 𝓣.

  Implicit Types (lx : list 𝓡) (ly : list 𝓣) (l : list 𝓟).

  Add Ring 𝓟_is_ring : (is_ring 𝓟).

  Let φ (x : 𝓡) : 𝓟 := (x,0ᵣ).
  Let ψ (y : 𝓣) : 𝓟 := (0ᵣ,y).
  
  (* φψ *)

  Local Fact φ_sub_homo : ring_sub_homo φ.
  Proof. split right; simpl; ring || split; (auto || ring). Qed.
  
  Local Fact ψ_sub_homo : ring_sub_homo ψ.
  Proof. split right; simpl; ring || split; (auto || ring). Qed.

  Local Fact fst_sub_homo : @ring_sub_homo 𝓟 𝓡 fst.
  Proof. split right; simpl; ring || auto || tauto. Qed.

  Local Fact snd_sub_homo : @ring_sub_homo 𝓟  𝓣 snd.
  Proof. split right; simpl; ring || auto || tauto. Qed.

  Local Lemma Idl_fst_snd l x y : Idl ⌞map fst l⌟ x → Idl ⌞map snd l⌟ y → Idl ⌞l⌟ (x,y).
  Proof.
    rewrite !Idl_iff_lc__list.
    induction l as [ | (u,v) l IHl ] in x, y |- *; simpl.
    + intros ?%lc_inv ?%lc_inv; constructor; split; auto.
    + intros (a & u' & H1 & H2)%lc_inv (b & v' & H3 & H4)%lc_inv.
      specialize (IHl _ _ H1 H3).
      constructor 2 with (a,b) (u',v'); auto.
      simpl; split; auto.
  Qed.

  Local Corollary Idl_φ l x : Idl ⌞map fst l⌟ x → Idl ⌞l⌟ (φ x).
  Proof. intro; apply Idl_fst_snd; auto. Qed.
  
  Local Corollary Idl_ψ l y : Idl ⌞map snd l⌟ y → Idl ⌞l⌟ (ψ y).
  Proof. intro; apply Idl_fst_snd; auto. Qed.
 
  Hint Resolve in_map : core.

  Local Corollary Idl_φ_ψ l z : Idl ⌞l⌟ (φ (fst z)) → Idl ⌞l⌟ (ψ (snd z)) → Idl ⌞l⌟ z.
  Proof.
    intros H1 H2.
    destruct z as (x,y).
    apply Idl_fst_snd.
    + apply Idl_sub_homo with (1 := fst_sub_homo) in H1.
      revert H1; simpl; apply Idl_mono.
      intros ? (? & -> & ?); auto.
    + apply Idl_sub_homo with (1 := snd_sub_homo) in H2.
      revert H2; simpl; apply Idl_mono.
      intros ? (? & -> & ?); auto.
  Qed.

  Local Remark Idl_φ_ψ_iff l x y :Idl ⌞l⌟ (x,y) ↔ Idl ⌞l⌟ (φ x) ∧ Idl ⌞l⌟ (ψ y).
  Proof.
    split.
    + split.
      * constructor 2 with (x := ((1ᵣ,0ᵣ) : 𝓟) *ᵣ (x,y)); auto.
        split; simpl; ring.
      * constructor 2 with (x := ((0ᵣ,1ᵣ) : 𝓟) *ᵣ (x,y)); auto.
        split; simpl; ring.
    + intros []; now apply Idl_φ_ψ.
  Qed.

  Let θ lx ly l := LD (l++map φ lx++map ψ ly).

  (* θ lx ly is an over-approximation of LD that matches LD with lx = ly = [] *)
  Local Fact bar_θ_nil_nil_LD : bar (θ [] []) ⊆₁ bar LD.
  Proof. apply bar_mono; intro; unfold θ; simpl; now rewrite app_nil_r. Qed.

  Hint Resolve Good_app_middle in_or_app : core.

  (* θ _ _ has insertion properties similar to LD *)
  Local Fact θ_app_middle lx ly l m r : θ lx ly (l++r) → θ lx ly (l++m++r).
  Proof. unfold θ; rewrite <- !app_assoc; apply LD_app_middle. Qed.

  Hint Resolve θ_app_middle : core.

  (** Hence we can work as smoolthy with bar (θ _ _) as with bar LD _ *)
 
  Local Fact bar_θ_middle lx ly l m r : bar (θ lx ly) (l++r) → bar (θ lx ly) (l++m++r).
  Proof. apply bar_app_middle; auto. Qed.

  Local Fact bar_θ_app_left lx ly l r : bar (θ lx ly) r → bar (θ lx ly) (l++r).
  Proof. apply bar_app_middle with (l := []); auto. Qed.

  Local Fact bar_θ_cons_middle lx ly x m r : bar (θ lx ly) (x::r) → bar (θ lx ly) (x::m++r).
  Proof. apply bar_app_middle with (l := [x]); auto. Qed.

  Local Fact bar_θ_cons lx ly x m : bar (θ lx ly) m → bar (θ lx ly) (x::m).
  Proof. apply bar_θ_app_left with (l := [_]); auto. Qed.

  Local Fact bar_θ_nil lx ly l : bar (θ lx ly) [] → bar (θ lx ly) l.
  Proof. rewrite <- (app_nil_r l); apply bar_app_middle with (l := []); auto. Qed.

  Section Ramsey_nested_induction.

    Hint Resolve in_or_app in_eq in_cons : core.

    Variables (lx : _) (ly : _) (z : 𝓡*𝓣).

    Local Lemma Ramsey_1 l :
        Idl ⌞ly⌟ (snd z)
      → bar (θ (fst z::lx) ly) l
      → bar (θ lx ly) (l++[z]).
    Proof.
      intros Hz.
      induction 1 as [ l Hl | l _ IHl ].
      + red in Hl; simpl in Hl.
        apply LD_middle_inv in Hl as [ (h1 & k & h2 & -> & Hh)| [|] ].
        * rewrite <- app_assoc; apply bar_θ_app_left.
          constructor 1; red; simpl. constructor 1.
          revert k Hh.
          apply Idl_smallest.
          1: apply Idl_ring_ideal.
          intros k; rewrite in_app_iff; simpl.
          intros [ H | [ <- | H ] ].
          - constructor 1; eauto.
          - constructor 2 with (((1ᵣ,0ᵣ) : 𝓟) *ᵣ z).
            1: destruct z; simpl; split; ring.
            constructor 5; constructor 1; eauto.
          - constructor 1; eauto.
        * apply bar_θ_app_left.
          constructor 1; red; simpl; constructor 1.
          apply Idl_φ_ψ; auto.
          apply Idl_ψ.
          revert Hz; apply Idl_mono.
          intros y ?; rewrite map_app, !map_map, in_app_iff.
          right; simpl; now rewrite map_id.
        * apply bar_θ_nil; now constructor 1.
      + now constructor 2.
    Qed.
 
    Local Lemma Ramsey_2 l :
        bar (θ lx (snd z::ly)) l
      → bar (θ (fst z::lx) ly) l
      → bar (θ lx ly) (l++[z]).
    Proof.
      induction 1 as [ l Hl | l _ IHl ].
      + red in Hl; simpl in Hl.
        apply LD_special_inv in Hl
          as [ (l1 & v & l2 & -> & Hv) 
           | [ (l1 & v & l2 & ? & Hv)
           | [ Hl | Hl ] ] ].
        * intros _; rewrite <- app_assoc.
          apply bar_θ_app_left.
          constructor 1; red; simpl.
          constructor 1.
          revert v Hv; apply Idl_smallest; [ apply Idl_ring_ideal | ].
          intros k; rewrite !in_app_iff; simpl.
          intros [ | [ | [ <- | ] ] ].
          1,2,4: constructor 1; eauto.
          constructor 2 with (((0ᵣ,1ᵣ) : 𝓟) *ᵣ z).
          1: destruct z; simpl; split; ring.
          constructor 5; constructor 1; eauto.
        * (* v is of shape (_,0) hence snd z does not contribute *)
          intros _; apply bar_θ_nil; constructor 1; red; simpl.
          apply map_split_inv in H as (l' & p & r' & -> & <- & <- & <-).
          rewrite map_app; simpl; rewrite <- app_assoc; simpl.
          apply LD_app_left; constructor 1.
          apply Idl_φ.
          apply Idl_sub_homo with (1 := fst_sub_homo) in Hv.
          rewrite map_app, !map_map; simpl; rewrite map_id.
          revert p Hv; simpl; apply Idl_smallest; [ apply Idl_ring_ideal | ].
          intros ? (? & -> & [ (? & <- & ?)%in_map_iff | [ <- | (? & <- & ?)%in_map_iff ] ]%in_app_iff); simpl.
          2,3: constructor 3.
          constructor 1; auto.
        * apply Ramsey_1.
          apply Idl_sub_homo with (1 := snd_sub_homo) in Hl.
          revert Hl; simpl; apply Idl_mono.
          intros ? (? & -> & (? & <- & ?)%in_map_iff); auto.
        * intros _; apply bar_θ_nil.
          constructor 1; red; simpl.
          now apply LD_app_left.
      + constructor 2; intro; apply IHl.
        now apply bar_θ_cons.
    Qed.

    Hypothesis (B1 : bar (θ (fst z::lx) ly) []).
    Hypothesis (B2 : bar (θ lx (snd z::ly)) []).

    Local Lemma Ramsey_3 : bar (θ lx ly) [z].
    Proof. apply Ramsey_2 with (l := []); auto. Qed.

  End Ramsey_nested_induction.

  Hint Resolve φ_sub_homo ψ_sub_homo : core.

  Local Lemma bar_LD__bar_θ lx ly : bar LD lx → bar LD ly → bar (θ lx ly) [].
  Proof.
    intros H1 H2; pattern lx, ly; revert lx ly H1 H2; apply bar_double_ind.
    + intros lx ly H; constructor 1; red; simpl.
      apply LD_app_right.
      revert H; apply LD_sub_homo; auto.
    + intros lx ly H; constructor 1; red; simpl.
      apply LD_app_left.
      revert H; apply LD_sub_homo; auto.
    + constructor 2; intro; apply Ramsey_3; auto.
  Qed.

  Theorem product_noetherian : noetherian 𝓡 → noetherian 𝓣 → noetherian 𝓟.
  Proof. intros; now apply bar_θ_nil_nil_LD, bar_LD__bar_θ. Qed.

End product_noetherian.

Check product_ring.
Check product_ring_correct.
Check product_noetherian.


  


