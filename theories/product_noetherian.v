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

  Hint Resolve in_map : core.

  Local Fact Idl_φ l z : Idl ⌞l⌟ z → Idl ⌞l⌟ (φ (fst z)).
  Proof.
    constructor 2 with (x := ((1ᵣ,0ᵣ) : 𝓟) *ᵣ z); auto.
    split; simpl; ring.
  Qed.

  Hint Resolve in_or_app in_eq in_cons : core.

  Local Corollary Idl_φ_fst l z r : Idl ⌞l++φ (fst z)::r⌟ ⊆₁ Idl ⌞l++z::r⌟.
  Proof.
    apply Idl_closed.
    intros ? [ | [ <- | ] ]%in_app_iff.
    2: apply Idl_φ.
    all: constructor 1; eauto.
  Qed.

  Local Fact Idl_ψ l z : Idl ⌞l⌟ z → Idl ⌞l⌟ (ψ (snd z)).
  Proof.
    constructor 2 with (x := ((0ᵣ,1ᵣ) : 𝓟) *ᵣ z); auto.
    split; simpl; ring.
  Qed.

  Local Corollary Idl_ψ_snd l z r : Idl ⌞l++ψ (snd z)::r⌟ ⊆₁ Idl ⌞l++z::r⌟.
  Proof.
    apply Idl_closed.
    intros ? [ | [ <- | ] ]%in_app_iff.
    2: apply Idl_ψ.
    all: constructor 1; eauto.
  Qed.

  Local Fact Idl_φ_iff l x : Idl ⌞map fst l⌟ x ↔ Idl ⌞l⌟ (φ x).
  Proof.
    split.
    + intro; apply Idl_fst_snd; auto.
    + intros H.
      apply Idl_sub_homo with (1 := fst_sub_homo) in H.
      revert H; simpl; apply Idl_mono.
      intros ? (? & -> & ?); auto.
 Qed.

  Local Corollary Idl_ψ_iff l y : Idl ⌞map snd l⌟ y ↔ Idl ⌞l⌟ (ψ y).
  Proof.
    split.
    + intro; apply Idl_fst_snd; auto.
    + intros H.
      apply Idl_sub_homo with (1 := snd_sub_homo) in H.
      revert H; simpl; apply Idl_mono.
      intros ? (? & -> & ?); auto.
  Qed.

  Local Corollary Idl_φ_ψ l z : Idl ⌞l⌟ (φ (fst z)) → Idl ⌞l⌟ (ψ (snd z)) → Idl ⌞l⌟ z.
  Proof.
    intros H1%Idl_φ_iff H2%Idl_ψ_iff.
    destruct z as (x,y); now apply Idl_fst_snd.
  Qed.

  Hint Resolve Idl_φ Idl_ψ : core.

  Local Remark Idl_φ_ψ_iff l x y :Idl ⌞l⌟ (x,y) ↔ Idl ⌞l⌟ (φ x) ∧ Idl ⌞l⌟ (ψ y).
  Proof.
    change y with (snd (x,y)) at 2.
    change x with (fst (x,y)) at 2.
    generalize (x,y).
    split; eauto.
    intros []; now apply Idl_φ_ψ.
  Qed.

  (** We define the essential parameterized approximation *)

   (* θ lx ly is an over-approximation of LD that matches LD with lx = ly = [] *)

  Let θ lx ly l := LD (l++map φ lx++map ψ ly).

  Local Fact bar_θ_nil_nil_LD : bar (θ [] []) ⊆₁ bar LD.
  Proof. apply bar_mono; intro; unfold θ; simpl; now rewrite app_nil_r. Qed.

  Hint Resolve Good_app_middle in_or_app : core.

  (* θ _ _ has insertion properties similar to LD *)
  Local Fact θ_app_middle lx ly l m r : θ lx ly (l++r) → θ lx ly (l++m++r).
  Proof. unfold θ; rewrite <- !app_assoc; apply LD_app_middle. Qed.

  Hint Resolve θ_app_middle : core.

  (** Hence we can work as smoolthy with bar (θ _ _) as with bar LD _ *)
 
  Local Lemma bar_θ_app_middle lx ly l m r : bar (θ lx ly) (l++r) → bar (θ lx ly) (l++m++r).
  Proof. apply bar_app_middle; auto. Qed.

  (** Consequences *)

  Local Fact bar_θ_app_left lx ly l r : bar (θ lx ly) r → bar (θ lx ly) (l++r).
  Proof. apply bar_app_middle with (l := []); auto. Qed.

  Local Fact bar_θ_cons_middle lx ly x m r : bar (θ lx ly) (x::r) → bar (θ lx ly) (x::m++r).
  Proof. apply bar_app_middle with (l := [_]); auto. Qed.

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
        * rewrite <- app_assoc.
          apply bar_θ_app_left.
          constructor 1; red; simpl; constructor 1.
          rewrite <- app_assoc.
          now apply Idl_φ_fst in Hh.
        * apply bar_θ_app_left.
          constructor 1; red; simpl; constructor 1.
          apply Idl_φ_ψ; auto.
          apply Idl_ψ_iff.
          rewrite map_app, !map_map; simpl; rewrite map_id.
          revert Hz; apply Idl_mono; eauto.
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
        * intros _; rewrite <- app_assoc; simpl.
          apply bar_θ_app_left.
          constructor 1; red; simpl; constructor 1.
          rewrite app_assoc in Hv; apply Idl_ψ_snd in Hv.
          rewrite <- app_assoc.
          revert v Hv; apply Idl_mono.
          intro; simpl; repeat (rewrite !in_app_iff; simpl); tauto.
        * intros _; apply bar_θ_nil; constructor 1; red; simpl.
          apply map_split_inv in H as (l' & p & r' & -> & <- & <- & <-).
          rewrite map_app; simpl; rewrite <- app_assoc; simpl.
          apply LD_app_left; constructor 1.
          rewrite <- Idl_φ_iff in Hv |- *.
          revert p Hv.
          rewrite !map_app; simpl; rewrite !map_map; simpl; rewrite !map_id.
          apply Idl_closed; intros ? [ | [ <- | ] ]%in_app_iff; eauto.
        * apply Ramsey_1.
          apply Idl_ψ_iff in Hl; revert Hl.
          rewrite map_map; simpl; now rewrite map_id.
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


  


