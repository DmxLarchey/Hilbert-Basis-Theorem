(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Ring Setoid Utf8.

Require Import utils bar ring ideal principal noetherian.

Import ListNotations.

#[local] Notation LD := linearly_dependent.

Inductive seq {A} (P : list A → A → Prop) : list A → Prop :=
  | seq_nil : seq P []
  | seq_cons a l : P l a → seq P l → seq P (a::l).

Section ramsey.

  Variables (𝓡 𝓣 : ring).
 
  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓣_is_ring : (is_ring 𝓣).

  Let 𝓟 := product_ring 𝓡 𝓣.

  Implicit Types (lx : list 𝓡) (ly : list 𝓣) (l : list 𝓟).

  Add Ring 𝓟_is_ring : (is_ring 𝓟).
  
  Let shomo_x (x : 𝓡) : 𝓟 := (x,0ᵣ).
  Let shomo_y (y : 𝓣) : 𝓟 := (0ᵣ,y).

  Local Fact shomo_x_shomo : ring_sub_homo shomo_x.
  Proof. split right; simpl; ring || split; (auto || ring). Qed.
  
  Local Fact shomo_y_shomo : ring_sub_homo shomo_y.
  Proof. split right; simpl; ring || split; (auto || ring). Qed.

  Let phi lx  ly l := @LD 𝓟 (l ++ map shomo_x lx ++ map shomo_y ly).

  Hint Resolve Good_app_middle in_or_app : core.

  Local Fact phi_app_middle lx ly l m r : phi lx ly (l++r) → phi lx ly (l++m++r).
  Proof. unfold phi. rewrite <- !app_assoc. apply LD_app_middle. Qed.

  Hint Resolve phi_app_middle : core.
  
  Local Fact bar_phi_middle lx ly l m r : bar (phi lx ly) (l++r) → bar (phi lx ly) (l++m++r).
  Proof. apply bar_app_middle; auto. Qed.
  
  Local Fact bar_phi_app_left lx ly l r : bar (phi lx ly) r → bar (phi lx ly) (l++r).
  Proof. apply bar_app_middle with (l := []); auto. Qed.
  
  Local Fact bar_phi_cons_middle lx ly x m r : bar (phi lx ly) (x::r) → bar (phi lx ly) (x::m++r).
  Proof. apply bar_app_middle with (l := [x]); auto. Qed.
  
  Local Fact bar_phi_nil lx ly l : bar (phi lx ly) [] → bar (phi lx ly) l.
  Proof. rewrite <- (app_nil_r l); apply bar_app_middle with (l := []); auto. Qed.

  Hint Resolve in_or_app in_eq : core.

  Section nested_induction.

    Variables (lx : _) (ly : _) (z : 𝓡*𝓣).
    
    Local Lemma lemma_ramsey_0 l :
        Idl ⌞ly⌟ (snd z)
      → bar (phi (fst z::lx) ly) l
      → bar (phi lx ly) (l++[z]).
    Proof.
      intros Hz.
      induction 1 as [ l Hl | l _ IHl ].
      + red in Hl; simpl in Hl.
        apply LD_special_inv in Hl as [ (h1 & k & h2 & -> & Hh)| [|] ].
        * rewrite <- app_assoc; apply bar_phi_app_left.
          constructor 1; red; simpl. constructor 1.
          admit. (* use 0 for the fst of the coef of z *)
        * (* we have Idl ⌞lx⌟ (fst z) (by projecting H) 
                 and Idl ⌞ly⌟ (snd z) (Hz)
                 hence Idl ⌞map shomo_x lx++map shomoe_y ly⌟ z *)
          apply bar_phi_app_left.
          constructor 1; red; simpl; constructor 1.
          admit.
        * apply bar_phi_nil; now constructor 1.
      + now constructor 2.
    Admitted. 
    
    Variables (P : list 𝓟 -> Prop) (Q : list 𝓟 -> 𝓟 -> Prop)
              (HP0 : P [])
              (HP1 : forall a l, Q l a -> P l -> P (a::l)).

    Local Lemma lem_ramsey_1 h l :
        (∀u, Q l u → bar (phi lx ly) (u::l++[z]))
      → bar (phi (fst z::lx) ly) h
      → bar (phi lx ly) (h++l++[z]).
    Proof.
      intros G.
      induction 1 as [ h Hh | h _ IHh ].
      2: constructor 2; auto.
      red in Hh; simpl in Hh.
      apply LD_special_inv in Hh as [ (h1 & k & h2 & -> & Hh)| [|] ].
      + rewrite <- !app_assoc; simpl.
        apply bar_phi_app_left, bar_phi_cons_middle.
        apply G.
        admit.
      + apply bar_phi_app_left.
        constructor 2.
      constructor 1; red.
        admit.
      + constructor 1; red.
        now apply LD_app_left.
    Admitted.
 
    Hypothesis (B1 : bar (phi (fst z::lx) ly) []).
    
    Local Lemma lemma_ramsey_2 l :
        P l 
        (* seq (fun h u => Idl ⌞map fst h++fst z::lx⌟ (fst u)) l *)
      → bar (phi lx (snd z::ly)) l
      → bar (phi lx ly) (l++[z]).
    Proof.
      intros H1 H2; revert H2 H1.
      induction 1 as [ l Hl | l _ IHl ].
      + intros H1; red in Hl; simpl in Hl.
        apply LD_app_inv in Hl as [ (l' & k & m' & -> & Hl) | Hl ].
        * constructor 1.
          red; simpl; rewrite <- !app_assoc.
          apply LD_app_left; simpl; constructor 1.
          admit. (* use zero for the fst of the coefficient of z *)
        * apply LD_special_inv in Hl as [ (l1 & a1 & r1 & E & Hl) | [ Hl | Hl] ].
          - constructor 1; red; simpl.
            apply map_split_inv in E as (l2 & a2 & r2 & -> & <- & <- & <-).
            rewrite map_app; simpl; rewrite <- !app_assoc.
            do 3 apply LD_app_left; simpl; constructor 1.
            admit. (* shomo_y (snd z) is 0 on the fst component and we do not care about the second *)
          - apply lemma_ramsey_0.
            ++ admit. (* projecting Hl *)
            ++ now apply bar_phi_nil.
          - constructor 1.
            red.
            now do 2 apply LD_app_left.
      + intros Hl.
        apply lem_ramsey_1 with (h := []); auto.
        intros ? ?; apply IHl; auto.
    Admitted.

    Hypothesis (B2 : bar (phi lx (snd z::ly)) []).
    
    Hint Constructors seq : core.

    Local Lemma lemma_ramsey_3 : bar (phi lx ly) [z].
    Proof. apply lemma_ramsey_2 with (l := []); auto. Qed.

  End nested_induction.
  
 
  Hint Resolve shomo_x_shomo shomo_y_shomo : core.

  Local Lemma bar_compose lx ly : bar LD lx → bar LD ly → bar (phi lx ly) [].
  Proof.
    intros H1 H2; pattern lx, ly; revert lx ly H1 H2; apply bar_double_ind.
    + intros lx ly H; constructor 1; red; simpl.
      apply LD_app_right.
      revert H; apply LD_sub_homo; auto.
    + intros lx ly H; constructor 1; red; simpl.
      apply LD_app_left.
      revert H; apply LD_sub_homo; auto.
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


  


