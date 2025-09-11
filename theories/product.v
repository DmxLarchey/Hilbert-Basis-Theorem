(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Ring ZArith Setoid Utf8.

Require Import utils ring category.

Set Implicit Arguments.

(** Definition of the product ring and its characteristic property *)

Section product_ring.

  Variables (𝓡 𝓣 : ring).
 
  Add Ring 𝓡_is_ring : (is_ring 𝓡).
  Add Ring 𝓣_is_ring : (is_ring 𝓣).

  Let 𝓟 := (𝓡 * 𝓣)%type.
  Let pun_a : 𝓟 := (0ᵣ,0ᵣ).
  Let pop_a (a b : 𝓟) : 𝓟 := (fst a +ᵣ fst b,snd a +ᵣ snd b).
  Let piv_a (a : 𝓟) : 𝓟 := (-ᵣ fst a, -ᵣ snd a).
  Let pun_m : 𝓟 := (1ᵣ,1ᵣ).
  Let pop_m (a b : 𝓟) : 𝓟 := (fst a *ᵣ fst b,snd a *ᵣ snd b).
  Let prel (a b : 𝓟) : Prop := fst a ∼ᵣ fst b ∧ snd a ∼ᵣ snd b.

  Local Fact 𝓟_equiv : Equivalence prel.
  Proof.
    split; unfold prel.
    + intros []; simpl; auto.
    + intros [] []; simpl; intros []; auto.
    + intros [] [] []; simpl; intros [] []; eauto.
  Qed.

  Tactic Notation "solve" :=
    repeat match goal with 
    | |- forall _ : 𝓟, _ => intros []
    end; simpl; split; ring.

  Local Fact 𝓟_ring : ring_theory pun_a pun_m pop_a pop_m (λ x y : 𝓟, pop_a x (piv_a y)) piv_a prel.
  Proof. split; unfold prel; solve. Qed.

  Local Fact 𝓟_ring_ext : ring_eq_ext pop_a pop_m piv_a prel.
  Proof.
    split; unfold prel.
    1,2: intros [] [] (E1 & E2) [] [] (E3 & E4); simpl in *; rewrite E1, E2, E3, E4; split; ring.
    intros [] [] (E1 & E2); simpl in *; rewrite E1, E2; split; ring.
  Qed.

  Hint Resolve 𝓟_equiv 𝓟_ring 𝓟_ring_ext : core.

  Definition product_ring : ring.
  Proof.
    exists 𝓟 pun_a pop_a piv_a pun_m pop_m prel; abstract auto.
  Defined.

  Fact product_ring_fst_homo : @ring_homo product_ring 𝓡 fst.
  Proof.
    split right; simpl; auto.
    intros [] [] []; auto.
  Qed.

  Fact product_ring_snd_homo : @ring_homo product_ring 𝓣 snd.
  Proof.
    split right; simpl; auto.
    intros [] [] []; auto.
  Qed.
  
  Hint Resolve pd_fst_homo pd_snd_homo : core.

  Theorem product_ring_correct :
    is_product_ring 𝓡 𝓣 
      {| pd_ring := product_ring;
         pd_fst := fst;
         pd_snd := snd;
         pd_fst_homo := product_ring_fst_homo;
         pd_snd_homo := product_ring_snd_homo;
      |}.
  Proof.
    split; simpl.
    + exists (fun q => (pd_fst 𝓠 q, pd_snd 𝓠 q)).
      split right; simpl; auto.
      split right; simpl.
      * split; simpl.
        - now apply pd_fst_homo.
        - now apply pd_snd_homo.
      * intros ? ?; split; simpl.
        - now apply pd_fst_homo.
        - now apply pd_snd_homo.
      * intros ? ?; split; simpl.
        - now apply pd_fst_homo.
        - now apply pd_snd_homo.
      * apply pd_fst_homo.
      * apply pd_snd_homo.
    + intros al be (H1 & H2 & H3) (G1 & G2 & G3) r; simpl in *; split.
      * now rewrite H2, G2.
      * now rewrite H3, G3.
  Qed.

End product_ring.
