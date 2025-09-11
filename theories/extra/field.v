(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Ring Setoid Utf8.

Import ListNotations.

Require Import utils bar ring ideal bezout noetherian.

#[local] Hint Resolve in_eq in_cons : core.

(** How can we show that Q (the field of rationals) is Noetherian.
    Trivial because idl ⌞l⌟ is either {0} or the whole Q *)

Section fields.

  Variables (𝓕 : ring)
            (H𝓕 : ∀x : 𝓕, x ∼ᵣ 0ᵣ ∨ ∃y, y *ᵣ x ∼ᵣ 1ᵣ).

  Add Ring 𝓕_is_ring : (is_ring 𝓕).

  Local Fact req_list_choose l : (∃ x y : 𝓕, x ∈ l ∧ y *ᵣ x ∼ᵣ 1ᵣ) ∨ ∀x, x ∈ l → x ∼ᵣ 0ᵣ.
  Proof.
    destruct list_choice
      with (Q := λ x : 𝓕, ∃y, op_m y x ∼ᵣ un_m)
           (P := λ x : 𝓕, x ∼ᵣ un_a)
           (l := l)
      as [ (? & ? & []) | ]; eauto.
  Qed.

  Theorem field_bezout_ring : bezout_ring 𝓕.
  Proof.
    intros l.
    destruct (req_list_choose l)
      as [ (x & y & H1 & Hy) | H ].
    + exists un_m; intros z; split.
      * exists z; ring.
      * intros (k & ->).
        constructor 2 with (op_m (op_m k y) x).
        1: rewrite <- Hy; ring.
        constructor 5. 
        now constructor 1.
    + exists un_a; intros z; split.
      * apply idl_smallest.
        - apply ring_div_ideal.
        - intros ? ->%H; apply ring_div_refl.
      * intros (k & ->).
        constructor 2 with un_a; try ring.
        constructor 3.
  Qed.

  Theorem field_noetherian : noetherian 𝓕.
  Proof.
    constructor 2; intros x.
    destruct (H𝓕 x) as [ Hx | (z & Hz) ].
    + constructor 1; constructor 1.
      constructor 2 with un_a.
      * now rewrite Hx.
      * constructor 3.
    + constructor 2; intros y.
      constructor 1; constructor 1.
      constructor 2 with (op_m (op_m y z) x).
      * setoid_replace y with (op_m y un_m) at 2 by ring.
        rewrite <- Hz; ring.
      * constructor 5; constructor 1; auto.
  Qed.

End fields.

