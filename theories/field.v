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

Require Import utils bar ring ideal principal noetherian.

#[local] Hint Resolve in_eq in_cons : core.

(** How can we show that Q (the field of rationals) is Noetherian.
    Trivial because Idl ⌞l⌟ is either {0} or the whole Q *)

Section fields.

  Variables (F : ring)
            (HF : ∀x : F, x ∼ᵣ 0ᵣ ∨ ∃y, y *ᵣ x ∼ᵣ 1ᵣ).

  Add Ring R_is_ring : (is_ring F).

  Local Fact req_list_choose l : (∃ x y : F, x ∈ l ∧ y *ᵣ x ∼ᵣ 1ᵣ) ∨ ∀x, x ∈ l → x ∼ᵣ 0ᵣ.
  Proof.
    destruct list_choice
      with (Q := λ x : F, ∃y, op_m y x ∼ᵣ un_m)
           (P := λ x : F, x ∼ᵣ un_a)
           (l := l)
      as [ | (? & ? & []) ]; eauto.
  Qed.

  Theorem field_principal : principal F.
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
      * apply Idl_smallest.
        - apply ring_div_ideal.
        - intros ? ->%H; apply ring_div_refl.
      * intros (k & ->).
        constructor 2 with un_a; try ring.
        constructor 3.
  Qed.

  Theorem field_noetherian : noetherian F.
  Proof.
    constructor 2; intros x.
    destruct (HF x) as [ Hx | (z & Hz) ].
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

