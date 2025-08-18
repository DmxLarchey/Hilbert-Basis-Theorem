(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

Import ListNotations.

Require Import utils bar.

Section MC_and_bar.

  (** monotone_closure (P : rel (list A) A) : rel₁ (list A) (denoted MC)
      subsumes good (R : rel₂ A) : rel₁ (list A), the notion of good (finite) sequence for a binary relation R
      and LD (𝓡 : ring) : rel₁ (list 𝓡), the notion of linearly dependent sequence in a ring 𝓡 *)  

  Variables (A : Type).

  Implicit Types (P Q : list A → A → Prop).

  Inductive monotone_closure P : list A → Prop :=
    | monotone_closure_stop a l : P l a                → monotone_closure P (a::l)
    | monotone_closure_skip a l : monotone_closure P l → monotone_closure P (a::l)
    .

  Notation MC := monotone_closure.

  Hint Constructors MC : core.

  Fact MC_inv P l :
      MC P l
    → match l with
      | []   => False
      | a::l => P l a ∨ MC P l
      end.
  Proof. destruct 1; eauto. Qed.

  Fact MC_cons_inv P x l : MC P (x::l) ↔ P l x ∨ MC P l.
  Proof.
    split.
    + apply MC_inv.
    + intros []; eauto.
  Qed.

  Fact MC_monotone P : monotone (MC P).
  Proof. now constructor 2. Qed.

  Fact MC_mono P Q : P ⊆₂ Q → MC P ⊆₁ MC Q.
  Proof. induction 2; eauto. Qed.

  Fact MC_app_left P l r : MC P r → MC P (l++r).
  Proof. intro; induction l; simpl; eauto. Qed.

  Fact MC_app_right P r : 
      (∀ l x, P l x → P (l++r) x)
    → (∀l, MC P l → MC P (l++r)).
  Proof. induction 2; simpl; eauto. Qed.

  Hint Resolve MC_app_left : core.

  (* Another characterization (in FOL) *)
  Lemma MC_split P m : MC P m ↔ ∃ l a r, m = l++a::r ∧ P r a.
  Proof.
    split.
    + induction 1 as [ a m H | a m _ (l & b & r & -> & H) ].
      * now exists [], a, m.
      * now exists (a::l), b, r.
    + intros (? & ? & ? & -> & ?); auto.
  Qed.

  Lemma MC_app_inv P l r : MC P (l++r) ↔ (∃ l' a m, l = l'++a::m ∧ P (m++r) a) ∨ MC P r.
  Proof.
    induction l as [ | x l IHl ]; simpl.
    + split; auto; now intros [ ([] & ? & ? & ? & _) | ].
    + rewrite MC_cons_inv, IHl; split.
      * intros [ H1 | [ (l' & y & m & -> & ?) | H1 ] ]; eauto.
        - left; now exists [], x, l.
        - left; now exists (x::l'), y, m.
      * intros [ ([ | z l'] & y & m & [=] & ?) | ]; subst; auto.
        right; left; now exists l', y, m.
  Qed.

  Hint Resolve bar_monotone : core.

  Fact bar_MC_app_left P l m : bar (MC P) m → bar (MC P) (l++m).
  Proof. apply bar_app_left; eauto. Qed.

  Section MC_app_middle.

    Variables (P : list A → A → Prop) (m : list A)
              (P_app_middle : ∀ l r a, P (l++r) a → P (l++m++r) a).

    Fact MC_app_middle l r : MC P (l++r) → MC P (l++m++r).
    Proof. induction l; simpl; eauto; intros []%MC_inv; auto. Qed.

    Hint Resolve MC_app_middle bar_app_middle : core.

    Fact bar_MC_app_middle l r : bar (MC P) (l++r) → bar (MC P) (l++m++r).
    Proof. eauto. Qed.

  End MC_app_middle.

End MC_and_bar.

Arguments monotone_closure {_}.

#[global] Notation MC := monotone_closure.

