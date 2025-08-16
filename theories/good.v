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

Section Good_and_bar.

  (** The generalization of good : rel₂ X → rel₁ (list A) 
                         as Good : rel (list A) A → rel₁ (list A)
      subsumes both the notion of good (finite) sequence for binary relation
                and the notion of Good increasing sequence of finitely 
                    generated ideals of a ring *)  

  Variables (A : Type).

  Implicit Types (P Q : list A → A → Prop).

  Inductive Good P : list A → Prop :=
    | Good_stop a l : P l a    → Good P (a::l)
    | Good_skip a l : Good P l → Good P (a::l).

  Hint Constructors Good : core.

  Fact Good_inv P l :
      Good P l
    → match l with
      | []   => False
      | a::l => P l a ∨ Good P l
      end.
  Proof. destruct 1; eauto. Qed.

  Fact Good_cons_inv P x l : Good P (x::l) ↔ P l x ∨ Good P l.
  Proof.
    split.
    + apply Good_inv.
    + intros []; eauto.
  Qed.

  Fact Good_mono P Q : P ⊆₂ Q → Good P ⊆₁ Good Q.
  Proof. induction 2; eauto. Qed.

  Fact Good_app_left P l r : Good P r → Good P (l++r).
  Proof. intro; induction l; simpl; eauto. Qed.

  Fact Good_app_right P r : 
      (∀ l x, P l x → P (l++r) x)
    → (∀l, Good P l → Good P (l++r)).
  Proof. induction 2; simpl; eauto. Qed.

  Hint Resolve Good_app_left : core.

  (* Another characterization (in FOL) *)
  Lemma Good_split P m : Good P m ↔ ∃ l a r, m = l++a::r ∧ P r a.
  Proof.
    split.
    + induction 1 as [ a m H | a m _ (l & b & r & -> & H) ].
      * now exists [], a, m.
      * now exists (a::l), b, r.
    + intros (? & ? & ? & -> & ?); auto.
  Qed.
  
  Lemma Good_app_inv P l r : Good P (l++r) ↔ (∃ l' a m, l = l'++a::m ∧ P (m++r) a) ∨ Good P r.
  Proof.
    induction l as [ | x l IHl ]; simpl.
    + split; auto; now intros [ ([] & ? & ? & ? & _) | ].
    + rewrite Good_cons_inv, IHl; split.
      * intros [ H1 | [ (l' & y & m & -> & ?) | H1 ] ]; eauto.
        - left; now exists [], x, l.
        - left; now exists (x::l'), y, m.
      * intros [ ([ | z l'] & y & m & [=] & ?) | ]; subst; auto.
        right; left; now exists l', y, m.
  Qed.

  Hint Resolve bar_monotone : core.

  Fact bar_Good_app_left P l m : bar (Good P) m → bar (Good P) (l++m).
  Proof. apply bar_app_left; eauto. Qed.
  
  Section Good_app_middle.

    Variables (P : list A → A → Prop) (m : list A)
              (P_app_middle : ∀ l r a, P (l++r) a → P (l++m++r) a).

    Fact Good_app_middle l r : Good P (l++r) → Good P (l++m++r).
    Proof. induction l; simpl; eauto; intros []%Good_inv; auto. Qed.

    Hint Resolve Good_app_middle bar_app_middle : core.

    Fact bar_Good_app_middle l r : bar (Good P) (l++r) → bar (Good P) (l++m++r).
    Proof. eauto. Qed.

  End Good_app_middle.

End Good_and_bar.

Arguments Good {_}.