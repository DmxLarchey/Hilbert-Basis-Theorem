(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Wellfounded Relations Setoid Utf8.

From Stdlib Require Fin.

Import ListNotations.

Require Import utils bar ring ideal poly category noetherian.

(** Ref:  https://link.springer.com/chapter/10.1007/3-540-48167-2_3 by Coquand & Persson *)

Section lex.

  Variables (A : Type) (T : A → A → Prop).

  (** This order is stronger that shortlex, ie either shorter
      or of equal length and lexicographically smaller *)
  Inductive lex : list A → list A → Prop :=
    | lex_stop a b m : T a b   → lex (a::m) (b::m)
    | lex_next b l m : lex l m → lex l (b::m).

  Hint Constructors lex : core.

  Fact lex_inv l m :
      lex l m
    → match m with
      | []   => False
      | b::m => (∃a, T a b ∧ l = a::m) ∨ lex l m
      end.
  Proof. destruct 1; eauto. Qed.

  Fact lex_app l m k : lex l m → lex l (k++m).
  Proof. intro; induction k; simpl; auto. Qed.

  Hypothesis T_wf : well_founded T.

  (** Wellfoundness of lexicographic orders is usually proved 
      by nested induction *)
  Remark lex_wf : well_founded lex.
  Proof.
    intros l.
    (* first induction, structural on l *)
    induction l as [ | b l IH ].
    + (* when l = [], it has no predecessors *)
      constructor; now intros ? ?%lex_inv.
    + (* second induction on the head of q::l, using T_wf as an induction principle *)
      induction b using (well_founded_induction T_wf) in l, IH |- *.
      constructor.
      intros ? [ (? & ? & ->) | ]%lex_inv; eauto.
      now apply Acc_inv with (1 := IH).
  Qed.

  (** We just need a tailored induction principle described below
      replacing "open induction" in Coquand & Perrson *)

  Section lex_special_wf.

    (** Given "fixed" k and P, to show P (a::k) it is enough to show:
        - the base case: P l holds for any l <lex k
        - the recursive case: P (a:k) holds further assuming P l for any l <lex a::k *)

    Variables (k : list A)
              (P : list A → Prop)
              (HP0 : ∀l, lex l k → P l)                        (* The base case *)
              (HP1 : ∀a, (∀l, lex l (a::k) → P l) → P (a::k))  (* The recursive case *)
              .

    Theorem lex_special_wf a : P (a::k).
    Proof.
      induction a using (well_founded_induction T_wf).
      apply HP1; intros ? [(? & ? & ->)|]%lex_inv; eauto.
    Qed.

  End lex_special_wf.

End lex.

Arguments lex {_}.

#[local] Notation PA := pauses.

Section HTB.

  (** Beware that PA is used for two rings below, both 𝓡 and 𝓡[X] !! *)

  Variable (𝓡 : ring).

  Implicit Type (h : list 𝓡)
                (p q : poly_ring 𝓡) 
                (l k : list (poly_ring 𝓡)).

  Hint Constructors lex bar : core.

  (** A well-founded order on representations of polynomials, being of smaller length *)
  Let T p q := ⌊p⌋ < ⌊q⌋.

  Local Fact T_wf : well_founded T.
  Proof. unfold T; apply wf_inverse_image, lt_wf. Qed.

  (** Hence lex T is well-founded as well and we can use the
      special instance of lex induction implemented above *)
(*
  Local Fact T_le p q x : ⌊p⌋ ≤ ⌊q⌋ → T p (q++[x]).
  Proof. intro; red; rewrite length_app; simpl; lia. Qed.

  Local Fact T_lt p q x : 1+⌊p⌋ < ⌊q⌋ → T (p++[x]) q.
  Proof. intro; red; rewrite length_app; simpl; lia. Qed.
*)

  Hint Resolve (*T_le T_lt*) lex_app : core.
  Hint Constructors is_last update : core.

  (* Remark: we use the term degree abusively in the comments below 
     because this notion applies to polynomials and they may not have
     one (when the ring is not discrete). We use "degree" for the length 
     of a representation of a polynomial, which exists, but is dependent
     on the represention, hence is not a notion attached to a polynomial. *)

  Local Lemma HBT_main h : bar PA h → ∀k, Forall2 is_last h k → (∀m, lex T m k → bar PA m) → bar PA k.
  Proof.
    (* induction on bar PA h *)
    induction 1 as [ h Hh | h _ IHh ].
    + (* The list of head coefficients pauses in 𝓡
         hence h = u++[x]++v where x is a linear combination of v. *)
      apply PA_split in Hh as (u & x & v & -> & Hx%idl_iff_lc__list).
      (* From Forall2 is_last (u++[x]++v) k, we split k accordingly into 
         k = l++[p]++m where is_last p x and Forall2 is_last v m *)
      intros ? (l & p & m & _ & Hp & Hm & ->)%Forall2_middle_inv_l IH.
      (* because PA is monotone, it is enough to show bar PA (p::m) *)
      apply bar_PA_app_left.
      (* either all polynomials in m have degree less than ⌊p⌋
         or one of them, say q, has degree strictly greater than ⌊p⌋ *)
      destruct list_choice 
        with (P := λ q : list 𝓡, ⌊q⌋ ≤ ⌊p⌋) 
             (Q := λ q : list 𝓡, ⌊p⌋ < ⌊q⌋)
             (l := m)
        as [ (q & H3 & H4) | Hm' ].
      * intros; lia.
      * (* Some polynomial in m, say q has a "degree" strictly greater than 
           that of p. Then m = m'++[q]++r with ⌊p⌋ < ⌊q⌋.
           By IH we get bar PA ([p]++r) and conclude *)
        apply in_split in H3 as (m' & r & ->).
        (* it is enough to show bar PA ([p]++r), 
           ie we can discard m++[q] in the middle *)
        replace (p::m'++q::r) with ([p]++(m'++[q])++r) by now rewrite <- app_assoc.
        apply (bar_PA_app_middle (poly_ring _)).
        (* bar PA ([p]++r) holds by IH *)
        apply IH, lex_app; simpl; eauto.
      * (* All polynomial in m have a "degree" lesser than that of p.
           We build a new polynomial q of "degree" strictly less than p
           such that p-q is a linear combination of m *)
        rewrite <- Forall_forall in Hm'.
        destruct update_lead_coef
          with (𝓡 := 𝓡) (1 := Hm') (p := p) (m := m)
          as (q & []); eauto.
        (* We update p by q, and conclude using IH *)
        apply bar_PA_update_closed with (q::m); auto.
    + (* h are the heads of k *)
      intros k Hhk IH.
      (* it is sufficient to show ∀p, bar PA (p::k) *)
      constructor 2.
      (* we use the special lexicographic induction on lex (p::k) 
         and can thus further assume bar PA l for any l <lex p::k *)
      apply lex_special_wf with (1 := T_wf); trivial.
      (* either p is [] or of shape q++[x] *)
      intros a; destruct a as [ | x q _ ] using rev_ind.
      * (* p is [] (the zero polynomial) and thus []::_ is PA *)
        constructor 1; constructor; constructor 3.
      * (* x::h are the heads of (q++[x])::k 
           hence we get bar PA ((q++[x])::k) using IHh *)
        apply (IHh x); auto.
  Qed.

  Theorem HBT : noetherian 𝓡 → noetherian (poly_ring 𝓡).
  Proof.
    intros H; apply HBT_main with (h := []); auto.
    now intros ? ?%lex_inv.
  Qed.

End HTB.

Check is_poly_ring.
Check poly_ring_correct.
Print is_poly_ring.
Check HBT.

Section Hilbert_Basis_Theorem.

  Notation idx := Fin.t.

  (** Recall that idx n = {1,...,n} and here
      we show that 𝓡[X₁,...,Xₙ] is Noetherian.

      Formally this is the multivariate ring generated
      by (idx n) over 𝓡 *)

  (* idx 0 is an empty type *)
  Local Fact idx0_rect : ∀ (P : idx 0 → Type) (p : idx 0), P p.
  Proof. exact Fin.case0. Qed.

  (* idx n + {*} and idx (S n) are equipotent (in bijection) *)
  Let idx2sum {n} (i : idx (S n)) : idx n + unit :=
    Fin.caseS' i _ (inr tt) (λ p : idx n, inl p).

  Let sum2idx {n} (c : idx n + unit) : idx (S n) :=
    match c with
    | inl i => Fin.FS i
    | inr _ => Fin.F1
    end.

  Local Fact idx2sum_bij n : bijection sum2idx (@idx2sum n).
  Proof.
    split.
    + revert n; apply Fin.rectS; simpl; auto.
    + intros [ | []]; simpl; trivial.
  Qed.

  Hint Resolve ring_homo_id ring_homo_compose : core.

  Variable (𝓡 : ring).

  (** By induction on n, one can compute a multi-extension 
      over unknowns in {1,...,n} of a ring 𝓡, ie a tupple
      (𝓡ₙ,φₙ,Xₙ) with  
         - 𝓡ₙ : ring
         - φₙ : 𝓡 → 𝓡ₙ (ring embedding)
         - Xₙ : {1,...,n} → 𝓡ₙ (unknowns)
      such that 𝓡ₙ is Noetherian when 𝓡 is 

      Notice that multi-ring extensions are
      unique up to isomorphism *)

  Local Lemma HTB_rec n :
    { 𝓡ₙ | is_multi_ring (idx n) 𝓡 𝓡ₙ ∧ (noetherian 𝓡 → noetherian 𝓡ₙ) }.
  Proof.
    induction n as [ | n (Rn & Hn1 & Hn2) ].
    + exists {| me_ring := 𝓡;
                me_embed := λ x, x;
                me_embed_homo := ring_homo_id 𝓡;
                me_points := idx0_rect _ |}; simpl; split; auto.
      intros [ T f Hf h ]; simpl; split.
      * exists f; split right; simpl; auto.
        apply idx0_rect.
      * intros ? ? (_ & _ & ?) (_ & _ & G) ?; simpl in *; now rewrite G.
    + generalize (poly_ring_correct Rn); intros H2.
      apply poly_ring__multi_ring in H2; simpl in H2.
      generalize (HBT Rn); intros G.
      generalize (multi_ring_compose Hn1 H2); intros H3.
      apply multi_ring_bijection with (1 := idx2sum_bij n) in H3.
      simpl in *; eauto.
  Qed.

  Definition multi_ring n := proj1_sig (HTB_rec n).

  Theorem multi_ring_correct n : is_multi_ring _ _ (multi_ring n).
  Proof. apply (proj2_sig (HTB_rec n)). Qed.

  Theorem Hilbert_Basis_Theorem n : noetherian 𝓡 → noetherian (multi_ring n).
  Proof. apply (proj2_sig (HTB_rec n)). Qed.

End Hilbert_Basis_Theorem.

Check multi_ring.
Check multi_ring_correct.
Print is_multi_ring.
Check Hilbert_Basis_Theorem.
