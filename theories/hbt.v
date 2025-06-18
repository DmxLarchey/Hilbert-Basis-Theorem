(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Arith Lia Wellfounded Relations Setoid Utf8.
From Coq Require Fin.

Import ListNotations.

Require Import utils bar php ring ideal poly noetherian.

(** Ref:  https://link.springer.com/chapter/10.1007/3-540-48167-2_3 by Coquand & Perrson *)

Section lex.

  Variables (X : Type) (R : X → X → Prop).

  (* This order is stronger that shortlex, ie either shorter
     or of equal length and lexicographically smaller *)
  Inductive lex : list X → list X → Prop :=
    | lex_stop p q m : R p q   → lex (p::m) (q::m)
    | lex_next x l m : lex l m → lex l (x::m).

  Hint Constructors lex : core.

  Fact lex_inv l m :
      lex l m
    → match m with
      | []   => False
      | y::m => (∃x, R x y ∧ l = x::m) ∨ lex l m
      end.
  Proof. destruct 1; eauto. Qed.

  Fact lex_app l m k : lex l m → lex l (k++m).
  Proof. intro; induction k; simpl; auto. Qed.

  Hypothesis R_wf : well_founded R.

  Theorem lex_wf : well_founded lex.
  Proof.
    intros l.
    induction l as [ | q l IH ].
    + constructor.
      now intros ? ?%lex_inv.
    + induction q using (well_founded_induction R_wf) in l, IH |- *.
      constructor.
      intros ? [ (p & Hpq & ->) | ]%lex_inv; eauto.
      now apply Acc_inv with (1 := IH).
  Qed.

  (** It gives rises to a tailored induction principle used below
      called "open induction" in Coquand & Perrson but we view it
      as a specialized case of a well-founded lexicographic product 
      on lists here *)

  Section lex_special_wf.

    (** Given "fixed" m and P, to show ∀x, P (x::m) it is enough to show:
        - the base case: P l holds for any l <lex m
        - the recursive case: P (x:m) holds further assuming P l for any l <lex x::m *)

    Variables (m : list X)
              (P : list X → Prop)
              (HP0 : ∀l, lex l m → P l)                        (* The base case *)
              (HP1 : ∀x, (∀l, lex l (x::m) → P l) → P (x::m))  (* The recursive case *)
              .

    Notation T := (λ x y, lex (x::m) (y::m)).

    Local Fact lex_special_T_wf : well_founded T.
    Proof. apply wf_inverse_image, lex_wf. Qed.

    Theorem lex_special_wf x : P (x::m).
    Proof.
      induction x using (well_founded_induction lex_special_T_wf).
      apply HP1; intros ? [(? & ? & ->)|]%lex_inv; eauto.
    Qed.

  End lex_special_wf.

End lex.

Arguments lex {_}.

#[local] Notation LD := linearly_dependent.

Section linearly_dependent.

  Variables (R : ring).

  Add Ring ring_is_ring : (is_ring R).

  Implicit Type (l m : list R).

  Local Remark LD_split m : LD m ↔ ∃ l x r, m = l ++ x :: r ∧ Idl ⌞r⌟ x.
  Proof. apply Good_split. Qed.

  (** We show, in sequence, that:
        - Idl _ x is update-closed
        - LD _ is update-closed
        - bar LD _ is update-closed *)

  (* linear dependency is invariant uner update *)
  Local Lemma LD_update_closed l m : update l m → LD l → LD m.
  Proof.
    unfold LD.
    induction 1 as [ x l r y H%Idl_iff_lc__list G | x l m H IH ]; intros [ H1 | H1 ]%Good_inv.
    + constructor 1; rewrite <- G; now apply Idl_op_a.
    + now constructor 2.
    + constructor 1.
      revert H1; now apply Idl_update_closed.
    + constructor 2; auto.
  Qed.

  Hint Resolve LD_update_closed : core.
  Hint Constructors bar update : core.

  (* bar LD is invariant under update *)
  Local Theorem bar_LD_update_closed l m : update l m → bar LD l → bar LD m.
  Proof. intros H1 H2; revert H2 m H1; induction 1; eauto. Qed.

  (* bar LD is invariant under adding elements anywhere *)
  Local Fact bar_LD_app_middle l m r :  bar LD (l++r) → bar LD (l++m++r).
  Proof.
    apply bar_Good_app_middle.
    intros ? ? ?; apply Idl_mono.
    intros ?; rewrite !in_app_iff; tauto.
  Qed.

  Local Fact bar_LD_app_left l r : bar LD r → bar LD (l++r).
  Proof. apply bar_LD_app_middle with (l := []). Qed.

  Local Fact bar_LD_cons_middle l x r : bar LD (l++r) → bar LD (l++x::r).
  Proof. apply bar_LD_app_middle with (m := [_]). Qed.

End linearly_dependent.

Section HTB.

  (** Beware that LD is used for two rings below, both R and R[X] !! *)

  Variable (R : ring).

  Implicit Type (h : list R)
                (p q : poly_ring R) 
                (l k : list (poly_ring R)).

  Hint Constructors lex bar : core.

  (** A well-founded order on polynomials, being of smaller length *)
  Let T p q := ⌊p⌋ < ⌊q⌋.

  Local Fact T_wf : well_founded T.
  Proof. unfold T; apply wf_inverse_image, lt_wf. Qed.

  (** Hence lex T is well-founded as well and we can use the
      special instance of lex induction implemented above *)

  Local Fact T_le p q x : ⌊p⌋ ≤ ⌊q⌋ → T p (q++[x]).
  Proof. intro; red; rewrite length_app; simpl; lia. Qed.
  
  Local Fact T_lt p q x : 1+⌊p⌋ < ⌊q⌋ → T (p++[x]) q.
  Proof. intro; red; rewrite length_app; simpl; lia. Qed.
  
  Hint Resolve T_le T_lt lex_app : core.

  Local Lemma HBT_main h : bar LD h → ∀k, Forall2 is_last h k → (∀m, lex T m k → bar LD m) → bar LD k.
  Proof.
    induction 1 as [ h Hh | h _ IHh ].
    + (* The list of head coefficients is linearly dependent in R 
         hence h = u++[x]++v where x is a linear combination of v
 
         From Forall2 is_last (u++[x]++v) k, we split k accordingly into 
         k = l++[p++[x]]++r where Forall2 is_last u l and Forall2 is_last v r *)
      apply LD_split in Hh as (u & x & v & -> & Hx%Idl_iff_lc__list).
      intros ? (l & y & r & _ & [p] & Hr & ->)%Forall2_middle_inv_l IH.
      (* because LD is monotone, it is enough to should bar LD ((p++[x])::r) *)
      apply bar_LD_app_left.
      (* either all polynomials in r have degree less than 1+⌊p⌋
         or one of them, say q, has degree strictly greeter than 1+⌊p⌋ *)
      destruct list_choice 
        with (P := λ q : list R, ⌊q⌋ <= 1+⌊p⌋) 
             (Q := λ q : list R, 1+⌊p⌋ < ⌊q⌋)
             (l := r)
        as [ Hr' | (q & H3 & H4) ].
      * intros; lia.
      * (** all polynomial in r have a degree lesser than that of p++[x]. 
            By update, we change p++[x] into a polynomial of strictly lesser 
            length using linear combinations of r. *)
        rewrite <- Forall_forall in Hr'.
        destruct update_lead_coef
          with (R := R) (1 := Hx) (2 := Hr) (3 := Hr')
          as (q & H3 & H4).
        apply bar_LD_update_closed with (1 := H4); auto.
      * (** some polynomial in r, say q has a degree strictly greater than 
            that of p++[x]. Then r = r1++[q]++r2 with
            1+⌊p⌋ < ⌊q⌋. By IH we get bar LD ([p++[x]]++r2) and conclude  *)
        apply in_split in H3 as (r1 & r2 & ->).
        apply (bar_LD_app_middle (poly_ring _)) with (l := [_]).
        apply (bar_LD_cons_middle (poly_ring _)) with (l := [_]).
        apply IH, lex_app; simpl; eauto.
    + intros k Hhk IH.
      (* it is sufficient to show bar LD (p::k) for any p *)
      constructor 2.
      (* we use the special lexicographic induction on lex (p::k) 
         and can thus further assume bar LD l for any l <lex p::k *)
      apply lex_special_wf with (1 := T_wf); trivial.
      (* either p is [] or of shape q++[x] *)
      intros p; destruct p as [ | x q _ ] using rev_ind.
      * (* p is [] (the zero polynomial) and thus []::_ is LD *)
        constructor 1; constructor; constructor 3.
      * (* Forall2 is_last (x::h) ((q++[x])::k holds
           hence we get bar LD ((q++[x])::k) using IHh *)
        apply (IHh x); auto.
  Qed.

  Theorem HBT : noetherian R → noetherian (poly_ring R).
  Proof.
    intros H; apply HBT_main with (h := []); auto.
    now intros ? ?%lex_inv.
  Qed.

End HTB.

Section Hilbert_Basis_Theorem.

  Notation idx := Fin.t.

  (* Recall that idx n = {1,...,n} and here
     we show that R[X₁,...,Xₙ] is Noetherian.

     Formally this is the multivariate ring generated
     by (idx n) over R *)

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

  Variable (R : ring).

  (** By induction on n, there exists a multivariate ring
      (Rₙ,φₙ,𝓧ₙ) with  
         - Rₙ : ring
         - φₙ : R → Rₙ (ring embedding)
         - 𝓧ₙ : {1,...,n} → Rₙ (unknowns)
      such that Rₙ is Noetherian with R is *)
  Local Lemma HTB_rec n :
    { Rₙ : ring & 
    { φₙ : R → Rₙ & 
    { 𝓧ₙ : idx n → Rₙ |
         @is_multivariate_ring (idx n) R Rₙ φₙ 𝓧ₙ 
       ∧ (noetherian R → noetherian Rₙ) } } }.
  Proof.
    induction n as [ | n (Rn & phi & h & H1 & H0) ].
    + exists R, (λ x, x), (idx0_rect _); split; auto; split; auto.
      intros T ga h Hga; split.
      * exists ga; split right; auto.
        apply idx0_rect.
      * intros al be H1 H2 H3 H4 H5 H6 r.
        now rewrite H6.
    + generalize (poly_ring_correct Rn); intros H2.
      generalize (HBT Rn); intros G.
      apply poly_ring__multivariate_ring in H2.
      generalize (multivariate_ring_compose H1 H2); intros H3.
      apply multivariate_ring_bijection with (1 := idx2sum_bij n) in H3.
      exists (poly_ring Rn), (λ x, poly_embed (phi x)); eauto.
  Qed.

  Definition multivariate_ring n := projT1 (HTB_rec n).
  Definition multivariate_embed n : R → multivariate_ring n := projT1 (projT2 (HTB_rec n)).
  Definition multivariate_unknowns n : idx n → multivariate_ring n := proj1_sig (projT2 (projT2 (HTB_rec n))).

  Theorem multivariate_ring_correct n :
     @is_multivariate_ring (idx n) R (multivariate_ring n) (multivariate_embed n) (multivariate_unknowns n).
  Proof. apply (proj2_sig (projT2 (projT2 (HTB_rec n)))). Qed.

  Theorem Hilbert_Basis_Theorem n : noetherian R → noetherian (multivariate_ring n).
  Proof. apply (proj2_sig (projT2 (projT2 (HTB_rec n)))). Qed.

End Hilbert_Basis_Theorem.

Check multivariate_embed.
Check multivariate_unknowns.
Print is_multivariate_ring.
Check multivariate_ring_correct.
Check Hilbert_Basis_Theorem.
