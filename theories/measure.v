(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Wellfounded Utf8.

(** Extraction friendly induction on 1, 2 or 3 values 
    combined as a documented tactic notation *)

(* Induction on a wf relation *)
Tactic Notation "induction"
                "on" hyp(x)
                "as" ident(loop) 
                "wf" "by" constr(wf) :=
  let d := fresh in
  (* Induction is grounded on relation ≺
     which is well-founded by wf *)
  pattern x; generalize (wf x); revert x;
  (* Implemented using a structural Fixpoint
     on d : Acc ≺ x *)
  fix loop 2; intros x d;
  (* Then specialized on input x'
     such that x' ≺ x *)
  specialize (λ x' d', loop x' (Acc_inv d d'));
  (* d : Acc ≺ x is of no use anymore *)
  clear d.

(* Induction on a wf relation on pairs *)
Tactic Notation "induction" 
                "on" hyp(x) hyp(y)
                "as" ident(loop) 
                "wf" "by" constr(wf) :=
  let d := fresh in
  (* Induction is grounded on relation ≺
     which is well-founded by wf *)
  pattern x, y; generalize (wf (x,y)); revert x y;
  (* Implemented using a structural Fixpoint
     on d : Acc ≺ (x,y) *)
  fix loop 3; intros x y d;
  (* Then specialized on inputs x' y'
     such that (x',y') ≺ (x,y) *)
  specialize (λ x' y' d', loop x' y' (Acc_inv d d'));
  (* d : Acc ≺ (x,y) is of no use anymore *)
  clear d.

(* Induction on a wf relation on triples *)
Tactic Notation "induction" 
                "on" hyp(x) hyp(y) hyp(z)
                "as" ident(loop) 
                "wf" "by" constr(wf) :=
  let d := fresh in
  (* Induction is grounded on relation ≺
     which is well-founded by wf *)
  pattern x, y, z; generalize (wf (x,y,z)); revert x y z;
  (* Implemented using a structural Fixpoint
     on d : Acc ≺ (x,y,z) *)
  fix loop 4; intros x y z d;
  (* Then specialized on inputs x' y' z'
     such that (x',y',z') ≺ (x,y,z) *)
  specialize (λ x' y' z' d', loop x' y' z' (Acc_inv d d'));
  (* d : Acc ≺ (x,y,z) is of no use anymore *)
  clear d.

#[local] Definition uncurry₂ {X Y Z} (m : X → Y → Z) '(x,y) := m x y.
#[local] Definition uncurry₃ {X Y Z K} (m : X → Y → Z → K) '(x,y,z) := m x y z.

#[local] Fact wf_measure₁ {X} (m : X → nat) : well_founded (λ p q, m p < m q).
Proof. apply wf_inverse_image, lt_wf. Qed.

#[local] Fact wf_measure₂ {X Y} (m : X → Y → nat) : well_founded (λ p q, uncurry₂ m p < uncurry₂ m q).
Proof. apply wf_inverse_image, lt_wf. Qed.

#[local] Fact wf_measure₃ {X Y Z} (m : X → Y → Z → nat) : well_founded (λ p q, uncurry₃ m p < uncurry₃ m q).
Proof. apply wf_inverse_image, lt_wf. Qed.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  induction on x as IH wf by (wf_measure₁ (λ x, f)).

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  induction on x y as IH wf by (wf_measure₂ (λ x y, f)); unfold uncurry₂ in IH.

Tactic Notation "induction" "on" hyp(x) hyp(y) hyp(z) "as" ident(IH) "with" "measure" uconstr(f) :=
  induction on x y z as IH wf by (wf_measure₃ (λ x y z, f)); unfold uncurry₃ in IH.
