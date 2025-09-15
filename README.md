```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# Hilbert Basis Theorem constructivelly in Rocq (artifact)

The repository contains an artifact for the draft paper [_Bar Inductive Predicates for Constructive Algebra in Rocq_](https://members.loria.fr/DLarchey/files/papers/HBT_2025.pdf)
by Dominique Larchey-Wendling (submitted Sept. 2025). It contains the following the main results:

- a characterization of _(Bar) Noetherian rings_ using `bar` inductive predicates;
- constructive proof of Hilbert's Basis Theorem (HBT) partly following the outline given in _Coquand & Persson 98_ (see refs below);
- a proof that (Bar) Noetherian rings are closed under direct products;
- a comparison with alternate constructive characterizations of Noetherianity, in the case of strongly discrete rings.

## Compile and review instructions

This artifact was written for `Rocq-9.0.0`. The main incompatibility with `Coq` relies in the
`From ... Import ...` directives: `From Stdlib Import ...` should be replaced with `From Coq Inport ...`
but doing so, `roqc` would then complain with warnings, so I decided to format the code for `Rocq` only.

Before reviewing the code, you should install `Rocq-9.0.0`. 
We suggest using the opam tool for this task and detail this
procedure below, as a last resort in case you do not have
other means to install Rocq. 

You can visit (https://github.com/rocq-prover/opam) 
for information about `Rocq` & `opam`. We suggest registering
the `released` repo, the recommended default.

The following tested sequence of commands will create a new opam 
switch named `hbt`, then register the `released` repo, and 
then install vanilla `Rocq-9.0.0` with `Stdlib` and `RocqIDE`. 
It is enough for the review, no external libraries are needed:

```console
opam switch create hbt ocaml-base-compiler.4.14.1 --jobs=16
eval $(opam env --switch=hbt)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install rocq-stdlib.9.0.0 rocqide.9.0.0 --jobs=16
```

The first and last command may take some time to complete.

Once `Rocq-9.0.0` is installed, unpack the archive and, in a terminal, 
from the main directory of the archive, compile the whole project with

```console
git clone https://github.com/DmxLarchey/Hilbert-Basis-Theorem.git
cd Hilbert-Basis-Theorem/theories
make all
```

This should run and complete in less than 15 seconds. Some of the main 
results are purposely displayed while they are compiled by Rocq.
After the code is compiled, you can review the individual files 
using your favorite Rocq visual editor, possibly RocqIDE as a
fallback. The following commands invokes RocqIDE:

```console
rocqide hbt.v
```

Some of the `*.v` files below are heavily commented.

## Contents of the individual `*.v` files

```console
_CoqProject:           lists the *.v Rocq source code files          
Makefile:              use _CoqProject to manage the Rocq compilation process
 
utils.v:               utilities and basic notations
measure.v:             tools for induction on a measure
php.v:                 tailored instance of the finite pigeon hole principle

bar.v:                 bar inductive predicates in general

ring.v:                the definition of (non-discrete) rings

ideal.v:               definition and tools for finitely generated ring ideals

monotone_closure.v:    monotone closure of a relation

noetherian_nc.v:       why does the classical characterization of
                       Noetherian rings fail constructively

bezout.v:              Bezout rings, among which Z, the ring of integers
                     
noetherian.v:          definition of (Bar) Noetherian rings and
                       Z is a (Bar) Noetherian ring
                     
product.v:             construction of the direct product of two rings

product_noetherian.v:  the direct product preserves Noetherian rings
                     
poly.v:                construction of the polynomial ring R[X] for a ring R
                     
category.v:            categorical characterizations of product rings,
                       polynomial rings, and multivariate polynomial rings

hbt.v:                 the Hilbert Basis Theorem

noetherian_wf.v:       well-founded induction principles for Noetherian rings

noetherian_alt.v:      comparison with alternate constructive characterizations
                       of RS- and ML-Noetherian rings
   
ramsey.v:              reworked proof that the direct product of two WQOs
                       is a WQO (for the record)
```

# Description of some of the theoritical results 

## Rings and ideals (constructivelly)

We assume some basic knowledge about rings `𝓡`, ring ideals `𝓘` and polynomial rings `𝓡[X]`:
- rings are tuples `(𝓡,+ᵣ,*ᵣ,0ᵣ,1ᵣ)` where addition `+ᵣ` forms a commutative group with `0ᵣ` as a neutral, and multiplication `*ᵣ` forms a commutative monoid with `1ᵣ` as neutral. There is also a distributivity law of `*ᵣ` over `+ᵣ`. Notice that rings need not have commutative multiplication `*ᵣ` (typically, matrices form non-commutative rings), but for our purpose here, we assume commutativity;
- ideals `𝓘` are non-empty additive sub-groups of rings furthermore stable under scalar products, i.e. `∀ x ∈ 𝓡, ∀ y ∈ 𝓘, x*ᵣy ∈ 𝓘`;
- the polynomial ring `𝓡[X]` is usually presented via its canonical representation (see below) but also has a categorical characterization as the initial ring in the category of pointed extensions of `𝓡`, i.e. the ring freely generated by adding an unknown `X` to `𝓡`. 

Notice that polynomials over a ring `𝓡` are a bit tricky to implement if one __does not__ assume that `𝓡` has decidable equality. Indeed, in that case, even the notion of degree of a polynomial cannot be defined (as a total function): what is the degree of `a.X¹` if one cannot discriminate whether `a` is `0ᵣ` or not?

Hence the usual canonical representation of `𝓡[X]` as finite formal sequences `a₀.X⁰+...+aₙ.Xⁿ` (where the head coefficent `aₙ` is not `0ᵣ`) is not workable because one cannot normalise addition (or multiplication for non-integral rings) to ensure that the head coefficient not `0ᵣ`.

Instead we build the theory of polynomial rings using setoids, i.e. equality on `𝓡` is relaxed to be a congruence and the polynomial
`0.X⁰+0.X¹+1.X²` has alternate equivalent representations such as eg `0.X⁰+0.X¹+1.X²+0.X³` that we identify under a well chosen congruence.

Of course, to ensure that we indeed build `𝓡[X]` and not an arbitrary pointed extension of `𝓡`, we show that our construction satisfies the categorical initiality condition.

## Hilbert Basis Theorem in classical settings

Classically, ring ideals can (possibly) be:
- _principal_: i.e. `𝓘 = { x*ᵣg | x ∈ 𝓡 }` is generated by a single generator `g`;
- _finitely generated_: i.e. `𝓘 = { x₁*ᵣg₁+ᵣ...+ᵣxₙ*ᵣgₙ | x₁,...,xₙ ∈ 𝓡 }` is generated by finitely many generators `g₁,...,gₙ`;

and in a _principal ring_, all the ideals are principal. Typically, because of Euclidean division, `𝓕[X]` is principal when `𝓕` is a _field_ (a ring where `*ᵣ` forms a group over non-zero values). However principality is not preserved by the construction of polynomial rings. Typically, neither `Z[X]` nor `(Z/4Z)[X]` are principal rings.

A _Noetherian ring_ is a ring where all ideals are finitely generated. Hence principal rings are Noetherian but, unlike principality, Noetherianess is preserved by the construction of polynomials rings. And as a consequence, for any field `𝓕`, `𝓕[X]` is Noetherian but more 
generally, also `𝓕[X₁,...,Xₙ]` is Noetherian which is _original the statement of the HBT_.

## Hilbert Basis Theorem in constructive settings

The definition of Noetherian ring (or principal ring btw) in anti-classical settings, where the law of excluded middle is refuted,
are mostly useless. Indeed, given a proposition `P : Prop` and any non trivial ring `𝓡` (i.e. where `0ᵣ ≠ 1ᵣ`) which has decidable equivalence (possibly this is equality, e.g. for the ring of integers `Z`), then `𝓘 := { x ∈ 𝓡 | x = 0ᵣ ∨ P }` is an ideal of `𝓡`, and if it is finitely generated (a fortiori principal) then one can prove `P ∨ ¬ P`. This observation is already made in the discussion [2].

As consequence, no non trivial ring with decidable equivalence can be Noetherian unless the law of excluded middle holds, which is by definition refuted in anti-classical settings. So neither `Z` nor `Z/nZ` (`n > 1`) can be Noetherian with that definition of Noetherianess based on the existence of a finite set of generators for all ideals.

There are many possible alternate characterizations of Noetherian rings that better suit constructive or anti-classical settings,
see e.g. [2], or [4] for a more in depth analysis.

The usually favored (constructive) formulation of the HBT is _`𝓡[X]` is Noetherian when the ring `𝓡` is_, i.e. Noetherianess is preserved by the polynomial ring construction. This of course constructivelly implies the initial formulation of the HBT as _`𝓕[X₁,...,Xₙ]` is Noetherian_. However, a good definition of Noetherianess will not constructivelly imply the existence of finite basis for any ideal (because of the argumentation above).

We use the definition proposed in [1], using `bar` inductive predicates, with a revisited terminology. 
For a given ring `𝓡`, let us define `pauses` (denoted `PA`) for a list of values in `𝓡` as 
```coq
Definition PA 𝓡 [x₁;...;xₙ] := ∃i, xᵢ ∈ idl 𝓡 {xᵢ₊₁;...;xₙ}.
```
where `idl 𝓡 P` is the smallest ideal containing a subset `P` of `𝓡`.

Then, following [1], we characterize Noetherianess as 
```coq 
Definition noetherian (𝓡 : ring) := bar (PA 𝓡) [].
```
i.e. the empty list `[] : list 𝓡` unavoidably pauses after finitely many steps, 
however you extend it by adding elements at its head. 
As a consequence there cannot exist a strictly increasing infinite sequence of 
finitely generated ideals. But constructivelly, this does not imply that 
ideals always have finite sets of generators.

We establish the two following results:
```coq
Theorem HBT : noetherian 𝓡 → noetherian (poly_ring 𝓡).
Theorem Hilbert_Basis_Theorem n : noetherian R → noetherian (multivariate_ring 𝓡 n).
```

where `poly_ring 𝓡` is (isomorphic to) `𝓡[X]` and `multivariate_ring 𝓡 n` is (isomorphic to) `𝓡[X₁,...,Xₙ]`.

## Examples of Noetherian rings

As explained in the previous paragraph, the classical definition of _principal ring_ (as having only mono-generated/principal ideals) is not suited in anti-classical settins
because again, the ring of integers `Z` would not be principal. Instead we define Bezout rings as:
```coq
Definition bezout_ring (𝓡 : ring) := ∃g, idl 𝓡 ⌞l⌟ = { x*ᵣg | x ∈ 𝓡 }.
```
i.e. every finitely generated ideal is a principal ideal. Notice that this definition of Bezout ring 
__does not__ implies Noetherianess but however the two properties are linked in some way, e.g. we show:
```coq
Theorem wf_sdiv_bezout_noetherian (𝓡 : ring) :
    bezout_ring 𝓡
  → (∀ x y : 𝓡, x |ᵣ y ∨ ¬ x |ᵣ y)
  → well_founded (λ x y : 𝓡, x |ᵣ y ∧ ¬ y |ᵣ x)
  → noetherian 𝓡.
```
meaning that any Bezout ring with (logically) decidable divisibility, and well-founded strict divisibility is Noetherian.

In addition to the HBT above, with these definitions, we can show that:
- (discrete) fields are Bezout and Noetherian rings;
- the ring of integers `Z` is a Bezout ring and Noetherian ring (via `wf_sdiv_bezout_noetherian` above);
- finite rings are Noetherian (e.g `Z/nZ` for `n > 0`);
- the quotient of a Bezout (resp. Noetherian) ring is Bezout (resp. Noetherian).

## The direct product is Noetherian

Additionally, we remarked classical proofs of the Noetherianess of the direct product of two rings was using Ramsey like arguments.
Hence, we wondered whether a constructive form of Ramsey's theorem, based on `bar` inductive predicates, could be adapted to 
derive the closure of Noetherianess under direct products, w/o assuming further properties on rings (such as e.g. strong discreteness).

And indeed, it turns out that D. Fridlender's proof of Ramsey's theorem [5], simplified and reworked in Rocq, 
was a good starting point to derive the Noetherianess of the direct products:
```coq
Theorem product_noetherian 𝓡 𝓣 : noetherian 𝓡 → noetherian 𝓣 → noetherian (product_ring 𝓡 𝓣).
```

Further comments on that **new proof** will come later on.

## Induction principles derived from Noetherianess

We show that several instances of _witnessed strict reverse inclusion_ are 
(constructivelly) well-founded for Noetherian ring:
```coq
Notation "P ⊃ Q" := Q ⊆ P ∧ ∃x, x ∈ P ∧ x ∉ Q.
```
Given a Noetherian ring `𝓡`:
- the relation `⊃` is well-founded when restricted to the ideals of `𝓡`;
- the relation `λ P Q, idl 𝓡 P ⊃ idl 𝓡 Q` is well-founded on `𝓡 → Prop`;
- the relation `λ l m, idl 𝓡 ⌞l⌟ ⊃ idl 𝓡 ⌞m⌟)` is well-founded on `list 𝓡`

where `⌞[x₁;...;xₙ]⌟ := {x₁,...,xₙ}` (mapping a list to a subset of `𝓡`) and `idl 𝓡 P` is smallest ideal containing the subset `P` of `𝓡`.

## Obtaining finite bases

Using one of the previous induction principles, it is possible to show
the existence of a basis for an ideal, under certain conditions. 
We finish with the construction of a finite basis for ideals satisfying the condition that 
they can be compared for inclusion with any finitely generated ideal:
```coq
Theorem find_basis (𝓡 : ring) (𝓘 : 𝓡 → Prop) :
    noetherian 𝓡
  → ideal 𝓡 𝓘
  → (∀ l : list 𝓡, (∃x, x ∈ 𝓘 ∧ ¬ idl 𝓡 ⌞l⌟ x) ∨ 𝓘 ⊆ idl 𝓡 ⌞l⌟)
  → ∃b, 𝓘 = idl 𝓡 ⌞b⌟.
```
The property `∀l, (∃x, x ∈ 𝓘 ∧ ¬ idl 𝓡 ⌞l⌟ x) ∨ 𝓘 ⊆ idl 𝓡 ⌞l⌟` states that for any list `l` (of generators), either `𝓘` contains a element outside of the ideal generated by `l`, or is included into it. It is of course is a trivial consequence of the law of excluded middle, but we do not assume excluded middle in here.

## Remarks on the proof

- the largest part of the proof, though not the most difficult, is the construction of the polynomial ring `𝓡[X]`, based on the `Setoid` rewriting and `Ring` frameworks of Coq which allows us to micro-manage ring computations, see [`poly.v`](theories/poly.v); Without those two frameworks, that construction could become quite tricky and unsurprisingly, this part was avoided in the implementation proposed in [1].
- the _open induction principle_ of [1] is reinterpreted as a well-founded induction over the projection of a lexicographic product.
- The proof of the `HBT` stated above is quite small (20-25 loc) in [`hbt.v`](theories/hbt.v) but relies on the theorem `update_lead_coef` from [`poly.v`](theories/poly.v) which states that if `x` is the head coefficent of `p` and is a linear combination of the head coefficents of `v`, a list of polynomials of length less than `p`, then `p::v` can be updated into `q::v` where `q := p+lc` is of length strictly less than `p` and `lc` is a linear combination of the values in `v`.
- Updating preserves `PA` (pauses) and thus also `bar PA`.

## References

- [1]. [Gröbner Bases in Type Theory](https://link.springer.com/chapter/10.1007/3-540-48167-2_3) by _Coquand & Persson_ 1998.
- [2]. The following discussion is interesting (https://mathoverflow.net/questions/222923/alternate-proofs-of-hilberts-basis-theorem).
- [3]. [Strongly Noetherian rings and constructive ideal theory](https://doi.org/10.1016/j.jsc.2003.02.001) by _Hervé Perdry_ 2004.
- [4]. See also the [Buchberger](https://github.com/rocq-community/buchberger) repository.
- [5]. [Higman's lemma in type theory](https://doi.org/10.1007/BFb0097789) by _Fridlender_ 1996.
