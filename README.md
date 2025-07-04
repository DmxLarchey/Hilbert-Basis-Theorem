# Hilbert Basis Theorem constructivelly in Coq/Rocq

The repository contains a constructive proof of Hilbert's Basis Theorem (a.k.a. HBT below) partly following the outline given in _Coquand & Persson 98_ (see refs below).

## Rings and ideals (constructivelly)

We assume some basic knowledge about rings `R`, ring ideals `I` and polynomial rings `R[X]`:
- rings are tuples `(R,+ᵣ,*ᵣ,0ᵣ,1ᵣ)` where addition `+ᵣ` forms a commutative group with `0ᵣ` as a neutral, and multiplication `*ᵣ` forms a commutative monoid with `1ᵣ` as neutral. There is also a distributivity law of `*ᵣ` over `+ᵣ`. Notice that rings need not have commutative multiplication `*ᵣ` (typically, matrices form non-commutative rings), but for our purpose here, we assume commutativity;
- ideals `I` are non-empty additive sub-groups of rings furthermore stable under scalar products, i.e. `∀ x ∈ R, ∀ y ∈ I, x*ᵣy ∈ I`;
- the polynomial ring `R[X]` is usually presented via its canonical representation (see below) but also has a categorical characterization as the initial ring in the category of pointed extensions of `R`, i.e. the ring freely generated by adding an unknown `X` to `R`. 

Notice that polynomials over a ring `R` are a bit tricky to implement if one __does not__ assume that `R` has decidable equality. Indeed, in that case, even the notion of degree of a polynomial cannot be defined (as a total function): what is the degree of `a.X¹` if one cannot discriminate whether `a` is `0ᵣ` or not?

Hence the usual canonical representation of `R[X]` as finite formal sequences `a₀.X⁰+...+aₙ.Xⁿ` (where the head coefficent `aₙ` is not `0ᵣ`) is not workable because one cannot normalise addition (or multiplication for non-integral rings) to ensure that the head coefficient not `0ᵣ`.

Instead we build the theory of polynomial rings using setoids, i.e. equality on `R` is relaxed to be a congruence and the polynomial
`0.X⁰+0.X¹+1.X²` has alternate equivalent representations such as eg `0.X⁰+0.X¹+1.X²+0.X³` that we identify under a well chosen congruence.

Of course, to ensure that we indeed build `R[X]` and not an arbitrary extension of `R`, we show that our construction satisfies the categorical initiality condition.

## Hilbert Basis Theorem in classical settings

Classically, ring ideals can (possibly) be:
- _principal_: i.e. `I = { x*ᵣg | x ∈ R }` is generated by a single generator `g`;
- _finitely generated_: i.e. `I = { x₁*ᵣg₁+ᵣ...+ᵣxₙ*ᵣgₙ | x₁,...,xₙ ∈ R }` is generated by finitely many generators `g₁,...,gₙ`;

and in a _principal ring_, all the ideals are principal. Typically, because of Euclidean division, `F[X]` is principal when `F` is a _field_ (a ring where `*ᵣ` forms a group over non-zero values). However principality is not preserved by the construction of polynomial rings. Typically, neither `Z[X]` nor `(Z/4Z)[X]` are principal rings.

A _Noetherian ring_ is a ring where all ideals are finitely generated. Hence principal rings are Noetherian but, unlike principality, Noetherianess is preserved by the construction of polynomials rings. And as a consequence, for any field `F`, `F[X]` is Noetherian but more 
generally, also `F[X₁,...,Xₙ]` is Noetherian which is _original the statement of the HBT_.

## Hilbert Basis Theorem in constructive settings

The definition of Noetherian ring (or principal ring btw) in anti-classical settings, where the law of excluded middle is refuted,
are mostly useless. Indeed, given a proposition `A : Prop` and any non trivial ring `R` (i.e. where `0ᵣ ≠ 1ᵣ`) which has decidable equivalence (possibly this is equality, e.g. for the ring of integers `Z`), then `I := { x ∈ R | x = 0ᵣ ∨ A }` is an ideal of `R`, and if it is finitely generated (a fortiori principal) then one can prove `A ∨ ¬ A`. This observation is already made in the discussion [2].

As consequence, no non trivial ring with decidable equivalence can be Noetherian unless the law of excluded middle holds, which is by definition refuted in anti-classical settings. So neither `Z` nor `Z/nZ` (`n > 1`) can be Noetherian with that definition of Noetherianess based on the existence of a finite set of generators for all ideals.

There are many possible alternate characterizations of Noetherian rings that better suit constructive or anti-classical settings,
see e.g. [2], or [4] for a more in depth analysis.

The usually favored (constructive) formulation of the HBT is _`R[X]` is Noetherian when the ring `R` is_, i.e. Noetherianess is preserved by the polynomial ring construction. This of course constructivelly implies the initial formulation of the HBT as _`F[X₁,...,Xₙ]` is Noetherian_. However, a good definition of Noetherianess will not constructivelly imply the existence of finite basis for any ideal (because of the argumentation above).

We use the definition proposed in [1], using `bar` inductive predicates, with a revisited terminology. 
For a given ring `R`, let us define L(inearly) D(ependent) for a list of values in `R` as 
```coq
Definition LD R [x₁;...;xₙ] := ∃i, xᵢ ∈ Idl R {xᵢ₊₁;...;xₙ}.
```
where `Idl R P` is the smallest ideal containing a subset `P` of `R`. Notice that when `R` is a field, this amounts to saying that the list of values `[x₁;...;xₙ]` are linearly dependent.

Then, following [1], we characterize Noetherianess as 
```coq 
Definition noetherian (R : ring) := bar (LD R) [].
```
i.e. the empty list `[] : list R` is bound to become linearly dependent after finitely many steps, however you extend it by adding elements at its head. As a consequence there cannot exist an infinite sequence of linearly independent elements. But constructivelly, this does not imply that ideals always have finite sets of generators.

We establish the two following results:
```coq
Theorem HBT : noetherian R → noetherian (poly_ring R).
Theorem Hilbert_Basis_Theorem n : noetherian R → noetherian (multivariate_ring R n).
```

where `poly_ring R` is (isomorphic to) `R[X]` and `multivariate_ring R n` is (isomorphic to) `R[X₁,...,Xₙ]`.

## Examples of Noetherian rings

As explained in the previous paragraph, the classical definition of _principal ring_ (as having only mono-generated/principal ideals) is not suited in anti-classical settins
because again, the ring of integers `Z` would not be principal. Instead we define principal rings as:
```coq
Definition principal R := ∃g, Idl R ⌞l⌟ = { x*ᵣg | x ∈ ∈ R }.
```
i.e. every finitely generated ideal is a principal ideal. Notice that this definition of principality __does not__ implies Noetherianess but however 
the two properties are linked in some way, e.g. we show:
```coq
Theorem wf_principal_noetherian (R : ring) :
    principal R
  → (∀ x y : R, x |ᵣ y ∨ ¬ x |ᵣ y)
  → well_founded (λ x y : R, x |ᵣ y ∧ ¬ y |ᵣ x)
  → noetherian R.
```
meaning that any ring which is principal, with (weakly) decidable divisibility, and well-founded strict divisibility is Noetherian.

In addition to the HBT above, with these definitions, we can show that:
- fields are principal and Noetherian rings;
- the ring of integers `Z` is a principal ring and Noetherian ring (via `wf_principal_noetherian` above);
- finite rings are Noetherian (e.g `Z/nZ` for `n > 0`);
- the quotient of a principal (resp. Noetherian) ring is principal (resp. Noetherian).

## Induction principles derived from Noetherianess

We show that several instances of _witnessed strict reverse inclusion_ are 
(constructivelly) well-founded for Noetherian ring:
```coq
Notation "P ⊃ Q" := Q ⊆ P ∧ ∃x, x ∈ P ∧ x ∉ Q.
```
Given a Noetherian ring `R`:
- the relation `⊃` is well-founded when restricted to the ideals of `R`;
- the relation `λ P Q, Idl R P ⊃ Idl R Q` is well-founded on `R → Prop`;
- the relation `λ l m, Idl R ⌞l⌟ ⊃ Idl R ⌞m⌟)` is well-founded on `list R`

where `⌞[x₁;...;xₙ]⌟ := {x₁,...,xₙ}` (mapping a list to a subset of `R`) and `Idl P` is smallest ideal containing the subset `P` of `R`.

## Obtaining finite bases

Using one of the previous induction principles, it is possible to show
the existence of a basis for an ideal, under certain conditions. 
We finish with the construction of a finite basis for ideals satisfying the condition that 
they can be compared for inclusion with any finitely generated ideal:
```coq
Theorem find_basis (R : ring) (I : R → Prop) :
    noetherian R
  → ideal R I
  → (∀ l : list R, (∃x, x ∈ I ∧ ¬ Idl R ⌞l⌟ x) ∨ I ⊆ Idl R ⌞l⌟)
  → ∃b, I = Idl ⌞b⌟.
```
The property `∀l, (∃x, x ∈ I ∧ ¬ Idl ⌞l⌟ x) ∨ I ⊆ Idl ⌞l⌟` states that for any list `l` (of generators), either `I` contains a element outside of the ideal generated by `l`, or is included into it. It is of course is a trivial consequence of the law of excluded middle, but we do not assume exxcluded middle in here.

## Remarks on the proof

- the largest part of the proof, though not the most difficult, is the construction of the polynomial ring `R[X]`, based on the `Setoid` rewriting and `Ring` frameworks of Coq which allows us to micro-manage ring computations, see [`poly.v`](theories/poly.v); Without those two frameworks, that construction could become quite tricky and unsurprisingly, this part was avoided in the implementation proposed in [1].
- the _open induction principle_ of [1] is reinterpreted as a well-founded induction over the projection of a lexicographic product.
- The proof of the `HBT` stated above is quite small (20-25 loc) in [`hbt.v`](theories/hbt.v) but relies on the theorem `update_lead_coef` from [`poly.v`](theories/poly.v) which states that if `x` is the head coefficent of `p` and is a linear combination of the head coefficents of `v`, a list of polynomials of length less than `p`, then `p::v` can be updated into `q::v` where `q := p+lc` is of length strictly less than `p` and `lc` is a linear combination of the values in `v`.
- Updating preserves `LD` (linear dependence) and thus also `bar LD`.

## References

- [1]. [Gröbner Bases in Type Theory](https://link.springer.com/chapter/10.1007/3-540-48167-2_3) by _Coquand & Persson_ 1998.
- [2]. The following discussion is interesting (https://mathoverflow.net/questions/222923/alternate-proofs-of-hilberts-basis-theorem).
- [3]. [Strongly Noetherian rings and constructive ideal theory](https://doi.org/10.1016/j.jsc.2003.02.001) by _Hervé Perdry_ 2004.
- [4]. See also the [Buchberger](https://github.com/rocq-community/buchberger) repository.
