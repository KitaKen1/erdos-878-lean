# Prospective Formal Conjectures target

This directory contains an unofficial, AI-assisted statement mock-up for
Erdős Problem #878. It is not an official Formal Conjectures file and has not
been reviewed, approved, submitted, or merged by that project.

It contains all seven questions from the current problem statement and all six conjectures or
known results listed in the official remarks. The five prior results use the
`erdos_878.variants` entries and `research solved`; this records their historical status
and does not present them as new results of this repository.

The catalog entries follow the Formal Conjectures source convention:

```lean
@[category research open, AMS 11]
theorem entry_name : answer(sorry) ↔ statement := by
  sorry
```

Here `def` is reserved for mathematical objects and predicates such as `f`, `F`, and
`IsAdmissible`. For an open yes/no question, `answer(sorry)` leaves the answer unknown; writing
`answer(True)` there would already assert an affirmative answer. The final `by sorry` is a second,
different placeholder—the proof of the catalog theorem. The separate `lean/` project instantiates
the proposed answers with `True` and keeps some `def ... : Prop` statement aliases so that its
modular, `sorry`-free proof theorems can use those propositions as target types.

The proposed `True` instantiation of Main 1 is proved, without extra analytic assumptions, by
[`erdos_878_first_question`](../lean/Erdos878/FixedLoss.lean). It fills the answer hole in
`erdos_878.parts.i`; this FClike directory remains the complete seven-question statement package. The original
formula-(17) natural-endpoint target is likewise proved by
[`original_formula_17_proved`](../lean/Erdos878/Formula17.lean).
The sharper coefficient-`1/2` declaration is now proved directly by
[`proposed_first_question_sharp`](../lean/Erdos878/SharpFirstAsymptotic.lean).
The seven source questions are all represented.  The admissibility definition explicitly excludes
the term `1`, as required by the original paper's assertion `f(p^a) = F(p^a)`; otherwise every
nonempty admissible family could be enlarged by adding `1`.  Questions (iv) and (v) use
Formal Conjectures' function-valued `answer(sorry)` syntax rather than the vacuous assertion that
some asymptotic comparison function exists.  The relevant proof targets were compared against the
proof project and match exactly.

The sharp coefficient-`1/2` density-one `F` statement now has a kernel-verified proof candidate in
[`SharpFirstAsymptotic.lean`](../lean/Erdos878/SharpFirstAsymptotic.lean), whose theorem
`Erdos878.proposed_first_question_sharp` has the exact FC-like sharp type. The ordinary
maximal-order `f` statement likewise has a kernel-verified proof candidate in
[`TrackBEndpointParameters.lean`](../lean/Erdos878/TrackBEndpointParameters.lean), whose theorem
`erdos_878_parts_ii_proved` has type `erdos_878.parts.ii` in the core package. For yes/no entries,
the core package is the `True` instantiation of this catalog's unknown answer; their mathematical
right-hand sides are identical.
It has not yet received independent mathematical or Formal Conjectures review. An internal
certificate audit rejects the earlier prefix-weighted Track-A and reciprocal-mass Track-B
shortcuts because their assumptions are inconsistent; the new Track-B proof uses a different
Vaughan/Fejér prime-count route.
The separate
[`TrackBPublicationAudit.lean`](../lean/Erdos878/TrackBPublicationAudit.lean) checks the unfolded
statement and a concrete finite packed-multiple example without changing this statement file.
The statement coverage here is unchanged; the corrected proof interface in
[`MatchingAsymptotic.lean`](../lean/Erdos878/MatchingAsymptotic.lean) uses actual admissible
matching terms and their counting and endpoint errors.

## Complete source coverage

[`Erdos878.lean`](Erdos878.lean) formalizes every natural-language question on
the current problem page. In particular, it does not replace the multi-part
problem by only the new proposed result.

The file contains:

- the current Erdős Problems finite-set definition of `F`;
- all seven question targets, splitting “for all `x`, or perhaps all large
  `x`” into two precise propositions; and
- Main 1, its sharpened `1/2` variant, and the independent
  maximal-order target pursued by this repository; and
- the exact formula (17) addendum from Erdős's original paper.

## Targets used by the proof projects

The first exact FC entry is Main 1 itself:

```lean
@[category research open, AMS 11]
theorem erdos_878.parts.i :
    answer(sorry) ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop]
        (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) ∧
      (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) =O[atTop]
        (fun n : A ↦ (F n : ℝ)) := by
  sorry
```

The public first-question entries, including the sharp `1/2` variant, spell out
`n * log (log n)` directly. The helper `scale` remains internal to the modular proof project.

The official-Remarks sharpening is named explicitly as
`erdos_878.variants.proposed_first_question_sharp`.  Its declaration contains exactly the
density-one coefficient-`1/2` limit for `F`; the independent `f=o(n log log n)` clause remains in
`parts.i` and is not duplicated in this variant. Its public catalog metadata remains
`research open`, and its answer remains `answer(sorry)`, until external acceptance. The proof
project supplies the proposed `True` instantiation.

The corresponding proof-development target is in
[`../lean/Erdos878FC.lean`](../lean/Erdos878FC.lean). Its standalone mathlib-only Lean4Web proof is
[`../lean4web/ProposedFirstQuestionSharpLean4Web.lean`](../lean4web/ProposedFirstQuestionSharpLean4Web.lean).

The entry preserves Formal Conjectures' open-question form `answer(sorry)`. Its catalog proof body
is also a placeholder; the proof-development project separately supplies the `answer(True)`
solution theorem and its kernel-dependency audit.

The proof project also closes the exact Question 2 entry,
`erdos_878.parts.ii`, concerning the ordinary limit
`max_{n≤x} f(n) ~ x log x / log log x`.

The additional source target, `original_formula_17`, uses the original-paper notation
`h(x)=max_{n≤x}ω(n)` and `m(x)=max_{n≤x}f(n)`. It is not counted as an eighth question on the
current problem page: it is explicitly an addendum from the 1984 source.

The proof project also contains a verified `RelaxedBound` module that converts
`f(n)/n` into a logarithmic product-budget term plus a finite positive-part surplus.
The endpoint-band summation and pointwise upper bound are now closed; the new `Formula17`
module adds the Chebyshev lower bound and finite-maximum transfer to prove the original
divergence.

The target currently builds successfully with `lake build Erdos878` (3018 jobs). Warnings about
declarations using `sorry` are expected for an FC-style conjecture catalog, so `--wfail` is not
used for this package. The known false answer to `parts.iii_all` is recorded here with a
placeholder proof; its constructive `x = 210` verification remains in the separate proof project.

The remaining questions are represented as categorized theorem entries. The two requests to
“find an asymptotic formula” instead mark the unknown function using `answer(sorry)`, following
Formal Conjectures practice; those markers are answers to be supplied, not fake solution proofs.
Solved metadata and `answer(True/False)` are used here only for results already settled before
publication, including the finite counterexample. This repository's new solution candidates stay
`research open` with `answer(sorry)` in the prospective FC catalog until external acceptance;
compilation of a statement alone is not treated as a solution.

## Definition boundary

The source page currently lets `F(n)` use an arbitrary finite set of distinct nontrivial positive
terms. This is the sole definition of `F` used by the catalog and all four proof targets.
