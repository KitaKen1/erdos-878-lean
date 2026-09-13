# Erdős Problem #878 in Lean

This repository presents five contributions related to
[Erdős Problem #878](https://www.erdosproblems.com/878).

1. **Complete FC-shaped statements.** The current problem page contains seven questions and six
   additional conjectures/results in its official remarks.
   [`FClikelean/Erdos878.lean`](FClikelean/Erdos878.lean) formalizes all of them, rather than
   replacing the source problem by only the questions addressed here.
2. **A Lean proof of the first question.** The proof project directly proves the fixed-loss
   statement in `erdos_878.parts.i`.
3. **A Lean proof of the second question.** The proof project supplies a direct theorem of
   `erdos_878.parts.ii`. In particular, it proves the ordinary
   all-endpoint maximal-order limit
   `max_{n ≤ x} f(n) ∼ x log x / log log x`.
4. **A Lean proof of the sharp `1/2` variant.** The proof project proves the separate
   official-remarks conjecture `F(n) ∼ (1/2)n log log n` on a density-one set.
5. **A Lean proof of the original formula (17).** The 1984 paper additionally asks whether
   `(x h(x) - m(x)) / x → ∞`. This source-level addendum is formalized and proved separately.

**Try it in Lean4Web:**

- [open the first-question proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-878-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FPartsILean4Web.lean)
- [open the second-question proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-878-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FPartsIILean4Web.lean)
- [open the sharp `1/2`-variant proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-878-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FProposedFirstQuestionSharpLean4Web.lean)
- [open the original formula (17) proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-878-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FOriginalFormula17Lean4Web.lean)

These are **Lean-kernel-verified solution candidates**. They have not yet received independent
mathematical review, acceptance by Formal Conjectures, or official solved status on the Erdős
Problems site. `OPEN → SOLVED` below means a kernel-verified solution claim made by this
repository, pending that external review.

## Problem and variant status

| Entry | Statement | Status and source |
| --- | --- | --- |
| Main 1 — `parts.i` | For almost all `n`, `f(n) = o(n log log n)` and `F(n) ≫ n log log n` | **OPEN → SOLVED** · direct Lean proof in this repository |
| Main 2 — `parts.ii` | `max_{n ≤ x} f(n) ∼ x log x / log log x` | **OPEN → SOLVED** · direct Lean proof in this repository |
| Main 3a — `parts.iii_all` | `max_{n ≤ x} f(n) = max_{n ≤ x} F(n)` for every `x` | **SOLVED previously** · false at `x = 210`; Lean-checked here |
| Main 3b — `parts.iii_eventually` | The same equality for every sufficiently large `x` | **OPEN** |
| Main 4 — `parts.iv` | Find an asymptotic for the count of `n < x` with `f(n) = F(n)` | **OPEN** |
| Main 5 — `parts.v` | Find an asymptotic formula for `H(x) = ∑_{n < x} f(n)/n` | **OPEN** |
| Main 6 — `parts.vi` | Is `H(x) ≪ x log log log log x`? | **OPEN** |

## Official remarks: variants and known results

| Entry | Statement | Status | Source |
| --- | --- | --- | --- |
| <code>variants.<wbr>second_question_<wbr>subsequence</code> | Along some sequence `x → ∞`, `max_{n ≤ x} f(n) ∼ x log x / log log x` | **SOLVED** | Erdős Problems forum |
| <code>variants.<wbr>proposed_first_<wbr>question_sharp</code> | For almost all `n`, `F(n) ∼ (1/2)n log log n` | **OPEN → SOLVED** | Erdős Problems forum |
| <code>variants.<wbr>H_div_self_<wbr>limsup_infinite</code> | `limsup H(x)/x = ∞` | **SOLVED** | Erdős Problems forum |
| <code>variants.<wbr>H_div_self_<wbr>liminf_finite</code> | `liminf H(x)/x < ∞` | **SOLVED** | Erdős Problems forum |
| <code>variants.<wbr>H_upper_<wbr>triple_log</code> | `H(x) ≪ x log log log x` | **SOLVED** | Erdős Problems forum |
| <code>variants.<wbr>H_lower_<wbr>quadruple_log_<wbr>infinitely_often</code> | `∃ c > 0, ∀ X, ∃ x ≥ X, c x log log log log x ≤ H(x)` | **SOLVED** | Erdős Problems forum |
| <code>variants.<wbr>original_<wbr>formula_17</code> | `(x h(x) - m(x))/x → ∞` | **OPEN → SOLVED** | [Er84e] |

## Formal Conjectures-shaped proved targets

These are the four Formal Conjectures-shaped target entries addressed by this repository:

```lean
@[category research open, AMS 11]
theorem erdos_878.parts.i :
    answer(sorry) ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop]
        (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) ∧
      (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) =O[atTop]
        (fun n : A ↦ (F n : ℝ)) := by
  sorry

@[category research open, AMS 11]
theorem erdos_878.parts.ii :
    answer(sorry) ↔
      Tendsto (fun x : ℕ ↦
        (maxUpTo f x : ℝ) / ((x : ℝ) * Real.log x / Real.log (Real.log x)))
        atTop (𝓝 1) := by
  sorry

@[category research open, AMS 11]
theorem erdos_878.variants.proposed_first_question_sharp :
    answer(sorry) ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦
        (F n : ℝ) / ((n : ℝ) * Real.log (Real.log (n : ℝ))))
        atTop (𝓝 (1 / 2 : ℝ)) := by
  sorry

@[category research open, AMS 11]
theorem erdos_878.variants.original_formula_17 :
    answer(sorry) ↔
      Tendsto (fun x : ℕ ↦
        ((x * h x - m x : ℕ) : ℝ) / (x : ℝ)) atTop atTop := by
  sorry
```

The `answer(sorry)` and final `by sorry` are the catalog placeholders. The separate proof project
proves the affirmative instantiations of these exact mathematical targets without `sorry`.

## Directory layout

| Directory / file | Contents |
| --- | --- |
| [`FClikelean/Erdos878.lean`](FClikelean/Erdos878.lean) | All seven current source questions, all six official-remarks statements, the original-paper addendum, and FC metadata; proofs are placeholders |
| [`lean/`](lean/) | Modular proof development and the main build project |
| [`lean/Erdos878/FixedLoss.lean`](lean/Erdos878/FixedLoss.lean) | Direct proof of `erdos_878.parts.i` |
| [`lean/Erdos878/SharpFirstAsymptotic.lean`](lean/Erdos878/SharpFirstAsymptotic.lean) | Direct proof of the coefficient-`1/2` density-one variant |
| [`lean/Erdos878/DensityDiagonal.lean`](lean/Erdos878/DensityDiagonal.lean) | Density-one pseudointersection used to diagonalize all fixed lower coefficients |
| [`lean/Erdos878/OmegaNormalOrder.lean`](lean/Erdos878/OmegaNormalOrder.lean) | Hardy–Ramanujan normal order in the exact density-one subtype form |
| [`lean/Erdos878/TrackBEndpointParameters.lean`](lean/Erdos878/TrackBEndpointParameters.lean) | Final all-endpoint parameters and direct proof of `erdos_878.parts.ii` |
| [`lean/Erdos878/TrackBPublicationAudit.lean`](lean/Erdos878/TrackBPublicationAudit.lean) | Statement checksum and concrete packed-multiple regression |
| [`lean/Erdos878/Formula17.lean`](lean/Erdos878/Formula17.lean) | Direct proof of the original formula (17) |
| [`lean/Erdos878/Verification.lean`](lean/Erdos878/Verification.lean) | Repository-wide kernel dependency audit |
| [`lean4web/PartsILean4Web.lean`](lean4web/PartsILean4Web.lean) | Standalone Lean4Web proof of `erdos_878.parts.i` |
| [`lean4web/PartsIILean4Web.lean`](lean4web/PartsIILean4Web.lean) | Standalone Lean4Web proof of `erdos_878.parts.ii` |
| [`lean4web/ProposedFirstQuestionSharpLean4Web.lean`](lean4web/ProposedFirstQuestionSharpLean4Web.lean) | Standalone Lean4Web proof of the sharp `1/2` variant |
| [`lean4web/OriginalFormula17Lean4Web.lean`](lean4web/OriginalFormula17Lean4Web.lean) | Standalone Lean4Web proof of the original formula (17) |

## Verification

The projects use Lean `4.34.0-rc1`. The main project pins Formal Conjectures commit
`205d301d60d01a2a432cbea611f9383cd08f9065` and LeanPool commit
`c8ddda0a64f21cb019720cdda48c94354d4091e7`.

```bash
cd lean
lake update
lake exe cache get
lake --wfail build
```

The four standalone files under `lean4web/` use Lean and Mathlib `4.34.0-rc2`. Each file can be
pasted into Lean4Web independently. Its final theorem repeats the corresponding FClikeLean entry
name and statement with `answer(True)`, followed by `#check` and `#print axioms` for that theorem.

The complete FC-shaped statement file is checked separately:

```bash
cd FClikelean
lake update
lake exe cache get
lake build Erdos878
```

The FC-shaped catalog intentionally contains `by sorry` placeholders and therefore emits expected
`declaration uses 'sorry'` warnings. The separate proof project and four Lean4Web proof files are
the artifacts audited without project-specific mathematical axioms.

Focused publication checks:

```bash
cd lean
lake --wfail build Erdos878.TrackBVerification
lake --wfail build Erdos878.TrackBPublicationAudit
```

Last local verification on 2026-09-13:

- main default build: **3904/3904 jobs**;
- Track-B theorem audit: **3873/3873 jobs**, with 204 listed theorems;
- publication regression audit: **3873/3873 jobs**;
- FC-shaped statement build: **3018/3018 jobs**.

The final claims have no `sorry`, `admit`, `sorryAx`, or project-specific mathematical axioms.
The printed dependency audit reports only Lean/Mathlib's standard logical dependencies
`propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical explanation (AI generated)

### First question

The proof first obtains `f(n) = o(n log log n)` on a density-one set. For the lower bound on `F`,
it uses two disjoint prime windows whose reciprocal masses are positive multiples of
`log log n`. Bad prime pairs and low divisor counts are placed in density-zero exceptional sets.
Outside those sets, the prime powers dividing `n` can be packed into one admissible pairwise-
coprime family, producing `F(n) ≥ c n log log n` for an explicit fixed `c > 0`. Intersecting the
two density-one sets proves the complete statement `erdos_878.parts.i`.

### Second question

The upper bound follows from the maximal order of the number of distinct prime factors. For the
lower bound, the proof establishes reciprocal-log exponential-sum estimates using a finite
Vaughan decomposition, Type-I/II estimates, and a finite Fejér kernel. Chebyshev bounds remove
higher prime powers and leave sufficiently many actual primes in a short phase window.

For a large endpoint `X`, the final choice is

```text
T = log X,
v = log T,
P = ceil(T v^128),
N = floor((1 - δ)T / log(16P)).
```

The selected `N` primes have product at most the available budget. Their largest powers below a
single packed multiple contribute at least
`N exp(T - 4/log P)` to `max_{n ≤ X} f(n)`. This normalized lower bound tends to `1 - δ`; letting
`δ` follow an arbitrary error and combining it with the proved upper bound gives the ordinary
limit at every sufficiently large endpoint.

The finite packing is also regression-tested at `S = {2,3}` and `X = 35`: the prime product is
`6`, the chosen multiple is `30`, and the selected contribution is `2^4 + 3^3 = 43`.

### Sharp `1/2` variant

For every coefficient `c < 1/2`, the proof chooses a sufficiently large finite family of disjoint
prime-window pairs. The bad-pair reciprocal-weight estimate and divisor-count second moment show
that the union of their exceptional sets has density zero. A combined admissible packing then
gives `F(n)/(n log log n) ≥ c` outside that exceptional set. A density-one pseudointersection
diagonal puts all rational lower coefficients approaching `1/2` on one set. For the reverse
inequality, the pointwise bound `F ≤ f + nω/2 + 1`, the already proved little-o estimate for `f`,
and Hardy–Ramanujan normal order for `ω` give limsup at most `1/2`. The resulting squeeze proves
`F(n)/(n log log n) → 1/2` on a density-one set.

### Original formula (17)

An elementary integer-base surplus bound gives a pointwise upper estimate for `f(n)/n`, while
Chebyshev's lower estimate supplies a lower bound for `h(x)`. The resulting pointwise deficit
tends to infinity. A finite-maximum transfer then proves that
`(x h(x) - m(x))/x → ∞`.

## References

- [Erdős Problems #878](https://www.erdosproblems.com/878)
- [P. Erdős, *On two unconventional number theoretic functions and on some related problems* (1984)](https://www.renyi.hu/~p_erdos/1984-16.pdf)
- [Formal Conjectures tracking issue #997](https://github.com/google-deepmind/formal-conjectures/issues/997)
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
- [LeanPool](https://github.com/Vilin97/lean-pool)
- [Erdős #873 Lean repository used as the README presentation model](https://github.com/KitaKen1/erdos-873-lean)

Third-party attribution and pinned-source details are recorded in [`NOTICE`](NOTICE).

## AI usage disclosure

This formalization, proof development, mathematical exploration, and documentation were produced
with assistance from OpenAI Codex and ChatGPT Astra under the direction of KitaKen1
(Kenta Kitamura).
