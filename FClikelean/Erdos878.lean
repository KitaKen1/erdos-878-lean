/-
This Lean file was created by KitaKen1 (Kenta Kitamura) with assistance from OpenAI Codex.

It imitates the style of Formal Conjectures for a possible future proposal.
It is not an official Formal Conjectures file and has not been reviewed,
approved, submitted, or merged by that project.
-/

import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic
import FormalConjecturesForMathlib.Data.Set.Density
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Erdős Problem 878

This file formalizes every question in the current natural-language statement of
[Erdős Problem #878](https://www.erdosproblems.com/878). The coefficient-`1/2` declaration
is recorded separately as the sharpening proposed in the official remarks.
-/

open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

/-- The function `f` from Erdős Problem 878. -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/-- The function `F` from Erdős Problem 878. -/
noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).powerset.filter fun A ↦
    A ⊆ Finset.Icc 2 n ∧
      (A : Set ℕ).Pairwise (fun a b ↦ Nat.Coprime a b) ∧
      ∀ a ∈ A, ∀ p, p.Prime → p ∣ a → p ∣ n).sup fun A ↦ ∑ a ∈ A, a

/-- The maximum of an arithmetic function on `{0, ..., x}`. -/
noncomputable def maxUpTo (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sup g

/-- The function `H(x) = ∑_{1 ≤ n < x} f(n)/n`. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / n

/-- Question 1: almost always, `f(n) = o(n log log n)` and `F(n) ≫ n log log n`? -/
@[category research open, AMS 11]
theorem erdos_878.parts.i :
    answer(sorry) ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop]
        (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) ∧
      (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) =O[atTop]
        (fun n : A ↦ (F n : ℝ)) := by
  sorry

/-- Question 2: is `max_{n ≤ x} f(n) ∼ x log x / log log x`? -/
@[category research open, AMS 11]
theorem erdos_878.parts.ii :
    answer(sorry) ↔
      Tendsto (fun x : ℕ ↦
        (maxUpTo f x : ℝ) / ((x : ℝ) * Real.log x / Real.log (Real.log x)))
        atTop (𝓝 1) := by
  sorry

/-- Question 3a: equality of the two maxima for every `x` (known false). -/
@[category research solved, AMS 11]
theorem erdos_878.parts.iii_all : answer(False) ↔
    ∀ x : ℕ, maxUpTo f x = maxUpTo F x := by
  sorry

/-- Question 3b: equality of the two maxima for all sufficiently large `x`? -/
@[category research open, AMS 11]
theorem erdos_878.parts.iii_eventually :
    answer(sorry) ↔ ∀ᶠ x : ℕ in atTop, maxUpTo f x = maxUpTo F x := by
  sorry

/-- Question 4: find an asymptotic for the count of `n < x` with `f(n) = F(n)`. -/
@[category research open, AMS 11]
theorem erdos_878.parts.iv :
    (fun x : ℕ ↦
      (((Finset.Ico 1 x).filter fun n ↦ f n = F n).card : ℝ))
      ~[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Question 5: find an asymptotic formula for `H(x)`. -/
@[category research open, AMS 11]
theorem erdos_878.parts.v :
    H ~[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Question 6: is `H(x) ≪ x log log log log x`? -/
@[category research open, AMS 11]
theorem erdos_878.parts.vi :
    answer(sorry) ↔
      H =O[atTop] fun x : ℕ ↦
        (x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ)))) := by
  sorry

/-- Variant of Question 2. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.second_question_subsequence :
    ∃ X : ℕ → ℕ, Tendsto X atTop atTop ∧
      Tendsto (fun k : ℕ ↦
        (maxUpTo f (X k) : ℝ) /
          ((X k : ℝ) * Real.log (X k) / Real.log (Real.log (X k))))
        atTop (𝓝 1) := by
  sorry

/-- Variant of Question 1. -/
@[category research open, AMS 11]
theorem erdos_878.variants.proposed_first_question_sharp :
    answer(sorry) ↔ ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦
        (F n : ℝ) / ((n : ℝ) * Real.log (Real.log (n : ℝ))))
        atTop (𝓝 (1 / 2 : ℝ)) := by
  sorry

/-- Variant of Question 5. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_div_self_limsup_infinite :
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C ≤ H x / (x : ℝ) := by
  sorry

/-- Variant of Question 5. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_div_self_liminf_finite :
    ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, H x / (x : ℝ) ≤ C := by
  sorry

/-- Variant of Question 6. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_upper_triple_log :
    H =O[atTop] fun x : ℕ ↦
      (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) := by
  sorry

/-- Variant of Questions 5 and 6. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_lower_quadruple_log_infinitely_often :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℕ in atTop,
      c * ((x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ))))) ≤ H x := by
  sorry

/- Variant from the original paper. -/
noncomputable def h (x : ℕ) : ℕ :=
  maxUpTo (fun n ↦ n.primeFactors.card) x

noncomputable def m (x : ℕ) : ℕ := maxUpTo f x

@[category research open, AMS 11]
theorem erdos_878.variants.original_formula_17 :
    answer(sorry) ↔
      Tendsto (fun x : ℕ ↦
        ((x * h x - m x : ℕ) : ℝ) / (x : ℝ)) atTop atTop := by
  sorry

end Erdos878
