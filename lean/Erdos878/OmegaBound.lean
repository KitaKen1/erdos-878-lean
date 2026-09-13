/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import LeanPool.PartialRegularity.Extension

/-!
# The maximal-order upper bound for the number of prime factors

This file develops the real-variable inversion of LeanPool's factorial bound
`(n.primeFactors.card + 1)! ≤ n`. It is the analytic input needed for the upper-bound half of
the maximal-order question in Erdős Problem 878.
-/

open Filter Topology
open scoped Real Topology

namespace Erdos878

/-- The safe, non-sieve LeanPool input used in this module. Keeping it here allows the module to
be imported together with Formal Conjectures without loading LeanPool's legacy Selberg sieve. -/
private theorem succ_omega_factorial_le (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card + 1).factorial ≤ n :=
  LeanPool.PartialRegularity.Extension.primeFactors_factorial_le_1 n hn

/-- Logarithmic Stirling consequence of the factorial bound. -/
private theorem succ_omega_log_sub_le_log (n : ℕ) (hn : 0 < n) :
    let k := n.primeFactors.card + 1
    (k : ℝ) * Real.log k - k ≤ Real.log n := by
  let k := n.primeFactors.card + 1
  have hk : k ≠ 0 := by simp [k]
  have hfac : k.factorial ≤ n := by
    simpa [k] using succ_omega_factorial_le n hn
  have hfacReal : (k.factorial : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfac
  have hlogFac : Real.log (k.factorial : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hfacReal
  have hstirling := Stirling.le_log_factorial_stirling hk
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by simp [k])
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  dsimp only
  linarith

private noncomputable def factorialBarrier (x : ℝ) : ℝ := x * Real.log x - x

/-- The Stirling main term `x log x - x` is strictly increasing from `1` onward. -/
private theorem factorialBarrier_strictMonoOn :
    StrictMonoOn factorialBarrier (Set.Ici 1) := by
  unfold factorialBarrier
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · fun_prop
  · intro x hx
    have hx1 : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
    rw [show deriv (fun y : ℝ ↦ y * Real.log y - y) x = Real.log x by
      change deriv ((fun y : ℝ ↦ y * Real.log y) - id) x = Real.log x
      simpa using ((Real.hasDerivAt_mul_log hx0).sub (hasDerivAt_id x)).deriv]
    exact Real.log_pos hx1

/-- The Stirling barrier evaluated at `c x / log x`, divided by `x`, tends to `c`.
This is the real-variable calculation which makes the leading constant in the maximal-order
upper bound sharp. -/
private theorem tendsto_factorialBarrier_candidate (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ factorialBarrier (c * x / Real.log x) / x)
      atTop (𝓝 c) := by
  have hloglog :
      Tendsto (fun x : ℝ ↦ Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero
  have hconst :
      Tendsto (fun x : ℝ ↦ (Real.log c - 1) / Real.log x) atTop (𝓝 0) :=
    Real.isLittleO_const_log_atTop.tendsto_div_nhds_zero
  have hone : Tendsto (fun _x : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hmain :
      Tendsto
        (fun x : ℝ ↦ c *
          ((Real.log c - 1) / Real.log x + 1 -
            Real.log (Real.log x) / Real.log x)) atTop (𝓝 c) := by
    simpa using (hconst.add hone |>.sub hloglog).const_mul c
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogx0 : Real.log x ≠ 0 := hlogx.ne'
  rw [factorialBarrier, Real.log_div (mul_ne_zero hc.ne' hx0) hlogx0,
    Real.log_mul hc.ne' hx0]
  field_simp
  ring

/-- For every `c > 1`, the Stirling barrier at `c x / log x` eventually lies strictly above
`x`. -/
private theorem eventually_lt_factorialBarrier_candidate (c : ℝ) (hc : 1 < c) :
    ∀ᶠ x : ℝ in atTop, x < factorialBarrier (c * x / Real.log x) := by
  filter_upwards [
    (tendsto_factorialBarrier_candidate c (zero_lt_one.trans hc)).eventually_const_lt hc,
    eventually_gt_atTop (0 : ℝ)] with x hratio hx
  have h := (lt_div_iff₀ hx).mp (by simpa using hratio)
  nlinarith

/-- Sharp eventual upper bound for the number of distinct prime divisors. This is the
`ω(n) ≤ (1 + ε) log n / log log n` estimate, proved from LeanPool's factorial inequality rather
than imported as a black box. -/
theorem eventually_card_primeFactors_le_log_div_loglog (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.primeFactors.card : ℝ) ≤
        (1 + ε) * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := by
  let c : ℝ := 1 + ε
  have hc : 1 < c := by simp [c, hε]
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
    hlogNat.eventually (eventually_lt_factorialBarrier_candidate c hc),
    hlogNat.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with n hbarrier hlogn hn
  let L : ℝ := Real.log (n : ℝ)
  let A : ℝ := c * L / Real.log L
  let k : ℝ := (n.primeFactors.card + 1 : ℕ)
  have hL : 0 < L := zero_lt_one.trans hlogn
  have hlogL : 0 < Real.log L := Real.log_pos hlogn
  have hApos : 0 < A := div_pos (mul_pos (zero_lt_one.trans hc) hL) hlogL
  have hLA : L < factorialBarrier A := by simpa [L, A] using hbarrier
  have hAone : 1 ≤ A := by
    by_contra hA
    have hAlt : A < 1 := lt_of_not_ge hA
    have hlogA : Real.log A < 0 := Real.log_neg hApos hAlt
    have : factorialBarrier A < 0 := by
      unfold factorialBarrier
      nlinarith
    linarith
  have hkone : 1 ≤ k := by simp [k]
  have hkbarrier : factorialBarrier k ≤ L := by
    simpa [factorialBarrier, k, L] using
      succ_omega_log_sub_le_log n hn
  have hkA : k ≤ A := by
    by_contra hk
    have hAk : A < k := lt_of_not_ge hk
    have := factorialBarrier_strictMonoOn hAone hkone hAk
    linarith
  change (n.primeFactors.card : ℝ) ≤
    (1 + ε) * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))
  have homega_le_k : (n.primeFactors.card : ℝ) ≤ k := by
    simp [k]
  exact homega_le_k.trans (by simpa [A, L, c] using hkA)

/-- Uniform sharp bound for the largest value of `ω(n)` with `n ≤ x`. This is the form used
after the pointwise estimate `f(n) ≤ n ω(n)`. -/
theorem eventually_max_card_primeFactors_le_log_div_loglog (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (((Finset.range (x + 1)).sup fun n ↦ n.primeFactors.card : ℕ) : ℝ) ≤
        (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
  let c : ℝ := 1 + ε
  have hc : 1 < c := by simp [c, hε]
  have hlogNat :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
    hlogNat.eventually (eventually_lt_factorialBarrier_candidate c hc),
    hlogNat.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with x hbarrier hlogx hx
  let L : ℝ := Real.log (x : ℝ)
  let A : ℝ := c * L / Real.log L
  have hL : 0 < L := zero_lt_one.trans hlogx
  have hlogL : 0 < Real.log L := Real.log_pos hlogx
  have hApos : 0 < A := div_pos (mul_pos (zero_lt_one.trans hc) hL) hlogL
  have hLA : L < factorialBarrier A := by simpa [L, A] using hbarrier
  have hAone : 1 ≤ A := by
    by_contra hA
    have hAlt : A < 1 := lt_of_not_ge hA
    have hlogA : Real.log A < 0 := Real.log_neg hApos hAlt
    have : factorialBarrier A < 0 := by
      unfold factorialBarrier
      nlinarith
    linarith
  have hrange : (Finset.range (x + 1)).Nonempty := by simp
  obtain ⟨n, hnrange, hsup⟩ :=
    Finset.sup_mem_of_nonempty (f := fun n ↦ n.primeFactors.card) hrange
  rw [show (Finset.range (x + 1)).sup (fun n ↦ n.primeFactors.card) =
      n.primeFactors.card from hsup.symm]
  by_cases hn0 : n = 0
  · simp only [hn0, Nat.primeFactors_zero, Finset.card_empty, Nat.cast_zero]
    simpa [A, L, c] using hApos.le
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnx : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)
  have hlognL : Real.log (n : ℝ) ≤ L := by
    apply Real.log_le_log
    · exact_mod_cast hnpos
    · exact_mod_cast hnx
  let k : ℝ := (n.primeFactors.card + 1 : ℕ)
  have hkone : 1 ≤ k := by simp [k]
  have hkbarrier : factorialBarrier k ≤ L := by
    calc
      factorialBarrier k ≤ Real.log (n : ℝ) := by
        simpa [factorialBarrier, k] using
          succ_omega_log_sub_le_log n hnpos
      _ ≤ L := hlognL
  have hkA : k ≤ A := by
    by_contra hk
    have hAk : A < k := lt_of_not_ge hk
    have := factorialBarrier_strictMonoOn hAone hkone hAk
    linarith
  change (n.primeFactors.card : ℝ) ≤
    (1 + ε) * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))
  have homega_le_k : (n.primeFactors.card : ℝ) ≤ k := by
    simp [k]
  exact homega_le_k.trans (by simpa [A, L, c] using hkA)

end Erdos878
