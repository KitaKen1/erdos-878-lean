/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import LeanPool.DeadEnds.PrimeTail
import LeanPool.Erdos1196.PreliminariesMertens
import LeanPool.PartialRegularity.Extension
import LeanPool.SelbergSieve4.Applications.BrunTitchmarsh
import LeanPool.SelbergSieve4.MainResults

/-!
# Upstream analytic inputs for Erdős Problem 878

This module pins and re-exports four already formalized inputs which match the proof architecture:

* Mathlib's reduced-rational form of Dirichlet approximation;
* LeanPool's bounded-error von Mangoldt Mertens estimate;
* LeanPool's convergent squared-prime-tail estimate;
* LeanPool's explicit short-interval prime-counting upper bound;
* LeanPool's factorial lower bound from the number of distinct prime factors.

The wrappers make the exact interfaces useful to this project visible in one small file. They do
not assert the still-missing bad-prime-pair estimate. This module is compiled as an independent
library root: LeanPool's pre-upstream Selberg sieve currently uses declaration names that collide
with the Selberg sieve now present in Mathlib's umbrella import used by Formal Conjectures.
-/

open scoped ArithmeticFunction BigOperators

namespace Erdos878.Upstream

/-- Dirichlet approximation with a rational in canonical reduced form. Using `q.den` here avoids
the error of treating an unreduced presentation `h / r` as if its grid spacing were `1 / r`. -/
theorem exists_reduced_rat_approx (ξ : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ q : ℚ, |ξ - q| ≤ 1 / ((M + 1) * q.den) ∧ q.den ≤ M :=
  Real.exists_rat_abs_sub_le_and_den_le ξ hM

/- A small representation bridge for the Dirichlet output.  Mathlib's rational is already stored
   in reduced form, but the rotation lemmas use natural-number data.  For a nonnegative rational,
   the signed numerator can therefore be replaced by its natural absolute value without changing
   the real quotient, while `q.reduced` supplies the coprimality needed by `ZMod`. -/
theorem nonneg_rat_num_den_data {q : ℚ} (hq : 0 ≤ q) :
    Nat.Coprime q.num.natAbs q.den ∧
      (q.num.natAbs : ℝ) / (q.den : ℝ) = (q : ℝ) := by
  refine ⟨q.reduced, ?_⟩
  have hnum : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumR' := congrArg (fun z : ℤ => (z : ℝ)) hnum
  have hnumR : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    exact hnumR'
  rw [hnumR, Rat.cast_def]

/- When the approximated real is at least one, the rational supplied by Dirichlet's theorem is
   automatically nonnegative: its error is at most one because both `M+1` and the canonical
   denominator are positive integers.  This packages the exact natural `h/r` data needed by the
   rotation route, including coprimality and the denominator bound. -/
theorem exists_nonneg_reduced_rat_approx {ξ : ℝ} {M : ℕ} (hM : 0 < M)
    (hξ : 1 ≤ ξ) :
    ∃ h r : ℕ, 0 < r ∧ r ≤ M ∧ Nat.Coprime h r ∧
      |ξ - (h : ℝ) / (r : ℝ)| ≤ 1 / (((M : ℝ) + 1) * (r : ℝ)) := by
  obtain ⟨q, hqapprox, hqden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le ξ hM
  have hdenpos : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hprodpos : 0 < ((M : ℝ) + 1) * (q.den : ℝ) := mul_pos hMpos hdenpos
  have hMone : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have hMoneNat : (1 : ℕ) ≤ M + 1 := by omega
    exact_mod_cast hMoneNat
  have hdenone : (1 : ℝ) ≤ (q.den : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr q.den_ne_zero)
  have hprodone : 1 ≤ ((M : ℝ) + 1) * (q.den : ℝ) := by
    simpa using (mul_le_mul hMone hdenone (by positivity) (by positivity))
  have herr_le_one : |ξ - (q : ℝ)| ≤ 1 := by
    apply le_trans hqapprox
    apply (div_le_one hprodpos).2
    exact hprodone
  have hdiff : ξ - (q : ℝ) ≤ 1 := (le_abs_self _).trans herr_le_one
  have hqnonneg : 0 ≤ (q : ℝ) := by linarith
  have hqnonnegRat : (0 : ℚ) ≤ q := by exact_mod_cast hqnonneg
  have hdata := nonneg_rat_num_den_data hqnonnegRat
  refine ⟨q.num.natAbs, q.den, ?_, hqden, hdata.1, ?_⟩
  · exact q.den_pos
  · rw [hdata.2]
    exact hqapprox

/-- Bounded-error Mertens estimate already proved in LeanPool. This is a von Mangoldt-weighted
input; obtaining the exact prime reciprocal mass in the moving windows remains a separate step. -/
theorem vonMangoldt_mertens_bounded_error :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃t : ℕ⦄, 2 ≤ t →
        |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C :=
  PrimitiveSetsAboveX.mertensEstimate

/-- A convergent squared-prime tail estimate from LeanPool. It is not the desired `∑ 1/p`
window estimate, but is immediately usable when square-divisibility exceptional sets occur. -/
theorem squared_prime_tail_small (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ,
      ∑' (p : {q : Nat.Primes // (q : ℕ) > y}),
        1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 < ε :=
  LeanPool.DeadEnds.prime_tail_sum_small ε hε

/-- Explicit LeanPool short-interval prime upper bound. This is the main existing ingredient for
turning a logarithmic interval for `q` into an upper bound for its reciprocal prime mass. -/
theorem short_interval_prime_count
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    BrunTitchmarsh.primesBetween x (x + y) ≤
      2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3 :=
  BrunTitchmarsh.primesBetween_le x y z hx hy hz

/- LeanPool's Selberg-sieve application also proves the global prime-counting upper bound
   π(N) ≪ N/log N.  Re-export it here so later finite reindexing code can use the same
   publication-level upstream namespace. -/
theorem primeCounting_le_mul_bound :
    ∃ N C, ∀ n ≥ N, (Nat.primeCounting n : ℝ) ≤ C * (n : ℝ) / Real.log (n : ℝ) := by
  simpa using (primeCounting_le_mul)

/- A sign-normalized form of the same bound.  Replacing the constant by `max C 0` and the
   threshold by `max N 2` makes all later denominator comparisons unconditional. -/
theorem primeCounting_le_mul_bound_nonneg :
    ∃ N C, 0 ≤ C ∧ ∀ n ≥ N,
      (Nat.primeCounting n : ℝ) ≤ C * (n : ℝ) / Real.log (n : ℝ) := by
  obtain ⟨N₀, C₀, hπ⟩ := primeCounting_le_mul_bound
  refine ⟨max N₀ 2, max C₀ 0, le_max_right _ _, ?_⟩
  intro n hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hbase := hπ n hnN₀
  have hnone : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnone
  have hnquot : 0 ≤ (n : ℝ) / Real.log (n : ℝ) :=
    div_nonneg (by positivity) hlogpos.le
  have hmul : C₀ * ((n : ℝ) / Real.log (n : ℝ)) ≤
      max C₀ 0 * ((n : ℝ) / Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hnquot
  exact hbase.trans (by simpa [div_eq_mul_inv, mul_assoc] using hmul)

/-- A direct combinatorial input for the upper half of the maximal-order argument. LeanPool
actually proves the slightly stronger `(omega n + 1)! ≤ n`, rather than merely `omega n ! ≤ n`. -/
theorem succ_omega_factorial_le (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card + 1).factorial ≤ n :=
  LeanPool.PartialRegularity.Extension.primeFactors_factorial_le_1 n hn

/-- A logarithmic consequence of the factorial bound and Mathlib's formalized Stirling lower
bound. This is the exact implicit inequality behind the standard maximal-order upper estimate
for the number of distinct prime divisors. -/
theorem succ_omega_log_sub_le_log (n : ℕ) (hn : 0 < n) :
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

end Erdos878.Upstream
