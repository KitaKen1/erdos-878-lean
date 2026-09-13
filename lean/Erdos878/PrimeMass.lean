/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/

import Erdos878.Upstream
import Erdos878.BadPair
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Reciprocal prime mass in a short interval

This file proves the elementary bridge from a prime-counting estimate to the reciprocal mass
of those primes.  The result is one of the reusable, `sorry`-free pieces needed by the
bad-prime-pair approach to Erdős Problem 878.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos878

/-- The sum of `1 / p` over primes in the real interval `[a, b]`. -/
def reciprocalPrimesBetween (a b : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime, ((p : ℝ)⁻¹)

/- The finite h-sum in the Brun main term is the ordinary harmonic number.  Exposing this
inequality lets the eventual report-scale argument use the standard `1 + log H` bound rather
than introducing a second analytic axiom. -/
theorem reciprocal_harmonic_sum_le_one_add_log (H : ℕ) :
    (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) ≤ 1 + Real.log (H : ℝ) := by
  have heq : (harmonic H : ℝ) =
      ∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹) := by
    rw [harmonic_eq_sum_Icc]
    norm_num
  rw [← heq]
  exact_mod_cast harmonic_le_one_add_log H

/- The harmonic lower bound supplies a fully formal divergence scale for block sums. -/
theorem tendsto_harmonic_real_atTop :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using Real.tendsto_log_atTop.comp hnat
  have hle : ∀ᶠ n : ℕ in atTop,
      Real.log ((n + 1 : ℕ) : ℝ) ≤ (harmonic n : ℝ) :=
    Filter.Eventually.of_forall (fun n ↦ log_add_one_le_harmonic n)
  exact Filter.tendsto_atTop_mono' atTop hle hlog

/- Mathlib's elementary Erdős proof of the divergence of the reciprocal-prime series can be
   reindexed as a monotone partial sum over `Nat.primesBelow`.  This is an unconditional mass
   source for later moving-window arguments; it does not assert that every short logarithmic
   window has the required mass. -/
theorem tendsto_reciprocal_prime_sum_atTop :
    Tendsto (fun N : ℕ ↦
      ∑ p ∈ N.primesBelow, ((p : ℝ)⁻¹)) atTop atTop := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ Set.indicator {p : ℕ | p.Prime} (fun _ ↦ (1 : ℝ) / n) n := by
    intro n
    by_cases hn : n.Prime <;> simp [Set.indicator, hn]
  have hpartial : Tendsto (fun N : ℕ ↦
      ∑ n ∈ Finset.range N,
        Set.indicator {p : ℕ | p.Prime} (fun n ↦ (1 : ℝ) / n) n) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
      not_summable_one_div_on_primes
  convert hpartial using 1
  funext N
  rw [Nat.primesBelow_eq_filter_range, Finset.sum_filter]
  simp [Set.indicator]

/- A finite form of the preceding divergence theorem.  It is convenient when an analytic
   certificate asks for a prescribed reciprocal-prime mass rather than a filter statement. -/
theorem eventually_reciprocal_prime_sum_ge (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C ≤ ∑ p ∈ N.primesBelow, ((p : ℝ)⁻¹) := by
  exact tendsto_reciprocal_prime_sum_atTop.eventually (eventually_ge_atTop C)

/- The explicit finite block from Mathlib's Erdős proof is a convenient certificate for moving
   prime-window constructions: it has reciprocal mass at least `1/2` and contains only primes
   at or above the prescribed cutoff.  The block is deliberately retained as a concrete Finset
   rather than hidden behind an existence theorem. -/
theorem exists_prime_family_mass_half_above (K : ℕ) :
    ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) ∧
      (∀ p ∈ S, K ≤ p) ∧
      1 / 2 ≤ ∑ p ∈ S, ((p : ℝ)⁻¹) := by
  let S : Finset ℕ :=
    (4 ^ (K.primesBelow.card + 1)).succ.primesBelow \ K.primesBelow
  have hmass : 1 / 2 ≤ ∑ p ∈ S, ((p : ℝ)⁻¹) := by
    simpa [S] using one_half_le_sum_primes_ge_one_div K
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hcutoff : ∀ p ∈ S, K ≤ p := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hnot : ¬ p < K := by
      intro hlt
      apply hp'.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hprime p hp⟩
    exact Nat.le_of_not_gt hnot
  exact ⟨S, hprime, hcutoff, hmass⟩

/- Every fixed shift of the reciprocal harmonic terms still has divergent partial sums. -/
theorem tendsto_shifted_reciprocal_sum_atTop (k : ℕ) :
    Tendsto (fun m : ℕ ↦
      ∑ i ∈ Finset.range m, (((i + k + 1 : ℕ) : ℝ)⁻¹)) atTop atTop := by
  have hh : Tendsto (fun n : ℕ ↦ (harmonic n : ℝ)) atTop atTop :=
    tendsto_harmonic_real_atTop
  have hadd : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, (((i + k + 1 : ℕ) : ℝ)⁻¹)) =
        (harmonic (m + k) : ℝ) - (harmonic k : ℝ) := by
    intro m
    have hdef : ∀ n : ℕ, (harmonic n : ℝ) =
        ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ)⁻¹) := by
      intro n
      rw [harmonic]
      norm_num
    rw [hdef, hdef]
    have hs := Finset.sum_range_add (f := fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) k m
    rw [Nat.add_comm k m] at hs
    have hsumEq : (∑ i ∈ Finset.range m, (((i + k + 1 : ℕ) : ℝ)⁻¹)) =
        ∑ x ∈ Finset.range m, (((k + x + 1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      simp [Nat.add_comm]
    rw [hsumEq, hs]
    ring
  rw [show (fun m : ℕ ↦
      ∑ i ∈ Finset.range m, (((i + k + 1 : ℕ) : ℝ)⁻¹)) =
      fun m ↦ (harmonic (m + k) : ℝ) - (harmonic k : ℝ) by
        funext m
        exact hadd m]
  have hshift := hh.comp (tendsto_add_atTop_nat k)
  simpa [Function.comp_def, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-(harmonic k : ℝ)) hshift)

theorem shifted_reciprocal_sum_eq_harmonic_sub (k m : ℕ) :
    (∑ i ∈ Finset.range m, (((i + k + 1 : ℕ) : ℝ)⁻¹)) =
      (harmonic (m + k) : ℝ) - (harmonic k : ℝ) := by
  have hdef : ∀ n : ℕ, (harmonic n : ℝ) =
      ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ)⁻¹) := by
    intro n
    rw [harmonic]
    norm_num
  rw [hdef, hdef]
  have hs := Finset.sum_range_add
    (f := fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) k m
  rw [Nat.add_comm k m] at hs
  have hsumEq : (∑ i ∈ Finset.range m, (((i + k + 1 : ℕ) : ℝ)⁻¹)) =
      ∑ x ∈ Finset.range m, (((k + x + 1 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    simp [Nat.add_comm]
  rw [hsumEq, hs]
  ring

/- A shifted reciprocal sum dominates a fixed positive multiple of `log (m+1)`.  The elementary
   denominator comparison `(K+i+1) ≤ (K+1)(i+1)` is enough; no asymptotic expansion is needed. -/
theorem shifted_reciprocal_sum_ge_inv_succ_mul_log (K m : ℕ) :
    (1 / (K + 1 : ℝ)) * Real.log ((m + 1 : ℕ) : ℝ) ≤
      ∑ i ∈ Finset.range m, (((K + i + 1 : ℕ) : ℝ)⁻¹) := by
  have hterm : ∀ i : ℕ,
      (1 / (K + 1 : ℝ)) * (((i + 1 : ℕ) : ℝ)⁻¹) ≤
        (((K + i + 1 : ℕ) : ℝ)⁻¹) := by
    intro i
    have hnat : K + i + 1 ≤ (K + 1) * (i + 1) := by
      nlinarith
    have hden : ((K + i + 1 : ℕ) : ℝ) ≤
        (((K + 1) * (i + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hpos : 0 < ((K + i + 1 : ℕ) : ℝ) := by positivity
    have hinv :
        (1 / (((K + 1) * (i + 1) : ℕ) : ℝ)) ≤
          (1 / ((K + i + 1 : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le hpos hden
    calc
      (1 / (K + 1 : ℝ)) * (((i + 1 : ℕ) : ℝ)⁻¹) =
          1 / (((K + 1) * (i + 1) : ℕ) : ℝ) := by
            push_cast
            field_simp
      _ ≤ 1 / ((K + i + 1 : ℕ) : ℝ) := hinv
      _ = (((K + i + 1 : ℕ) : ℝ)⁻¹) := by simp [one_div]
  have hsum :
      (1 / (K + 1 : ℝ)) *
          (∑ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ)⁻¹)) ≤
        ∑ i ∈ Finset.range m, (((K + i + 1 : ℕ) : ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi ↦ hterm i)
  have hharm :
      (∑ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ)⁻¹)) =
        (harmonic m : ℝ) := by
    rw [harmonic]
    norm_num
  have hlog : Real.log ((m + 1 : ℕ) : ℝ) ≤ (harmonic m : ℝ) := by
    exact log_add_one_le_harmonic m
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (1 / (K + 1 : ℝ)))
  rw [← hharm] at hmul
  exact hmul.trans hsum

/-- A finite reciprocal-prime sum is controlled by the von Mangoldt Mertens partial sum after
dividing by a common logarithmic lower bound.  This is the elementary bridge needed to avoid
losing a factor equal to the length of the exponential prime window. -/
theorem reciprocal_prime_sum_le_mertens
    {A : ℝ} {s : Finset ℕ} {N : ℕ}
    (hA : 0 < A) (hsubset : s ⊆ Finset.Icc 1 N)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ A ≤ Real.log (p : ℝ)) :
    (∑ p ∈ s, ((p : ℝ)⁻¹)) ≤
      PrimitiveSetsAboveX.mertensPartialSum N / A := by
  classical
  have hterm : ∀ p ∈ s,
      ((p : ℝ)⁻¹) ≤
        ArithmeticFunction.vonMangoldt p / (p : ℝ) / A := by
    intro p hp
    have hpPrime := (hs p hp).1
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hlog := (hs p hp).2
    have hmul : A * ((p : ℝ)⁻¹) ≤ Real.log (p : ℝ) * ((p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hpPos.le)
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
    apply (le_div_iff₀ hA).2
    calc
      (p : ℝ)⁻¹ * A = A * ((p : ℝ)⁻¹) := by ring
      _ ≤ Real.log (p : ℝ) * ((p : ℝ)⁻¹) := hmul
      _ = Real.log (p : ℝ) / (p : ℝ) := by ring
  calc
    (∑ p ∈ s, ((p : ℝ)⁻¹)) ≤
        ∑ p ∈ s, ArithmeticFunction.vonMangoldt p / (p : ℝ) / A := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p hp
    _ ≤ ∑ p ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt p / (p : ℝ) / A := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp _
      exact div_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)) hA.le
    _ = PrimitiveSetsAboveX.mertensPartialSum N / A := by
      unfold PrimitiveSetsAboveX.mertensPartialSum
      rw [Finset.sum_div]

/-- The strict lower endpoint in `primeWindow` only removes terms from the closed interval used by
`reciprocalPrimesBetween`. -/
theorem primeWindow_reciprocal_le_between (T a b : ℝ) :
    (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) ≤
      reciprocalPrimesBetween (Real.exp (Real.rpow T a))
        (Real.exp (Real.rpow T b)) := by
  classical
  unfold reciprocalPrimesBetween primeWindow
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
  · intro p hp _
    positivity

/-- The moving prime-window mass is bounded by the Mertens partial sum at its upper endpoint,
divided by the logarithmic lower endpoint. -/
theorem primeWindow_reciprocal_le_mertens
    {T a b : ℝ} (hT : 0 < T) :
    (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) ≤
      PrimitiveSetsAboveX.mertensPartialSum
          (Nat.floor (Real.exp (Real.rpow T b))) /
        Real.rpow T a := by
  have hA : 0 < Real.rpow T a := Real.rpow_pos_of_pos hT _
  apply (reciprocal_prime_sum_le_mertens hA ?_ ?_)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpPrime : Nat.Prime p := hp'.2.1
    have hpOne : 1 ≤ p := hpPrime.one_lt.le
    have hpUpper : p ≤ Nat.floor (Real.exp (Real.rpow T b)) :=
      (Finset.mem_Icc.mp hp'.1).2
    exact Finset.mem_Icc.mpr ⟨hpOne, hpUpper⟩
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpPrime : Nat.Prime p := hp'.2.1
    exact ⟨hpPrime, (primeWindow_log_bounds hp hpPrime.pos).1.le⟩

/- A finite lower bridge in the opposite direction.  Every prime in the window is at most the
upper endpoint, so its reciprocal is at least the reciprocal of that endpoint.  The analytic
prime-counting argument only has to supply a lower bound for `primeWindow.card`; no asymptotic
claim is hidden in this lemma. -/
theorem primeWindow_reciprocal_ge_card_div_upper
    {T a b : ℝ} (hupper : 0 < (Nat.floor (Real.exp (Real.rpow T b)) : ℝ)) :
    ((primeWindow T a b).card : ℝ) /
        (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) ≤
      ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
  classical
  let U : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  have hU : 0 < (U : ℝ) := by simpa [U] using hupper
  have hterm : ∀ p ∈ primeWindow T a b,
      (1 : ℝ) / (U : ℝ) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hIcc := Finset.mem_Icc.mp hp'.1
    have hpU : (p : ℝ) ≤ (U : ℝ) := by
      exact_mod_cast hIcc.2
    have hpPrime : Nat.Prime p := hp'.2.1
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    simpa [one_div] using (one_div_le_one_div_of_le hpPos hpU)
  calc
    ((primeWindow T a b).card : ℝ) / (U : ℝ) =
        ∑ p ∈ primeWindow T a b, (1 : ℝ) / (U : ℝ) := by
      simp [Finset.sum_const, div_eq_mul_inv]
    _ ≤ ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
      exact Finset.sum_le_sum (fun p hp ↦ hterm p hp)

/- The integer interval obtained by removing the lower floor is contained in the real-endpoint
window.  Consequently its prime count is bounded by the window cardinality.  This is the exact
floor/ceil interface needed before applying a quantitative lower bound for `π`. -/
theorem primeWindow_card_ge_primeCounting_sub
    {T a b : ℝ}
    (hLU : Nat.floor (Real.exp (Real.rpow T a)) ≤
      Nat.floor (Real.exp (Real.rpow T b))) :
    Nat.primeCounting (Nat.floor (Real.exp (Real.rpow T b))) ≤
      Nat.primeCounting (Nat.floor (Real.exp (Real.rpow T a))) +
        (primeWindow T a b).card := by
  classical
  let L : ℕ := Nat.floor (Real.exp (Real.rpow T a))
  let U : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  let S : Finset ℕ := (Finset.Icc (L + 1) U).filter Nat.Prime
  have hS_eq : S = Nat.primesLE U \ Nat.primesLE L := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hIcc := Finset.mem_Icc.mp hp'.1
      have hpPrime : Nat.Prime p := hp'.2
      have hpU : p ∈ Nat.primesLE U :=
        Nat.mem_primesLE.mpr ⟨hIcc.2, hpPrime⟩
      have hpnotL : p ∉ Nat.primesLE L := by
        intro hpL
        have hpL' := Nat.mem_primesLE.mp hpL
        omega
      exact Finset.mem_sdiff.mpr ⟨hpU, hpnotL⟩
    · intro hp
      have hp' := Finset.mem_sdiff.mp hp
      have hpU := Nat.mem_primesLE.mp hp'.1
      have hpPrime : Nat.Prime p := hpU.2
      have hpLow : L + 1 ≤ p := by
        have hpnotL := hp'.2
        have : ¬ p ≤ L := by
          intro hple
          apply hpnotL
          exact Nat.mem_primesLE.mpr ⟨hple, hpPrime⟩
        omega
      have hpIcc : p ∈ Finset.Icc (L + 1) U := Finset.mem_Icc.mpr ⟨hpLow, hpU.1⟩
      exact Finset.mem_filter.mpr ⟨hpIcc, hpPrime⟩
  have hSsub : S ⊆ primeWindow T a b := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hIcc := Finset.mem_Icc.mp hp'.1
    have hpPrime : Nat.Prime p := hp'.2
    have hAlow : Real.exp (Real.rpow T a) < (L : ℝ) + 1 := by
      simpa [L] using Nat.lt_floor_add_one (Real.exp (Real.rpow T a))
    have hpLowReal : Real.exp (Real.rpow T a) < (p : ℝ) := by
      exact hAlow.trans_le (by exact_mod_cast hIcc.1)
    have hceil : Nat.ceil (Real.exp (Real.rpow T a)) ≤ L + 1 := by
      simpa [L] using Nat.ceil_le_floor_add_one (Real.exp (Real.rpow T a))
    have hpCeil : Nat.ceil (Real.exp (Real.rpow T a)) ≤ p := hceil.trans hIcc.1
    have hpUpper : p ≤ Nat.floor (Real.exp (Real.rpow T b)) := by
      simpa [U] using hIcc.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpCeil, hpUpper⟩, ⟨hpPrime, hpLowReal⟩⟩
  have hcard : S.card ≤ (primeWindow T a b).card := Finset.card_le_card hSsub
  have hsub : Nat.primesLE L ⊆ Nat.primesLE U := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.1.trans hLU, hp'.2⟩
  have hdiff : S.card = Nat.primeCounting U - Nat.primeCounting L := by
    rw [hS_eq, Finset.card_sdiff]
    have hinter : Nat.primesLE L ∩ Nat.primesLE U = Nat.primesLE L :=
      Finset.inter_eq_left.mpr hsub
    rw [hinter, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hcount : Nat.primeCounting U - Nat.primeCounting L ≤
      (primeWindow T a b).card := by simpa [hdiff] using hcard
  have hcount' := (Nat.sub_le_iff_le_add').mp hcount
  simpa [L, U] using hcount'

/- A purely integer version of the reciprocal lower bridge.  It is convenient for partitioning a
large logarithmic window into finitely many blocks: each block contributes its prime-counting
increment divided by the block's upper endpoint. -/
theorem reciprocalPrimesNat_ge_primeCounting_sub_div
    (A B : ℕ) (hAB : A ≤ B) (hB : 0 < B) :
    ((Nat.primeCounting B - Nat.primeCounting A : ℕ) : ℝ) / (B : ℝ) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  classical
  let S : Finset ℕ := (Finset.Icc (A + 1) B).filter Nat.Prime
  have hS_eq : S = Nat.primesLE B \ Nat.primesLE A := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hIcc := Finset.mem_Icc.mp hp'.1
      have hpPrime : Nat.Prime p := hp'.2
      have hpB : p ∈ Nat.primesLE B := Nat.mem_primesLE.mpr ⟨hIcc.2, hpPrime⟩
      have hpnotA : p ∉ Nat.primesLE A := by
        intro hpA
        have hpA' := Nat.mem_primesLE.mp hpA
        omega
      exact Finset.mem_sdiff.mpr ⟨hpB, hpnotA⟩
    · intro hp
      have hp' := Finset.mem_sdiff.mp hp
      have hpB := Nat.mem_primesLE.mp hp'.1
      have hpPrime : Nat.Prime p := hpB.2
      have hpLow : A + 1 ≤ p := by
        have hpnotA := hp'.2
        have : ¬ p ≤ A := by
          intro hple
          apply hpnotA
          exact Nat.mem_primesLE.mpr ⟨hple, hpPrime⟩
        omega
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpLow, hpB.1⟩, hpPrime⟩
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.1.trans hAB, hp'.2⟩
  have hcard : S.card = Nat.primeCounting B - Nat.primeCounting A := by
    rw [hS_eq, Finset.card_sdiff]
    have hinter : Nat.primesLE A ∩ Nat.primesLE B = Nat.primesLE A :=
      Finset.inter_eq_left.mpr hsub
    rw [hinter, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hterm : ∀ p ∈ S, (1 : ℝ) / (B : ℝ) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hIcc := Finset.mem_Icc.mp hp'.1
    have hpPrime : Nat.Prime p := hp'.2
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpB : (p : ℝ) ≤ (B : ℝ) := by exact_mod_cast hIcc.2
    simpa [one_div] using (one_div_le_one_div_of_le hpPos hpB)
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  calc
    ((Nat.primeCounting B - Nat.primeCounting A : ℕ) : ℝ) / (B : ℝ) =
        (S.card : ℝ) / (B : ℝ) := by rw [hcard]
    _ = ∑ p ∈ S, (1 : ℝ) / (B : ℝ) := by
      simp [Finset.sum_const, div_eq_mul_inv]
    _ ≤ ∑ p ∈ S, ((p : ℝ)⁻¹) := by
      exact Finset.sum_le_sum (fun p hp ↦ hterm p hp)
    _ = ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := by
      rfl

/- A logarithmically weighted lower bridge.  It avoids a local prime-counting asymptotic: the
   Chebyshev theta difference is exactly the sum of `log p` on the interval, and each term is
   converted to a reciprocal weight using monotonicity of `x ↦ x log x`.  This is useful for the
   fixed-loss two-window route, where only divergence of the reciprocal mass is required. -/
theorem reciprocalPrimesNat_ge_theta_diff_div_log_upper
    (A B : ℕ) (hAB : A ≤ B) (_hA : 1 ≤ A) (hB : 2 ≤ B) :
    (Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ)) /
        ((B : ℝ) * Real.log (B : ℝ)) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  classical
  let S : Finset ℕ := (Finset.Icc (A + 1) B).filter Nat.Prime
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.1.trans hAB, hp'.2⟩
  have hS_eq : S = Nat.primesLE B \ Nat.primesLE A := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hIcc := Finset.mem_Icc.mp hp'.1
      have hpPrime : Nat.Prime p := hp'.2
      have hpB : p ∈ Nat.primesLE B := Nat.mem_primesLE.mpr ⟨hIcc.2, hpPrime⟩
      have hpnotA : p ∉ Nat.primesLE A := by
        intro hpA
        have hpA' := Nat.mem_primesLE.mp hpA
        omega
      exact Finset.mem_sdiff.mpr ⟨hpB, hpnotA⟩
    · intro hp
      have hp' := Finset.mem_sdiff.mp hp
      have hpB := Nat.mem_primesLE.mp hp'.1
      have hpPrime : Nat.Prime p := hpB.2
      have hpLow : A + 1 ≤ p := by
        have hpnotA := hp'.2
        have : ¬ p ≤ A := by
          intro hple
          apply hpnotA
          exact Nat.mem_primesLE.mpr ⟨hple, hpPrime⟩
        omega
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpLow, hpB.1⟩, hpPrime⟩
  have htheta : Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ) =
      ∑ p ∈ S, Real.log (p : ℝ) := by
    have hthetaB : Chebyshev.theta (B : ℝ) =
        ∑ p ∈ Nat.primesLE B, Real.log (p : ℝ) := by
      simpa using (Chebyshev.theta_eq_sum_primesLE_log B)
    have hthetaA : Chebyshev.theta (A : ℝ) =
        ∑ p ∈ Nat.primesLE A, Real.log (p : ℝ) := by
      simpa using (Chebyshev.theta_eq_sum_primesLE_log A)
    rw [hthetaB, hthetaA]
    rw [← Finset.sum_sdiff hsub]
    rw [hS_eq]
    abel
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hBone : 1 < B := by omega
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hBone)
  have hterm : ∀ p ∈ S, Real.log (p : ℝ) / ((B : ℝ) * Real.log (B : ℝ)) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpI := Finset.mem_Icc.mp hp'.1
    have hpPrime := hp'.2
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpB : (p : ℝ) ≤ (B : ℝ) := by exact_mod_cast hpI.2
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)
    have hlogmono : Real.log (p : ℝ) ≤ Real.log (B : ℝ) := Real.strictMonoOn_log.monotoneOn
      (show (p : ℝ) ∈ Set.Ioi 0 by exact hpPos)
      (show (B : ℝ) ∈ Set.Ioi 0 by exact hBpos) hpB
    have hprod : (p : ℝ) * Real.log (p : ℝ) ≤ (B : ℝ) * Real.log (B : ℝ) := by
      calc
        (p : ℝ) * Real.log (p : ℝ) ≤ (B : ℝ) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right hpB hlogp
        _ ≤ (B : ℝ) * Real.log (B : ℝ) :=
          mul_le_mul_of_nonneg_left hlogmono hBpos.le
    apply (div_le_iff₀ (mul_pos hBpos hlogB)).2
    have hquot : Real.log (p : ℝ) ≤
        ((B : ℝ) * Real.log (B : ℝ)) / (p : ℝ) := by
      apply (le_div_iff₀ hpPos).2
      simpa [mul_comm] using hprod
    simpa [one_div, div_eq_mul_inv, mul_comm] using hquot
  have hsum := Finset.sum_le_sum (fun p hp ↦ hterm p hp)
  have hdiv :
      (∑ p ∈ S, Real.log (p : ℝ)) / ((B : ℝ) * Real.log (B : ℝ)) ≤
        ∑ p ∈ S, ((p : ℝ)⁻¹) := by
    rw [Finset.sum_div]
    exact hsum
  rw [htheta]
  simpa [S] using hdiv

/- Explicit Chebyshev specialization of the theta bridge.  The lower endpoint is handled only by
   the elementary upper bound `theta_le_log4_mul_x`; no local PNT or interval asymptotic is hidden
   in this inequality. -/
theorem reciprocalPrimesNat_ge_theta_chebyshev
    (A B : ℕ) (hAB : A ≤ B) (hA : 1 ≤ A) (hB : 2 ≤ B) :
    ((B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1) -
        2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) -
        Real.log 4 * (A : ℝ)) /
        ((B : ℝ) * Real.log (B : ℝ)) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hbase := reciprocalPrimesNat_ge_theta_diff_div_log_upper A B hAB hA hB
  have hBtheta := Chebyshev.theta_ge B
  have hAtheta := Chebyshev.theta_le_log4_mul_x (x := (A : ℝ)) (by positivity)
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hBone : 1 < B := by omega
  have hdenpos : 0 < (B : ℝ) * Real.log (B : ℝ) :=
    mul_pos hBpos (Real.log_pos (by exact_mod_cast hBone))
  have hnum :
      (B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1) -
        2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) -
        Real.log 4 * (A : ℝ) ≤
        Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ) := by
    linarith
  exact (div_le_div_of_nonneg_right hnum hdenpos.le).trans hbase

/- A normalized form useful for geometric blocks.  The only extra hypothesis is a relative-error
   estimate for the explicit Chebyshev remainder; the conclusion has the clean main-term scale
   `(1 - η) * log 2 / log B`. -/
theorem reciprocalPrimesNat_ge_theta_chebyshev_of_relative_error
    (A B : ℕ) (hAB : A ≤ B) (hA : 1 ≤ A) (hB : 2 ≤ B)
    {η : ℝ}
    (herr : Real.log ((B : ℝ) + 1) +
        2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) +
        Real.log 4 * (A : ℝ) ≤ η * ((B : ℝ) * Real.log 2)) :
    (1 - η) * Real.log 2 / Real.log (B : ℝ) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hbase := reciprocalPrimesNat_ge_theta_chebyshev A B hAB hA hB
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hBone : 1 < B := by omega
  have hlogpos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hBone)
  have hdenpos : 0 < (B : ℝ) * Real.log (B : ℝ) := mul_pos hBpos hlogpos
  have hnum :
      (1 - η) * ((B : ℝ) * Real.log 2) ≤
        (B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1) -
          2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) - Real.log 4 * (A : ℝ) := by
    linarith
  have hdiv :
      ((1 - η) * ((B : ℝ) * Real.log 2)) /
          ((B : ℝ) * Real.log (B : ℝ)) ≤
        ((B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1) -
          2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) - Real.log 4 * (A : ℝ)) /
          ((B : ℝ) * Real.log (B : ℝ)) :=
    div_le_div_of_nonneg_right hnum hdenpos.le
  have hnorm :
      ((1 - η) * ((B : ℝ) * Real.log 2)) /
          ((B : ℝ) * Real.log (B : ℝ)) =
        (1 - η) * Real.log 2 / Real.log (B : ℝ) := by
    field_simp [ne_of_gt hBpos, ne_of_gt hlogpos]
  rw [← hnorm]
  exact hdiv.trans hbase

/- Summing the preceding block estimate over any finite monotone partition.  This is the exact
interface used by the moving-window argument: the analytic input only needs to provide lower
bounds for the prime-counting increments on each block.  No asymptotic estimate is built into
the statement. -/
theorem reciprocalPrimesNat_sum_ge_primeCounting_sub_div_sum
    (m : ℕ) (A : ℕ → ℕ)
    (hmono : ∀ i < m, A i ≤ A (i + 1))
    (hpos : ∀ i < m, 0 < A (i + 1)) :
    (∑ i ∈ Finset.range m,
      ((Nat.primeCounting (A (i + 1)) - Nat.primeCounting (A i) : ℕ) : ℝ) /
        (A (i + 1) : ℝ)) ≤
      ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  exact reciprocalPrimesNat_ge_primeCounting_sub_div
    (A i) (A (i + 1)) (hmono i hi') (hpos i hi')

/- A parameterised form which cleanly separates the analytic prime-counting input from the
elementary reciprocal conversion.  Supplying any lower bound for `π B` and upper bound for `π A`
immediately yields a reciprocal-prime lower bound. -/
theorem reciprocalPrimesNat_ge_of_primeCounting_bounds
    (A B : ℕ) (hAB : A ≤ B) (hB : 0 < B)
    {lower upper : ℝ}
    (hlower : lower ≤ (Nat.primeCounting B : ℝ))
    (hupper : (Nat.primeCounting A : ℝ) ≤ upper) :
    (lower - upper) / (B : ℝ) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hπ : Nat.primeCounting A ≤ Nat.primeCounting B :=
    Nat.monotone_primeCounting hAB
  have hcast :
      ((Nat.primeCounting B - Nat.primeCounting A : ℕ) : ℝ) =
        (Nat.primeCounting B : ℝ) - (Nat.primeCounting A : ℝ) := by
    exact (Nat.cast_sub (R := ℝ) hπ)
  have hnum : lower - upper ≤
      ((Nat.primeCounting B - Nat.primeCounting A : ℕ) : ℝ) := by
    rw [hcast]
    linarith
  have hden : 0 ≤ (B : ℝ) := by exact_mod_cast hB.le
  have hdiv : (lower - upper) / (B : ℝ) ≤
      ((Nat.primeCounting B - Nat.primeCounting A : ℕ) : ℝ) / (B : ℝ) :=
    div_le_div_of_nonneg_right hnum hden
  exact hdiv.trans (reciprocalPrimesNat_ge_primeCounting_sub_div A B hAB hB)

/- Concrete Chebyshev instantiation.  It is intentionally a finite estimate: it exposes the
explicit lower bound that must later be summed over multiplicative blocks, rather than asserting
the missing local-prime-number-theorem asymptotic. -/
theorem reciprocalPrimesNat_ge_chebyshev
    (A B : ℕ) (hA : 1 < A) (hAB : A ≤ B) :
    (((B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1)) / Real.log (B : ℝ) -
        (Real.log 4 * (A : ℝ) / Real.log (Real.sqrt (A : ℝ)) + Real.sqrt (A : ℝ))) /
        (B : ℝ) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hB : 0 < B := by omega
  apply reciprocalPrimesNat_ge_of_primeCounting_bounds A B hAB hB
  · exact Chebyshev.pi_ge B
  · have hAreal : 1 < (A : ℝ) := by exact_mod_cast hA
    have hupper := Chebyshev.pi_le_log4_mul_div (x := (A : ℝ)) hAreal
    simpa using hupper

/- The explicit Chebyshev remainder is asymptotically negligible on any endpoint family whose
   upper endpoint tends to infinity and whose lower/upper ratio tends to zero.  This is an
   elementary real-variable lemma; it does not use a local prime-number theorem. -/
theorem tendsto_theta_chebyshev_error_ratio_zero_of_vanishing_endpoint_ratio
    (A B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hAoverB : Tendsto (fun i : ℕ ↦ (A i : ℝ) / (B i : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun i : ℕ ↦
      (Real.log ((B i : ℝ) + 1) +
        2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) +
        Real.log 4 * (A i : ℝ)) /
        ((B i : ℝ) * Real.log 2)) atTop (𝓝 0) := by
  have hBreal : Tendsto (fun i : ℕ ↦ (B i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hB
  have hlogdiv : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogdivB : Tendsto (fun i : ℕ ↦ Real.log (B i : ℝ) / (B i : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlogdiv.comp hBreal
  have hlogdiffNat := Real.tendsto_log_nat_add_one_sub_log.comp hB
  have hBinv : Tendsto (fun i : ℕ ↦ (B i : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hBreal
  have hlogdiffdiv : Tendsto (fun i : ℕ ↦
      (Real.log ((B i : ℝ) + 1) - Real.log (B i : ℝ)) / (B i : ℝ)) atTop (𝓝 0) := by
    have hmul := hlogdiffNat.mul hBinv
    simpa [div_eq_mul_inv] using hmul
  have hlogplus : Tendsto (fun i : ℕ ↦
      Real.log ((B i : ℝ) + 1) / (B i : ℝ)) atTop (𝓝 0) := by
    have hadd := hlogdiffdiv.add hlogdivB
    have hadd0 : Tendsto (fun i : ℕ ↦
        (Real.log ((B i : ℝ) + 1) - Real.log (B i : ℝ)) / (B i : ℝ) +
          Real.log (B i : ℝ) / (B i : ℝ)) atTop (𝓝 0) := by
      simpa using hadd
    refine hadd0.congr' ?_
    filter_upwards [] with i
    ring
  have hloglittle : Real.log =o[atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 2)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hlogdivsqrt : Tendsto (fun x : ℝ ↦
      Real.log x / x ^ ((1 : ℝ) / 2)) atTop (𝓝 0) :=
    hloglittle.tendsto_div_nhds_zero
  have hlogdivsqrtB : Tendsto (fun i : ℕ ↦
      Real.log (B i : ℝ) / (B i : ℝ) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlogdivsqrt.comp hBreal
  have hsqrtterm : Tendsto (fun i : ℕ ↦
      2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) /
        ((B i : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _i : ℕ ↦ (2 / Real.log 2 : ℝ)) atTop
        (𝓝 (2 / Real.log 2)) := tendsto_const_nhds
    have hmul := hconst.mul hlogdivsqrtB
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hBpos : ∀ᶠ i : ℕ in atTop, 0 < (B i : ℝ) := by
      filter_upwards [hB.eventually (eventually_ge_atTop (1 : ℕ))] with i hi
      exact_mod_cast (Nat.zero_lt_of_lt hi)
    have hmul0 : Tendsto (fun i : ℕ ↦ (2 / Real.log 2 : ℝ) *
        (Real.log (B i : ℝ) / (B i : ℝ) ^ ((1 : ℝ) / 2))) atTop (𝓝 0) := by
      simpa using hmul
    refine hmul0.congr' ?_
    filter_upwards [hBpos] with i hBi
    rw [Real.sqrt_eq_rpow]
    field_simp [hBi.ne', hlog2]
    have hpow : ((B i : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (B i : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBi.le]
      norm_num
    rw [hpow]
  have hAterm : Tendsto (fun i : ℕ ↦
      Real.log 4 * (A i : ℝ) / ((B i : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hconst : Tendsto (fun _i : ℕ ↦ (Real.log 4 / Real.log 2 : ℝ)) atTop
        (𝓝 (Real.log 4 / Real.log 2)) := tendsto_const_nhds
    have hmul := hconst.mul hAoverB
    have hmul0 : Tendsto (fun i : ℕ ↦ (Real.log 4 / Real.log 2 : ℝ) *
        ((A i : ℝ) / (B i : ℝ))) atTop (𝓝 0) := by
      simpa using hmul
    refine hmul0.congr' ?_
    filter_upwards [] with i
    field_simp [hlog2]
  have hdenom : Tendsto (fun i : ℕ ↦
      Real.log ((B i : ℝ) + 1) / ((B i : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hmul := hlogplus.mul
      (tendsto_const_nhds : Tendsto (fun _i : ℕ ↦ (1 / Real.log 2 : ℝ)) atTop _)
    have hmul0 : Tendsto (fun i : ℕ ↦
        Real.log ((B i : ℝ) + 1) / (B i : ℝ) * (1 / Real.log 2)) atTop (𝓝 0) := by
      simpa using hmul
    refine hmul0.congr' ?_
    filter_upwards [] with i
    field_simp [hlog2pos.ne']
  have hsum := hdenom.add hsqrtterm |>.add hAterm
  have hsum0 : Tendsto (fun i =>
      Real.log ((B i : ℝ) + 1) / ((B i : ℝ) * Real.log 2) +
        2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) /
          ((B i : ℝ) * Real.log 2) +
        Real.log 4 * (A i : ℝ) / ((B i : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    simpa using hsum
  refine hsum0.congr' ?_
  filter_upwards [] with i
  ring

/- General endpoint-ratio form.  The preceding zero-limit lemma is the special case ρ = 0;
   keeping the limit explicit is useful when a block family has a nonzero asymptotic endpoint
   ratio and one wants to budget the resulting Chebyshev loss quantitatively. -/
theorem tendsto_theta_chebyshev_error_ratio_of_endpoint_ratio
    (A B : ℕ → ℕ) {ρ : ℝ}
    (hB : Tendsto B atTop atTop)
    (hAoverB : Tendsto (fun i : ℕ ↦ (A i : ℝ) / (B i : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun i : ℕ ↦
      (Real.log ((B i : ℝ) + 1) +
        2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) +
        Real.log 4 * (A i : ℝ)) /
        ((B i : ℝ) * Real.log 2)) atTop
      (𝓝 ((Real.log 4 / Real.log 2) * ρ)) := by
  have hzeroAB : Tendsto (fun i : ℕ ↦ ((0 : ℕ) : ℝ) / (B i : ℝ)) atTop (𝓝 0) := by
    refine (tendsto_const_nhds : Tendsto (fun _i : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr' ?_
    filter_upwards [] with i
    simp
  have hzero := tendsto_theta_chebyshev_error_ratio_zero_of_vanishing_endpoint_ratio
    (fun _i : ℕ ↦ 0) B hB hzeroAB
  have hzero' : Tendsto (fun i : ℕ ↦
      (Real.log ((B i : ℝ) + 1) +
        2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ)) /
        ((B i : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    simpa using hzero
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hconst : Tendsto (fun _i : ℕ ↦ (Real.log 4 / Real.log 2 : ℝ)) atTop
      (𝓝 (Real.log 4 / Real.log 2)) := tendsto_const_nhds
  have hmul := hconst.mul hAoverB
  have hAterm : Tendsto (fun i : ℕ ↦
      Real.log 4 * (A i : ℝ) / ((B i : ℝ) * Real.log 2)) atTop
      (𝓝 ((Real.log 4 / Real.log 2) * ρ)) := by
    have hmul0 : Tendsto (fun i : ℕ ↦ (Real.log 4 / Real.log 2 : ℝ) *
        ((A i : ℝ) / (B i : ℝ))) atTop
        (𝓝 ((Real.log 4 / Real.log 2) * ρ)) := by
      simpa using hmul
    refine hmul0.congr' ?_
    filter_upwards [] with i
    field_simp [hlog2]
  have hsum := hzero'.add hAterm
  have hsum0 : Tendsto (fun i =>
      (Real.log ((B i : ℝ) + 1) +
        2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ)) /
          ((B i : ℝ) * Real.log 2) +
        Real.log 4 * (A i : ℝ) / ((B i : ℝ) * Real.log 2)) atTop
      (𝓝 ((Real.log 4 / Real.log 2) * ρ)) := by
    simpa using hsum
  refine hsum0.congr' ?_
  filter_upwards [] with i
  ring

/- If the limiting endpoint ratio is small enough, the previous limit gives the exact relative
   error inequality needed by the normalized block lower bound. -/
theorem eventually_theta_chebyshev_error_le_of_endpoint_ratio_lt
    (A B : ℕ → ℕ) {ρ η : ℝ}
    (hB : Tendsto B atTop atTop)
    (hAoverB : Tendsto (fun i : ℕ ↦ (A i : ℝ) / (B i : ℝ)) atTop (𝓝 ρ))
    (hη : (Real.log 4 / Real.log 2) * ρ < η) :
    ∀ᶠ i : ℕ in atTop,
      Real.log ((B i : ℝ) + 1) +
          2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) +
          Real.log 4 * (A i : ℝ) ≤
        η * ((B i : ℝ) * Real.log 2) := by
  have hratio := tendsto_theta_chebyshev_error_ratio_of_endpoint_ratio A B hB hAoverB
  have hηevent : ∀ᶠ i : ℕ in atTop, (Real.log ((B i : ℝ) + 1) +
      2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) + Real.log 4 * (A i : ℝ)) /
        ((B i : ℝ) * Real.log 2) < η :=
    hratio.eventually (eventually_lt_nhds hη)
  have hBtwo : ∀ᶠ i : ℕ in atTop, 2 ≤ B i :=
    hB.eventually (eventually_ge_atTop (2 : ℕ))
  filter_upwards [hηevent, hBtwo] with i hi hBi
  apply (div_le_iff₀ ?_).mp hi.le
  have hBpos : 0 < (B i : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hBi)
  exact mul_pos hBpos (Real.log_pos (by norm_num))

/- A concrete safe budget used by the fixed-loss route: endpoint ratio 1/16 leaves half of the
   main Chebyshev term after the explicit constants are accounted for. -/
theorem eventually_theta_chebyshev_error_le_of_endpoint_ratio_one_sixteenth
    (A B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hAoverB : Tendsto (fun i : ℕ ↦ (A i : ℝ) / (B i : ℝ)) atTop (𝓝 ((1 : ℝ) / 16))) :
    ∀ᶠ i : ℕ in atTop,
      Real.log ((B i : ℝ) + 1) +
          2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) +
          Real.log 4 * (A i : ℝ) ≤
        (1 / 2 : ℝ) * ((B i : ℝ) * Real.log 2) := by
  have hconst : (Real.log 4 / Real.log 2) * ((1 : ℝ) / 16) < (1 / 2 : ℝ) := by
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    field_simp [hlog2]
    norm_num
  exact eventually_theta_chebyshev_error_le_of_endpoint_ratio_lt A B hB hAoverB hconst

/- Combining the concrete error budget with the finite bridge yields a reusable eventual lower
   bound for a whole block family.  This is the first point at which a geometric endpoint-ratio
   hypothesis produces an actual reciprocal-prime contribution, rather than only an error estimate. -/
theorem eventually_reciprocalPrimesNat_ge_half_log2_div_log_of_endpoint_ratio_one_sixteenth
    (A B : ℕ → ℕ)
    (hAB : ∀ i : ℕ, A i ≤ B i)
    (hA : ∀ᶠ i : ℕ in atTop, 1 ≤ A i)
    (hB : Tendsto B atTop atTop)
    (hBtwo : ∀ᶠ i : ℕ in atTop, 2 ≤ B i)
    (hAoverB : Tendsto (fun i : ℕ ↦ (A i : ℝ) / (B i : ℝ)) atTop
      (𝓝 ((1 : ℝ) / 16))) :
    ∀ᶠ i : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log 2 / Real.log (B i : ℝ) ≤
        ∑ p ∈ (Finset.Icc (A i + 1) (B i)).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have herr := eventually_theta_chebyshev_error_le_of_endpoint_ratio_one_sixteenth
    A B hB hAoverB
  filter_upwards [hA, hBtwo, herr] with i hAi hBi hi
  have hmain := reciprocalPrimesNat_ge_theta_chebyshev_of_relative_error
    (A i) (B i) (hAB i) hAi hBi hi
  norm_num at hmain ⊢
  exact hmain

/- A canonical geometric block family.  The endpoints differ by four binary exponents, so their
   ratio is exactly 1/16; this makes the preceding relative-error theorem directly executable. -/
def dyadicLowerEndpoint (i : ℕ) : ℕ := 2 ^ i

def dyadicUpperEndpoint (i : ℕ) : ℕ := 2 ^ (i + 4)

theorem dyadicLowerEndpoint_le_upper (i : ℕ) :
    dyadicLowerEndpoint i ≤ dyadicUpperEndpoint i := by
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right i 4)

theorem tendsto_dyadicUpperEndpoint : Tendsto dyadicUpperEndpoint atTop atTop := by
  have hp : Tendsto (fun n : ℕ ↦ 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  change Tendsto (fun i : ℕ ↦ 2 ^ (i + 4)) atTop atTop
  simpa [Function.comp_def] using hp.comp (tendsto_add_atTop_nat 4)

theorem tendsto_dyadicEndpoint_ratio :
    Tendsto (fun i : ℕ ↦
      (dyadicLowerEndpoint i : ℝ) / (dyadicUpperEndpoint i : ℝ)) atTop
        (𝓝 ((1 : ℝ) / 16)) := by
  have hEq : ∀ i : ℕ, (dyadicLowerEndpoint i : ℝ) /
      (dyadicUpperEndpoint i : ℝ) = (1 : ℝ) / 16 := by
    intro i
    unfold dyadicLowerEndpoint dyadicUpperEndpoint
    norm_num [Nat.cast_pow, pow_add]
    field_simp
  refine (tendsto_const_nhds : Tendsto (fun _i : ℕ ↦ (1 : ℝ) / 16) atTop
      (𝓝 ((1 : ℝ) / 16))).congr' ?_
  filter_upwards [] with i
  exact (hEq i).symm

theorem eventually_reciprocalPrimesNat_ge_half_log2_div_log_dyadic :
    ∀ᶠ i : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicUpperEndpoint i : ℝ) ≤
        ∑ p ∈ (Finset.Icc (dyadicLowerEndpoint i + 1)
          (dyadicUpperEndpoint i)).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hAB : ∀ i : ℕ, dyadicLowerEndpoint i ≤ dyadicUpperEndpoint i :=
    dyadicLowerEndpoint_le_upper
  have hA : ∀ᶠ i : ℕ in atTop, 1 ≤ dyadicLowerEndpoint i := by
    filter_upwards [] with i
    unfold dyadicLowerEndpoint
    exact Nat.one_le_pow i 2 (by norm_num)
  have hBtwo : ∀ᶠ i : ℕ in atTop, 2 ≤ dyadicUpperEndpoint i := by
    filter_upwards [] with i
    unfold dyadicUpperEndpoint
    have hi : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by norm_num)
    norm_num [pow_add]
    nlinarith
  exact eventually_reciprocalPrimesNat_ge_half_log2_div_log_of_endpoint_ratio_one_sixteenth
    dyadicLowerEndpoint dyadicUpperEndpoint hAB hA tendsto_dyadicUpperEndpoint hBtwo
      tendsto_dyadicEndpoint_ratio

/- The normalized lower contributions of these dyadic blocks have divergent partial sums.  This
   turns the per-block estimate above into an explicit mass-divergence scale, with no PNT input. -/
theorem tendsto_dyadic_normalized_block_lower_sum_atTop :
    Tendsto (fun m : ℕ ↦
      ∑ i ∈ Finset.range m,
        (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicUpperEndpoint i : ℝ)) atTop atTop := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hterm : ∀ i : ℕ,
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicUpperEndpoint i : ℝ) =
        (1 / 2 : ℝ) * (((i + 3 + 1 : ℕ) : ℝ)⁻¹) := by
    intro i
    unfold dyadicUpperEndpoint
    rw [Nat.cast_pow, Real.log_pow]
    field_simp [hlog2]
    ring_nf
  have hsumEq : (fun m : ℕ ↦
      ∑ i ∈ Finset.range m,
        (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicUpperEndpoint i : ℝ)) =
      (fun m : ℕ ↦ (1 / 2 : ℝ) *
        (∑ i ∈ Finset.range m, (((i + 3 + 1 : ℕ) : ℝ)⁻¹))) := by
    funext m
    simp_rw [hterm]
    rw [← Finset.mul_sum]
  rw [hsumEq]
  simpa [mul_comm] using (tendsto_shifted_reciprocal_sum_atTop 3).atTop_mul_const
    (show (0 : ℝ) < 1 / 2 by norm_num)

/- Consequently the reciprocal mass of the actual dyadic prime blocks diverges.  The only prime
   input here is the finite Chebyshev bridge; eventual termwise domination transfers the harmonic
   divergence through the generic summation lemma in `UnionBound`. -/
theorem tendsto_dyadic_reciprocal_block_mass_sum_atTop :
    Tendsto (fun m : ℕ ↦
      ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (dyadicLowerEndpoint i + 1)
          (dyadicUpperEndpoint i)).filter Nat.Prime, ((p : ℝ)⁻¹)) atTop atTop := by
  let u : ℕ → ℝ := fun i ↦
    ∑ p ∈ (Finset.Icc (dyadicLowerEndpoint i + 1)
      (dyadicUpperEndpoint i)).filter Nat.Prime, ((p : ℝ)⁻¹)
  let v : ℕ → ℝ := fun i ↦
    (1 / 2 : ℝ) * Real.log 2 /
      Real.log (dyadicUpperEndpoint i : ℝ)
  have hu : ∀ i : ℕ, 0 ≤ u i := by
    intro i
    dsimp [u]
    positivity
  have hlimv : Tendsto (fun m : ℕ ↦ ∑ i ∈ Finset.range m, v i) atTop atTop := by
    simpa [v] using tendsto_dyadic_normalized_block_lower_sum_atTop
  have hbound : ∀ᶠ i : ℕ in atTop, v i ≤ u i := by
    simpa [u, v] using eventually_reciprocalPrimesNat_ge_half_log2_div_log_dyadic
  have hlimu := tendsto_sum_atTop_of_eventually_ge_nonneg u v hu hlimv hbound
  simpa [u] using hlimu

/- A disjoint variant of the dyadic family.  The exponent gap is four at every step, so the
   integer prime blocks are adjacent rather than overlapping. -/
def dyadicDisjointLowerEndpoint (i : ℕ) : ℕ := 2 ^ (4 * i)

def dyadicDisjointUpperEndpoint (i : ℕ) : ℕ := 2 ^ (4 * (i + 1))

def dyadicDisjointPrimeBlock (i : ℕ) : Finset ℕ :=
  (Finset.Icc (dyadicDisjointLowerEndpoint i + 1)
    (dyadicDisjointUpperEndpoint i)).filter Nat.Prime

def dyadicDisjointPrimeFamily (m : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion dyadicDisjointPrimeBlock

theorem dyadicDisjointPrimeFamily_mono {m n : ℕ} (hmn : m ≤ n) :
    dyadicDisjointPrimeFamily m ⊆ dyadicDisjointPrimeFamily n := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i, ?_, hpi⟩
  exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hmn)

/- Every prime up to `Y` occurs in the dyadic family whose length is one more than the base-16
   logarithm of `Y`.  The strict lower endpoint is discharged using primality: a prime cannot be
   the even power `16^i` (and for `i=0` it cannot be `1`).  This finite cover is the bridge needed
   to turn blockwise prime-counting estimates into an arbitrary cutoff estimate. -/
theorem primesLE_subset_dyadicDisjointPrimeFamily_succ_log (Y : ℕ) :
    Nat.primesLE Y ⊆ dyadicDisjointPrimeFamily (Nat.log 16 Y + 1) := by
  intro p hp
  have hpdata := Nat.mem_primesLE.mp hp
  have hpprime : p.Prime := hpdata.2
  have hp2 : 2 ≤ p := hpprime.two_le
  have hp0 : p ≠ 0 := by omega
  have hi_le : Nat.log 16 p ≤ Nat.log 16 Y := Nat.log_mono_right hpdata.1
  let i := Nat.log 16 p
  have hi_mem : i ∈ Finset.range (Nat.log 16 Y + 1) := by
    dsimp [i]
    exact Finset.mem_range.mpr (by omega)
  have hlow16 : 16 ^ i ≤ p := by
    dsimp [i]
    exact Nat.pow_log_le_self 16 hp0
  have hupp16 : p < 16 ^ (i + 1) := by
    dsimp [i]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 16) p
  have hstrict : 16 ^ i < p := by
    by_contra hnot
    have heq : p = 16 ^ i := Nat.le_antisymm (le_of_not_gt hnot) hlow16
    by_cases hi0 : i = 0
    · have heq1 : p = 1 := by simpa [hi0] using heq
      exact hpprime.ne_one heq1
    · have hdiv : 2 ∣ 16 ^ i := dvd_pow (by norm_num : 2 ∣ 16) hi0
      have hmod : (16 ^ i) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      rcases hpprime.eq_two_or_odd with heven | hodd
      · have hpowge : 16 ≤ 16 ^ i := by
          rw [show i = 1 + (i - 1) by omega, pow_add]
          have hbase : 1 ≤ 16 ^ (i - 1) := Nat.one_le_pow _ _ (by norm_num)
          norm_num
          nlinarith
        rw [heq] at heven
        omega
      · rw [← heq] at hmod
        omega
  have hlow2 : 16 ^ i + 1 ≤ p := by omega
  have hIcc : p ∈ Finset.Icc (2 ^ (4 * i) + 1) (2 ^ (4 * (i + 1))) := by
    have hloweq : 2 ^ (4 * i) = 16 ^ i := by rw [pow_mul]; norm_num
    have hupeq : 2 ^ (4 * (i + 1)) = 16 ^ (i + 1) := by rw [pow_mul]; norm_num
    rw [hloweq, hupeq]
    exact Finset.mem_Icc.mpr ⟨hlow2, hupp16.le⟩
  unfold dyadicDisjointPrimeFamily
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi_mem, ?_⟩
  exact Finset.mem_filter.mpr ⟨hIcc, hpprime⟩

/- The dyadic endpoints can be chosen from the real logarithmic scale without any hidden
   floor/ceiling convention.  These two endpoint lemmas are the finite arithmetic interface used
   when embedding a moving dyadic tail into a report window. -/
theorem dyadicDisjointLowerEndpoint_ge_exp_rpow {T a : ℝ} :
    Real.exp (Real.rpow T a) ≤
      (dyadicDisjointLowerEndpoint
        (Nat.ceil (Real.rpow T a / (4 * Real.log 2))) : ℝ) := by
  let k : ℕ := Nat.ceil (Real.rpow T a / (4 * Real.log 2))
  have hden : 0 < (4 : ℝ) * Real.log 2 := by positivity
  have hceil : Real.rpow T a / (4 * Real.log 2) ≤ (k : ℝ) := by
    simpa [k] using (Nat.le_ceil (Real.rpow T a / (4 * Real.log 2)))
  have hpowlog : Real.rpow T a ≤ (4 * (k : ℝ)) * Real.log 2 := by
    have hmul := (div_le_iff₀ hden).mp hceil
    nlinarith
  have hpow : Real.exp (Real.rpow T a) ≤ (2 : ℝ) ^ (4 * k) := by
    apply Real.le_pow_of_log_le (by norm_num)
    rw [Real.log_exp]
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hpowlog
  simpa [k, dyadicDisjointLowerEndpoint] using hpow

theorem dyadicDisjointUpperEndpoint_le_exp_rpow {T b : ℝ} (hT : 0 < T)
    {K : ℕ} (hK : K + 1 ≤ Nat.floor (Real.rpow T b / (4 * Real.log 2))) :
    (dyadicDisjointUpperEndpoint K : ℝ) ≤ Real.exp (Real.rpow T b) := by
  have hden : 0 < (4 : ℝ) * Real.log 2 := by positivity
  have hfloor : (Nat.floor (Real.rpow T b / (4 * Real.log 2)) : ℝ) ≤
      Real.rpow T b / (4 * Real.log 2) :=
    Nat.floor_le (div_nonneg (Real.rpow_nonneg (le_of_lt hT) b) hden.le)
  have hKlog : (4 * ((K + 1 : ℕ) : ℝ)) * Real.log 2 ≤ Real.rpow T b := by
    have hKcast : ((K + 1 : ℕ) : ℝ) ≤
        (Nat.floor (Real.rpow T b / (4 * Real.log 2)) : ℝ) := by
      exact_mod_cast hK
    have hKcast' : ((K + 1 : ℕ) : ℝ) ≤
        Real.rpow T b / (4 * Real.log 2) := hKcast.trans hfloor
    simpa [mul_comm, mul_left_comm, mul_assoc] using ((le_div_iff₀ hden).mp hKcast')
  have hpow : (2 : ℝ) ^ (4 * (K + 1)) ≤ Real.exp (Real.rpow T b) := by
    apply (Real.pow_le_iff_le_log (by norm_num) (by positivity)).2
    rw [Real.log_exp]
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hKlog
  simpa [dyadicDisjointUpperEndpoint] using hpow

/- A shifted finite tail of the disjoint family.  The first block starts at index `k`, while
   `m` records the number of consecutive blocks retained.  This is the convenient finite model
   for a moving window whose lower endpoint is allowed to drift to infinity. -/
def dyadicDisjointPrimeTail (k m : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion (fun i ↦ dyadicDisjointPrimeBlock (i + k))

theorem tendsto_dyadicDisjointUpperEndpoint :
    Tendsto dyadicDisjointUpperEndpoint atTop atTop := by
  have hp : Tendsto (fun n : ℕ ↦ 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have he : Tendsto (fun i : ℕ ↦ 4 * (i + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop ((N + 3) / 4)] with i hi
    omega
  change Tendsto (fun i : ℕ ↦ 2 ^ (4 * (i + 1))) atTop atTop
  exact hp.comp he

theorem tendsto_dyadicDisjointEndpoint_ratio :
    Tendsto (fun i : ℕ ↦
      (dyadicDisjointLowerEndpoint i : ℝ) /
        (dyadicDisjointUpperEndpoint i : ℝ)) atTop
      (𝓝 ((1 : ℝ) / 16)) := by
  have hEq : ∀ i : ℕ,
      (dyadicDisjointLowerEndpoint i : ℝ) /
          (dyadicDisjointUpperEndpoint i : ℝ) = (1 : ℝ) / 16 := by
    intro i
    unfold dyadicDisjointLowerEndpoint dyadicDisjointUpperEndpoint
    rw [show 4 * (i + 1) = 4 * i + 4 by omega, pow_add]
    norm_num [Nat.cast_pow]
    field_simp
  refine (tendsto_const_nhds : Tendsto (fun _i : ℕ ↦ (1 : ℝ) / 16) atTop
      (𝓝 ((1 : ℝ) / 16))).congr' ?_
  filter_upwards [] with i
  exact (hEq i).symm

theorem eventually_dyadicDisjointPrimeBlock_lower :
    ∀ᶠ i : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint i : ℝ) ≤
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹) := by
  have hAB : ∀ i : ℕ,
      dyadicDisjointLowerEndpoint i ≤ dyadicDisjointUpperEndpoint i := by
    intro i
    unfold dyadicDisjointLowerEndpoint dyadicDisjointUpperEndpoint
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have hA : ∀ᶠ i : ℕ in atTop, 1 ≤ dyadicDisjointLowerEndpoint i := by
    filter_upwards [] with i
    unfold dyadicDisjointLowerEndpoint
    exact Nat.one_le_pow (4 * i) 2 (by norm_num)
  have hBtwo : ∀ᶠ i : ℕ in atTop, 2 ≤ dyadicDisjointUpperEndpoint i := by
    filter_upwards [] with i
    unfold dyadicDisjointUpperEndpoint
    have hi : 1 ≤ 2 ^ (4 * i) := Nat.one_le_pow (4 * i) 2 (by norm_num)
    rw [show 4 * (i + 1) = 4 * i + 4 by omega, pow_add]
    norm_num
    nlinarith
  exact eventually_reciprocalPrimesNat_ge_half_log2_div_log_of_endpoint_ratio_one_sixteenth
    dyadicDisjointLowerEndpoint dyadicDisjointUpperEndpoint hAB hA
      tendsto_dyadicDisjointUpperEndpoint hBtwo tendsto_dyadicDisjointEndpoint_ratio

/- The lower contribution of a disjoint block has the simple reciprocal-index form
   `1 / (8(i+1))`.  Exposing this identity is useful when the divergent block family is
   compared with the `log log X` scale required by the Erdős #878 lower construction. -/
theorem dyadicDisjointPrimeBlock_lower_explicit (i : ℕ) :
    (1 / 2 : ℝ) * Real.log 2 /
        Real.log (dyadicDisjointUpperEndpoint i : ℝ) =
      (1 / 8 : ℝ) / (i + 1 : ℝ) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold dyadicDisjointUpperEndpoint
  rw [Nat.cast_pow, Real.log_pow]
  field_simp [hlog2]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

theorem tendsto_dyadicDisjoint_normalized_block_lower_sum_atTop :
    Tendsto (fun m : ℕ ↦
      ∑ i ∈ Finset.range m,
        (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint i : ℝ)) atTop atTop := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hterm : ∀ i : ℕ,
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint i : ℝ) =
        (1 / 8 : ℝ) * (((i + 1 : ℕ) : ℝ)⁻¹) := by
    intro i
    unfold dyadicDisjointUpperEndpoint
    rw [Nat.cast_pow, Real.log_pow]
    norm_num [Nat.cast_mul, Nat.cast_add]
    have hipos : (0 : ℝ) < (i + 1 : ℕ) := by
      exact_mod_cast (Nat.zero_lt_succ i)
    field_simp [hlog2, hipos.ne']
    ring_nf
  have hsumEq : (fun m : ℕ ↦
      ∑ i ∈ Finset.range m,
        (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint i : ℝ)) =
      (fun m : ℕ ↦ (1 / 8 : ℝ) *
        (∑ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ)⁻¹))) := by
    funext m
    simp_rw [hterm]
    rw [← Finset.mul_sum]
  rw [hsumEq]
  simpa [mul_comm] using (tendsto_shifted_reciprocal_sum_atTop 0).atTop_mul_const
    (show (0 : ℝ) < 1 / 8 by norm_num)

theorem dyadicDisjointPrimeBlock_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (dyadicDisjointPrimeBlock i) (dyadicDisjointPrimeBlock j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hpiI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpi).1
  have hpjI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpj).1
  have hupper : dyadicDisjointUpperEndpoint i ≤
      dyadicDisjointLowerEndpoint j := by
    unfold dyadicDisjointUpperEndpoint dyadicDisjointLowerEndpoint
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  omega

theorem dyadicDisjointPrimeBlock_pairwiseDisjoint (m : ℕ) :
    (↑(Finset.range m) : Set ℕ).PairwiseDisjoint dyadicDisjointPrimeBlock := by
  intro i hi j hj hij
  change Disjoint (dyadicDisjointPrimeBlock i) (dyadicDisjointPrimeBlock j)
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · exact dyadicDisjointPrimeBlock_disjoint_of_lt hij'
  · exact (dyadicDisjointPrimeBlock_disjoint_of_lt hij').symm

theorem dyadicDisjointPrimeTail_pairwiseDisjoint (k m : ℕ) :
    (↑(Finset.range m) : Set ℕ).PairwiseDisjoint
      (fun i ↦ dyadicDisjointPrimeBlock (i + k)) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · exact dyadicDisjointPrimeBlock_disjoint_of_lt (Nat.add_lt_add_right hij' k)
  · exact (dyadicDisjointPrimeBlock_disjoint_of_lt (Nat.add_lt_add_right hij' k)).symm

theorem dyadicDisjointPrimeTail_mass_eq (k m : ℕ) :
    ∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹) =
      ∑ i ∈ Finset.range m,
        ∑ p ∈ dyadicDisjointPrimeBlock (i + k), ((p : ℝ)⁻¹) := by
  unfold dyadicDisjointPrimeTail
  rw [Finset.sum_biUnion (dyadicDisjointPrimeTail_pairwiseDisjoint k m)]

theorem dyadicDisjointPrimeTail_mass_ge_harmonic_sub (k m : ℕ)
    (hblock : ∀ j : ℕ, k ≤ j →
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint j : ℝ) ≤
        ∑ p ∈ dyadicDisjointPrimeBlock j, ((p : ℝ)⁻¹)) :
    (1 / 8 : ℝ) * ((harmonic (m + k) : ℝ) - (harmonic k : ℝ)) ≤
      ∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹) := by
  have hterm : ∀ i : ℕ,
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ) =
        (1 / 8 : ℝ) * (((i + k + 1 : ℕ) : ℝ)⁻¹) := by
    intro i
    unfold dyadicDisjointUpperEndpoint
    rw [Nat.cast_pow, Real.log_pow]
    norm_num [Nat.cast_mul, Nat.cast_add]
    have hipos : (0 : ℝ) < (i + k + 1 : ℕ) := by
      exact_mod_cast (Nat.zero_lt_succ (i + k))
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlog2, hipos.ne']
    ring_nf
  have hsum :
      (∑ i ∈ Finset.range m,
        (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ)) ≤
      ∑ i ∈ Finset.range m,
        ∑ p ∈ dyadicDisjointPrimeBlock (i + k), ((p : ℝ)⁻¹) := by
    apply Finset.sum_le_sum
    intro i hi
    apply hblock (i + k)
    omega
  have hscaled :
      (∑ i ∈ Finset.range m,
        (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ)) =
      (1 / 8 : ℝ) * ((harmonic (m + k) : ℝ) - (harmonic k : ℝ)) := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, shifted_reciprocal_sum_eq_harmonic_sub]
  calc
    (1 / 8 : ℝ) * ((harmonic (m + k) : ℝ) - (harmonic k : ℝ)) =
        ∑ i ∈ Finset.range m,
          (1 / 2 : ℝ) * Real.log 2 /
            Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ) := hscaled.symm
    _ ≤ ∑ i ∈ Finset.range m,
        ∑ p ∈ dyadicDisjointPrimeBlock (i + k), ((p : ℝ)⁻¹) := hsum
    _ = ∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹) :=
      (dyadicDisjointPrimeTail_mass_eq k m).symm

theorem eventually_dyadicDisjointPrimeTail_mass_ge_harmonic_sub :
    ∀ᶠ k : ℕ in atTop, ∀ m : ℕ,
      (1 / 8 : ℝ) * ((harmonic (m + k) : ℝ) - (harmonic k : ℝ)) ≤
        ∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹) := by
  rcases (eventually_atTop.1 eventually_dyadicDisjointPrimeBlock_lower) with ⟨K, hK⟩
  filter_upwards [eventually_ge_atTop K] with k hk m
  exact dyadicDisjointPrimeTail_mass_ge_harmonic_sub k m
    (fun j hj ↦ hK j (le_trans hk hj))

/- A concrete moving-tail choice.  Taking `m = k^2` makes the harmonic difference grow like
   `log k`, so the reciprocal mass still diverges even while the lower endpoint drifts outward. -/
theorem tendsto_dyadicDisjointPrimeTail_mass_square_atTop :
    Tendsto (fun k : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹)) atTop atTop := by
  have hlog : Tendsto (fun k : ℕ ↦ Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun k : ℕ ↦
      (1 / 8 : ℝ) * (Real.log (k : ℝ) - 1)) atTop atTop := by
    have hshift := tendsto_atTop_add_const_right atTop (-1 : ℝ) hlog
    simpa [sub_eq_add_neg, mul_comm] using hshift.atTop_mul_const
      (show (0 : ℝ) < 1 / 8 by norm_num)
  have hdiff : ∀ᶠ k : ℕ in atTop, Real.log (k : ℝ) - 1 ≤
      (harmonic (k * k + k) : ℝ) - (harmonic k : ℝ) := by
    have hkone : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
    have hlogpow : ∀ᶠ k : ℕ in atTop,
        2 * Real.log (k : ℝ) ≤ Real.log ((k * k + k + 1 : ℕ) : ℝ) := by
      filter_upwards [hkone] with k hk
      have hsqNat : k ^ 2 ≤ k * k + k + 1 := by
        simpa [pow_two] using (show k * k ≤ k * k + k + 1 by omega)
      have hsq : (k : ℝ) ^ 2 ≤ ((k * k + k + 1 : ℕ) : ℝ) := by
        exact_mod_cast hsqNat
      have hlog := Real.log_le_log (by positivity : 0 < (k : ℝ) ^ 2) hsq
      simpa [Real.log_pow] using hlog
    filter_upwards [hkone, hlogpow] with k hk hlogpow
    have hlogadd := log_add_one_le_harmonic (k * k + k)
    have hupp := harmonic_le_one_add_log k
    have hlogadd' : Real.log ((k * k + k + 1 : ℕ) : ℝ) ≤
        (harmonic (k * k + k) : ℝ) := by
      simpa using hlogadd
    linarith
  have hbound : ∀ᶠ k : ℕ in atTop,
      (1 / 8 : ℝ) * (Real.log (k : ℝ) - 1) ≤
        ∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹) := by
    filter_upwards [eventually_dyadicDisjointPrimeTail_mass_ge_harmonic_sub, hdiff]
      with k hk hdiff
    calc
      (1 / 8 : ℝ) * (Real.log (k : ℝ) - 1) ≤
          (1 / 8 : ℝ) * ((harmonic (k * k + k) : ℝ) - (harmonic k : ℝ)) := by
        gcongr
      _ ≤ ∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹) :=
        hk (k * k)
  exact Filter.tendsto_atTop_mono' atTop hbound hbase

theorem tendsto_dyadicDisjointPrimeTail_mass_square_inv_zero :
    Tendsto (fun k : ℕ ↦
      (∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) :=
  (tendsto_dyadicDisjointPrimeTail_mass_square_atTop).inv_tendsto_atTop

theorem dyadicDisjointPrimeTail_prime (k m : ℕ) {p : ℕ}
    (hp : p ∈ dyadicDisjointPrimeTail k m) : p.Prime := by
  unfold dyadicDisjointPrimeTail at hp
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  exact (Finset.mem_filter.mp hpi).2

theorem dyadicDisjointPrimeTail_subset_Icc (k m : ℕ) :
    dyadicDisjointPrimeTail k m ⊆
      Finset.Icc 1 (dyadicDisjointUpperEndpoint (k + m)) := by
  intro p hp
  unfold dyadicDisjointPrimeTail at hp
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  have hi_lt : i < m := Finset.mem_range.mp hi
  have hpiI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpi).1
  have hlow : 1 ≤ p := by
    have hpow : 1 ≤ dyadicDisjointLowerEndpoint (i + k) := by
      unfold dyadicDisjointLowerEndpoint
      exact Nat.one_le_pow (4 * (i + k)) 2 (by norm_num)
    omega
  have huple : dyadicDisjointUpperEndpoint (i + k) ≤
      dyadicDisjointUpperEndpoint (k + m) := by
    unfold dyadicDisjointUpperEndpoint
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  exact Finset.mem_Icc.mpr ⟨hlow, hpiI.2.trans huple⟩

/- Finite endpoint transfer into the report's real logarithmic window.  The hypotheses deliberately
   expose only the two endpoint inequalities; all floor/ceiling and strict-lower-endpoint details
   are discharged here. -/
theorem dyadicDisjointPrimeTail_subset_primeWindow_of_endpoint_bounds
    {T a b : ℝ} {k m : ℕ}
    (hlow : Real.exp (Real.rpow T a) ≤
      (dyadicDisjointLowerEndpoint k : ℝ))
    (hupp : (dyadicDisjointUpperEndpoint (k + m) : ℝ) ≤
      Real.exp (Real.rpow T b)) :
    dyadicDisjointPrimeTail k m ⊆ primeWindow T a b := by
  intro p hp
  unfold dyadicDisjointPrimeTail at hp
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  have hi_lt : i < m := Finset.mem_range.mp hi
  have hpiI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpi).1
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpi).2
  have hlowEndpoint : dyadicDisjointLowerEndpoint k ≤
      dyadicDisjointLowerEndpoint (i + k) := by
    unfold dyadicDisjointLowerEndpoint
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have hstrictNat : dyadicDisjointLowerEndpoint (i + k) < p := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hpiI.1
  have hstrictReal : (dyadicDisjointLowerEndpoint (i + k) : ℝ) < (p : ℝ) := by
    exact_mod_cast hstrictNat
  have hlowReal : Real.exp (Real.rpow T a) < (p : ℝ) := by
    exact lt_of_le_of_lt (hlow.trans (by exact_mod_cast hlowEndpoint)) hstrictReal
  have hupperEndpoint : dyadicDisjointUpperEndpoint (i + k) ≤
      dyadicDisjointUpperEndpoint (k + m) := by
    unfold dyadicDisjointUpperEndpoint
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have hupperReal : (p : ℝ) ≤ Real.exp (Real.rpow T b) := by
    have hpUpperNat : p ≤ dyadicDisjointUpperEndpoint (i + k) := hpiI.2
    have hpUpperReal' : (p : ℝ) ≤
        (dyadicDisjointUpperEndpoint (k + m) : ℝ) := by
      exact_mod_cast (hpUpperNat.trans hupperEndpoint)
    exact hpUpperReal'.trans hupp
  have hceil : Nat.ceil (Real.exp (Real.rpow T a)) ≤ p := by
    apply Nat.ceil_le.mpr
    exact hlowReal.le
  have hfloor : p ≤ Nat.floor (Real.exp (Real.rpow T b)) :=
    Nat.le_floor hupperReal
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hceil, hfloor⟩, ⟨hpPrime, hlowReal⟩⟩

/- The preceding inclusion also transfers reciprocal mass.  This is the finite bridge used by
the shortened fixed-loss route: the dyadic tail supplies divergence, while the report window is
the family consumed by the bad-pair and divisor-count interfaces. -/
theorem dyadicDisjointPrimeTail_mass_le_primeWindow_of_endpoint_bounds
    {T a b : ℝ} {k m : ℕ}
    (hlow : Real.exp (Real.rpow T a) ≤
      (dyadicDisjointLowerEndpoint k : ℝ))
    (hupp : (dyadicDisjointUpperEndpoint (k + m) : ℝ) ≤
      Real.exp (Real.rpow T b)) :
    (∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹)) ≤
      ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
  have hsub := dyadicDisjointPrimeTail_subset_primeWindow_of_endpoint_bounds hlow hupp
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p hp _
  positivity

/- The square-length tail also satisfies the sharp divisor-count exceptional-ratio conclusion at
   its own moving endpoint.  This is a completely explicit cofinal moving-window test family. -/
theorem tendsto_dyadicDisjointPrimeTail_square_exceptionalRatio_zero :
    Tendsto (fun k : ℕ ↦
      ((((Finset.Icc 1 (dyadicDisjointUpperEndpoint (k + k * k))).filter
        (fun n ↦ divisorCount (dyadicDisjointPrimeTail k (k * k)) n <
          (∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (dyadicDisjointUpperEndpoint (k + k * k) : ℝ)) atTop (𝓝 0) := by
  have hindex : Tendsto (fun k : ℕ ↦ k + k * k) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    omega
  have hX : Tendsto (fun k : ℕ ↦
      dyadicDisjointUpperEndpoint (k + k * k)) atTop atTop := by
    exact tendsto_dyadicDisjointUpperEndpoint.comp hindex
  have hμ : ∀ᶠ k : ℕ in atTop,
      0 < ∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹) := by
    have h := (tendsto_dyadicDisjointPrimeTail_mass_square_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
    filter_upwards [h] with k hk
    exact hk
  exact tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc_scale
    (fun k ↦ dyadicDisjointPrimeTail k (k * k))
    (fun k ↦ dyadicDisjointUpperEndpoint (k + k * k))
    (fun k p hp ↦ dyadicDisjointPrimeTail_prime k (k * k) hp)
    (fun k ↦ dyadicDisjointPrimeTail_subset_Icc k (k * k))
    hX hμ tendsto_dyadicDisjointPrimeTail_mass_square_inv_zero

theorem tendsto_dyadicDisjointPrimeTail_mass_atTop (k : ℕ) :
    Tendsto (fun m : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹)) atTop atTop := by
  have hterm : ∀ i : ℕ,
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ) =
        (1 / 8 : ℝ) * (((i + k + 1 : ℕ) : ℝ)⁻¹) := by
    intro i
    unfold dyadicDisjointUpperEndpoint
    rw [Nat.cast_pow, Real.log_pow]
    norm_num [Nat.cast_mul, Nat.cast_add]
    have hipos : (0 : ℝ) < (i + k + 1 : ℕ) := by
      exact_mod_cast (Nat.zero_lt_succ (i + k))
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlog2, hipos.ne']
    ring_nf
  have hlimv : Tendsto (fun m : ℕ ↦
      ∑ i ∈ Finset.range m,
        (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ)) atTop atTop := by
    have hshift := tendsto_shifted_reciprocal_sum_atTop k
    have hscaled := hshift.atTop_mul_const
      (show (0 : ℝ) < 1 / 8 by norm_num)
    have hEq : (fun m : ℕ ↦
        ∑ i ∈ Finset.range m,
          (1 / 2 : ℝ) * Real.log 2 /
            Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ)) =
        (fun m : ℕ ↦ (1 / 8 : ℝ) *
          (∑ i ∈ Finset.range m, (((i + k + 1 : ℕ) : ℝ)⁻¹))) := by
      funext m
      simp_rw [hterm]
      rw [← Finset.mul_sum]
    rw [hEq]
    simpa [mul_comm] using hscaled
  have hbound : ∀ᶠ i : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log 2 /
          Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ) ≤
        ∑ p ∈ dyadicDisjointPrimeBlock (i + k), ((p : ℝ)⁻¹) := by
    exact (tendsto_add_atTop_nat k).eventually
      eventually_dyadicDisjointPrimeBlock_lower
  have hu : ∀ i : ℕ, 0 ≤
      ∑ p ∈ dyadicDisjointPrimeBlock (i + k), ((p : ℝ)⁻¹) := by
    intro i
    positivity
  have hsum := tendsto_sum_atTop_of_eventually_ge_nonneg
    (fun i ↦ ∑ p ∈ dyadicDisjointPrimeBlock (i + k), ((p : ℝ)⁻¹))
    (fun i ↦ (1 / 2 : ℝ) * Real.log 2 /
      Real.log (dyadicDisjointUpperEndpoint (i + k) : ℝ)) hu hlimv hbound
  rw [show (fun m : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹)) =
      (fun m : ℕ ↦ ∑ i ∈ Finset.range m,
        ∑ p ∈ dyadicDisjointPrimeBlock (i + k), ((p : ℝ)⁻¹)) by
        funext m
        exact dyadicDisjointPrimeTail_mass_eq k m]
  exact hsum

theorem tendsto_dyadicDisjointPrimeTail_exceptionalRatio_zero (k : ℕ) :
    Tendsto (fun m : ℕ ↦
      ((((Finset.Icc 1 (dyadicDisjointUpperEndpoint (k + m))).filter
        (fun n ↦ divisorCount (dyadicDisjointPrimeTail k m) n <
          (∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (dyadicDisjointUpperEndpoint (k + m) : ℝ)) atTop (𝓝 0) := by
  have hX : Tendsto (fun m : ℕ ↦ dyadicDisjointUpperEndpoint (k + m)) atTop atTop := by
    simpa [Function.comp_def, Nat.add_comm] using
      tendsto_dyadicDisjointUpperEndpoint.comp (tendsto_add_atTop_nat k)
  have hμ : ∀ᶠ m : ℕ in atTop,
      0 < ∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹) := by
    have h := (tendsto_dyadicDisjointPrimeTail_mass_atTop k).eventually
      (eventually_gt_atTop (0 : ℝ))
    filter_upwards [h] with m hm
    exact hm
  have hinvμ : Tendsto (fun m : ℕ ↦
      (∑ p ∈ dyadicDisjointPrimeTail k m, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) :=
    (tendsto_dyadicDisjointPrimeTail_mass_atTop k).inv_tendsto_atTop
  exact tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc_scale
    (fun m ↦ dyadicDisjointPrimeTail k m)
    (fun m ↦ dyadicDisjointUpperEndpoint (k + m))
    (fun m p hp ↦ dyadicDisjointPrimeTail_prime k m hp)
    (fun m ↦ dyadicDisjointPrimeTail_subset_Icc k m)
    hX hμ hinvμ

theorem dyadicDisjointPrimeFamily_mass_eq (m : ℕ) :
    ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹) =
      ∑ i ∈ Finset.range m,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹) := by
  unfold dyadicDisjointPrimeFamily
  rw [Finset.sum_biUnion (dyadicDisjointPrimeBlock_pairwiseDisjoint m)]

/- Summing the eventual block lower bound from its threshold onward gives a finite shifted
   harmonic lower bound for the disjoint family.  Keeping the shift explicit avoids any hidden
   asymptotic cancellation and is the form needed by a moving density-one construction. -/
theorem eventually_dyadicDisjointPrimeFamily_mass_ge_shifted_reciprocal :
    ∃ K : ℕ, ∀ᶠ m : ℕ in atTop,
      (1 / 8 : ℝ) *
          (∑ i ∈ Finset.range (m - K), (((K + i + 1 : ℕ) : ℝ)⁻¹)) ≤
        ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹) := by
  rcases (eventually_atTop.1 eventually_dyadicDisjointPrimeBlock_lower) with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop K] with m hm
  rw [dyadicDisjointPrimeFamily_mass_eq]
  rw [← Finset.sum_range_add_sum_Ico _ hm]
  have htail :
      (∑ i ∈ Finset.Ico K m,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≥
        (1 / 8 : ℝ) *
          (∑ i ∈ Finset.range (m - K), (((K + i + 1 : ℕ) : ℝ)⁻¹)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiK : K ≤ K + i := by omega
    have him : K + i < m := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hblock := hK (K + i) hiK
    have hblock' :
        (1 / 8 : ℝ) / (K + i + 1 : ℝ) ≤
          ∑ p ∈ dyadicDisjointPrimeBlock (K + i), ((p : ℝ)⁻¹) := by
      have hb := hblock
      rw [dyadicDisjointPrimeBlock_lower_explicit (K + i)] at hb
      convert hb using 1
      norm_num [Nat.cast_add, Nat.cast_one]
    simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using hblock'
  have hhead :
      0 ≤ ∑ i ∈ Finset.range K,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹) := by
    positivity
  linarith

/- The shifted lower bound implies a logarithmic growth rate for the finite disjoint family.
   The constant depends only on the finitely many initial blocks discarded by the eventual
   Chebyshev estimate, which is sufficient for a positive-scale lower certificate. -/
theorem eventually_dyadicDisjointPrimeFamily_mass_ge_log :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c * Real.log ((m + 1 : ℕ) : ℝ) ≤
        ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹) := by
  rcases eventually_dyadicDisjointPrimeFamily_mass_ge_shifted_reciprocal with
    ⟨K, hshift⟩
  let c : ℝ := 1 / (16 * (K + 1 : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogAtTop : Tendsto (fun m : ℕ ↦ Real.log ((m + 1 : ℕ) : ℝ)) atTop atTop := by
    have hnat : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact Real.tendsto_log_atTop.comp hnat
  have hlarge : ∀ᶠ m : ℕ in atTop,
      K ≤ m ∧ 2 * K ≤ m ∧
        2 * Real.log (2 : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 * K),
      hlogAtTop.eventually (eventually_ge_atTop (2 * Real.log (2 : ℝ)))] with m hm hlog
    exact ⟨by omega, hm, hlog⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hshift, hlarge] with m hsm hm
  have hlogshift := shifted_reciprocal_sum_ge_inv_succ_mul_log K (m - K)
  have hlogmono :
      Real.log (((m + 1 : ℕ) : ℝ) / 2) ≤
        Real.log ((m - K + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · positivity
    · have hdenNat : m + 1 ≤ 2 * (m - K + 1) := by omega
      have hden : ((m + 1 : ℕ) : ℝ) ≤
          2 * ((m - K + 1 : ℕ) : ℝ) := by
        exact_mod_cast hdenNat
      nlinarith
  have hlogdiv :
      Real.log (((m + 1 : ℕ) : ℝ) / 2) =
        Real.log ((m + 1 : ℕ) : ℝ) - Real.log (2 : ℝ) := by
    rw [Real.log_div (by positivity) (by norm_num)]
  have hhalf :
      (1 / 2 : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) ≤
        Real.log ((m - K + 1 : ℕ) : ℝ) := by
    have hhalf' :
        (1 / 2 : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) ≤
          Real.log (((m + 1 : ℕ) : ℝ) / 2) := by
      rw [hlogdiv]
      nlinarith [hm.2.2]
    exact hhalf'.trans hlogmono
  have hmass' :
      (1 / 8 : ℝ) * (1 / (K + 1 : ℝ)) *
          Real.log ((m - K + 1 : ℕ) : ℝ) ≤
        ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹) := by
    calc
      (1 / 8 : ℝ) * (1 / (K + 1 : ℝ)) *
          Real.log ((m - K + 1 : ℕ) : ℝ) ≤
          (1 / 8 : ℝ) *
            (∑ i ∈ Finset.range (m - K), (((K + i + 1 : ℕ) : ℝ)⁻¹)) := by
        have hmul := mul_le_mul_of_nonneg_left hlogshift
          (by norm_num : (0 : ℝ) ≤ 1 / 8)
        nlinarith [hmul]
      _ ≤ ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹) := hsm
  have hcoef : 0 ≤ (1 / 8 : ℝ) * (1 / (K + 1 : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hhalf hcoef
  change (1 / (16 * (K + 1 : ℝ))) * Real.log ((m + 1 : ℕ) : ℝ) ≤
    ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹)
  calc
    (1 / (16 * (K + 1 : ℝ))) * Real.log ((m + 1 : ℕ) : ℝ) =
        (1 / 8 : ℝ) * (1 / (K + 1 : ℝ)) *
          ((1 / 2 : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) := by
            field_simp [show (K + 1 : ℝ) ≠ 0 by positivity]
            ring
    _ ≤ (1 / 8 : ℝ) * (1 / (K + 1 : ℝ)) *
          Real.log ((m - K + 1 : ℕ) : ℝ) := hscaled
    _ ≤ ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹) := hmass'
  

theorem tendsto_dyadicDisjointPrimeFamily_mass_atTop :
    Tendsto (fun m : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹)) atTop atTop := by
  have hu : ∀ i : ℕ, 0 ≤
      ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹) := by
    intro i
    positivity
  have hlimv : Tendsto (fun m : ℕ ↦ ∑ i ∈ Finset.range m,
      (1 / 2 : ℝ) * Real.log 2 /
        Real.log (dyadicDisjointUpperEndpoint i : ℝ)) atTop atTop :=
    tendsto_dyadicDisjoint_normalized_block_lower_sum_atTop
  have hbound : ∀ᶠ i : ℕ in atTop,
      (1 / 2 : ℝ) * Real.log 2 /
        Real.log (dyadicDisjointUpperEndpoint i : ℝ) ≤
      ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹) :=
    eventually_dyadicDisjointPrimeBlock_lower
  have hsum := tendsto_sum_atTop_of_eventually_ge_nonneg
    (fun i ↦ ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹))
    (fun i ↦ (1 / 2 : ℝ) * Real.log 2 /
      Real.log (dyadicDisjointUpperEndpoint i : ℝ)) hu hlimv hbound
  rw [show (fun m : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹)) =
      (fun m : ℕ ↦ ∑ i ∈ Finset.range m,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) by
        funext m
        exact dyadicDisjointPrimeFamily_mass_eq m]
  exact hsum

theorem tendsto_dyadicDisjointPrimeFamily_mass_inv_zero :
    Tendsto (fun m : ℕ ↦
      (∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) := by
  exact tendsto_dyadicDisjointPrimeFamily_mass_atTop.inv_tendsto_atTop

theorem dyadicDisjointPrimeFamily_prime (m : ℕ) {p : ℕ}
    (hp : p ∈ dyadicDisjointPrimeFamily m) : p.Prime := by
  unfold dyadicDisjointPrimeFamily at hp
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  exact (Finset.mem_filter.mp hpi).2

theorem dyadicDisjointPrimeFamily_subset_Icc (m : ℕ) :
    dyadicDisjointPrimeFamily m ⊆
      Finset.Icc 1 (dyadicDisjointUpperEndpoint m) := by
  intro p hp
  unfold dyadicDisjointPrimeFamily at hp
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  have hi_lt : i < m := Finset.mem_range.mp hi
  have hpiI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpi).1
  have hlow : 1 ≤ p := by
    have hpow : 1 ≤ dyadicDisjointLowerEndpoint i := by
      unfold dyadicDisjointLowerEndpoint
      exact Nat.one_le_pow (4 * i) 2 (by norm_num)
    omega
  have huple : dyadicDisjointUpperEndpoint i ≤
      dyadicDisjointUpperEndpoint m := by
    unfold dyadicDisjointUpperEndpoint
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  exact Finset.mem_Icc.mpr ⟨hlow, hpiI.2.trans huple⟩

/- The disjoint dyadic family now supplies a complete sharp exceptional-ratio conclusion at its
natural endpoint scale.  The remaining #878 work is to show that this particular family (or a
pair of compatible families) is the one required by the normal-order construction. -/
theorem tendsto_dyadicDisjointPrimeFamily_exceptionalRatio_zero :
    Tendsto (fun m : ℕ ↦
      ((((Finset.Icc 1 (dyadicDisjointUpperEndpoint m)).filter
        (fun n ↦ divisorCount (dyadicDisjointPrimeFamily m) n <
          (∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (dyadicDisjointUpperEndpoint m : ℝ)) atTop (𝓝 0) := by
  have hμ : ∀ᶠ m : ℕ in atTop,
      0 < ∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹) := by
    have h := tendsto_dyadicDisjointPrimeFamily_mass_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))
    filter_upwards [h] with m hm
    exact hm
  exact tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc_scale
    dyadicDisjointPrimeFamily dyadicDisjointUpperEndpoint
    (fun m p hp ↦ dyadicDisjointPrimeFamily_prime m hp)
    (fun m ↦ dyadicDisjointPrimeFamily_subset_Icc m)
    tendsto_dyadicDisjointUpperEndpoint hμ
    tendsto_dyadicDisjointPrimeFamily_mass_inv_zero

/- Eventual form of the preceding limit.  It supplies exactly the hypothesis consumed by the
   normalized block lower bound for every fixed positive error budget. -/
theorem eventually_theta_chebyshev_error_le_of_vanishing_endpoint_ratio
    (A B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hAoverB : Tendsto (fun i : ℕ ↦ (A i : ℝ) / (B i : ℝ)) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ i : ℕ in atTop,
      Real.log ((B i : ℝ) + 1) +
          2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) +
          Real.log 4 * (A i : ℝ) ≤
        η * ((B i : ℝ) * Real.log 2) := by
  have hratio := tendsto_theta_chebyshev_error_ratio_zero_of_vanishing_endpoint_ratio
    A B hB hAoverB
  have hηevent : ∀ᶠ i : ℕ in atTop, (Real.log ((B i : ℝ) + 1) +
      2 * Real.sqrt (B i : ℝ) * Real.log (B i : ℝ) + Real.log 4 * (A i : ℝ)) /
        ((B i : ℝ) * Real.log 2) ≤ η :=
    hratio.eventually (eventually_le_nhds hη)
  have hBtwo : ∀ᶠ i : ℕ in atTop, 2 ≤ B i :=
    hB.eventually (eventually_ge_atTop (2 : ℕ))
  filter_upwards [hηevent, hBtwo] with i hi hBi
  apply (div_le_iff₀ ?_).mp hi
  have hBpos : 0 < (B i : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hBi)
  exact mul_pos hBpos (Real.log_pos (by norm_num))

/- The completely explicit finite Chebyshev lower bounds can themselves be summed over a
monotone partition.  This is the strongest unconditional statement available here without a
separate local prime-number-theorem estimate. -/
theorem reciprocalPrimesNat_sum_ge_chebyshev
    (m : ℕ) (A : ℕ → ℕ)
    (hA : ∀ i < m, 1 < A i)
    (hmono : ∀ i < m, A i ≤ A (i + 1)) :
    (∑ i ∈ Finset.range m,
      (((A (i + 1) : ℝ) * Real.log 2 -
          Real.log ((A (i + 1) : ℝ) + 1)) /
          Real.log (A (i + 1) : ℝ) -
        (Real.log 4 * (A i : ℝ) / Real.log (Real.sqrt (A i : ℝ)) +
          Real.sqrt (A i : ℝ))) /
        (A (i + 1) : ℝ)) ≤
      ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  exact reciprocalPrimesNat_ge_chebyshev
    (A i) (A (i + 1)) (hA i hi') (hmono i hi')

/- The same finite block summation using the theta-weighted lower bound.  This form is often
   easier to feed into a hand-chosen geometric partition because the only analytic quantity is a
   theta endpoint difference, not a separate prime-counting lower and upper estimate. -/
theorem reciprocalPrimesNat_sum_ge_theta_chebyshev
    (m : ℕ) (A : ℕ → ℕ)
    (hA : ∀ i < m, 1 ≤ A i)
    (hmono : ∀ i < m, A i ≤ A (i + 1))
    (hB : ∀ i < m, 2 ≤ A (i + 1)) :
    (∑ i ∈ Finset.range m,
      (((A (i + 1) : ℝ) * Real.log 2 -
          Real.log ((A (i + 1) : ℝ) + 1) -
          2 * Real.sqrt (A (i + 1) : ℝ) * Real.log (A (i + 1) : ℝ) -
          Real.log 4 * (A i : ℝ)) /
        ((A (i + 1) : ℝ) * Real.log (A (i + 1) : ℝ)))) ≤
      ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  exact reciprocalPrimesNat_ge_theta_chebyshev
    (A i) (A (i + 1)) (hmono i hi') (hA i hi') (hB i hi')

/- A blockwise relative-error version.  The error rate may vary with the block, which is the
   natural form for a geometric partition whose endpoints grow with the index. -/
theorem reciprocalPrimesNat_sum_ge_sum_relative_error
    (m : ℕ) (A : ℕ → ℕ)
    (hA : ∀ i < m, 1 ≤ A i)
    (hmono : ∀ i < m, A i ≤ A (i + 1))
    (hB : ∀ i < m, 2 ≤ A (i + 1))
    (η : ℕ → ℝ)
    (herr : ∀ i < m,
      Real.log ((A (i + 1) : ℝ) + 1) +
          2 * Real.sqrt (A (i + 1) : ℝ) * Real.log (A (i + 1) : ℝ) +
          Real.log 4 * (A i : ℝ) ≤
        η i * ((A (i + 1) : ℝ) * Real.log 2)) :
    (∑ i ∈ Finset.range m,
      (1 - η i) * Real.log 2 / Real.log (A (i + 1) : ℝ)) ≤
      ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  exact reciprocalPrimesNat_ge_theta_chebyshev_of_relative_error
    (A i) (A (i + 1)) (hmono i hi') (hA i hi') (hB i hi') (herr i hi')

/- Floor/ceiling bookkeeping for the lower bridge: the integer prime interval just above the
lower floor is contained in the real-endpoint `primeWindow`. -/
theorem primeInterval_filter_prime_subset_primeWindow
    {T a b : ℝ} :
    (Finset.Icc (Nat.floor (Real.exp (Real.rpow T a)) + 1)
      (Nat.floor (Real.exp (Real.rpow T b)))).filter Nat.Prime ⊆
      primeWindow T a b := by
  intro p hp
  let L : ℕ := Nat.floor (Real.exp (Real.rpow T a))
  let U : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  have hp' := Finset.mem_filter.mp hp
  have hIcc := Finset.mem_Icc.mp hp'.1
  have hpPrime : Nat.Prime p := hp'.2
  have hAlow : Real.exp (Real.rpow T a) < (L : ℝ) + 1 := by
    simpa [L] using Nat.lt_floor_add_one (Real.exp (Real.rpow T a))
  have hpLowReal : Real.exp (Real.rpow T a) < (p : ℝ) := by
    exact hAlow.trans_le (by exact_mod_cast hIcc.1)
  have hceil : Nat.ceil (Real.exp (Real.rpow T a)) ≤ L + 1 := by
    simpa [L] using Nat.ceil_le_floor_add_one (Real.exp (Real.rpow T a))
  have hpCeil : Nat.ceil (Real.exp (Real.rpow T a)) ≤ p := hceil.trans hIcc.1
  have hpUpper : p ≤ Nat.floor (Real.exp (Real.rpow T b)) := by
    simpa [U] using hIcc.2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpCeil, hpUpper⟩, ⟨hpPrime, hpLowReal⟩⟩

/- The explicit Chebyshev block estimate now reaches the actual moving prime window.  Only the
finite floor/ceiling inclusion is used here; proving a useful asymptotic lower bound for this
quantity remains the analytic part of the project. -/
theorem primeWindow_reciprocal_ge_chebyshev
    {T a b : ℝ}
    (hAB : Nat.floor (Real.exp (Real.rpow T a)) ≤
      Nat.floor (Real.exp (Real.rpow T b)))
    (hA : 1 < Nat.floor (Real.exp (Real.rpow T a))) :
    let A : ℕ := Nat.floor (Real.exp (Real.rpow T a))
    let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
    (((B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1)) / Real.log (B : ℝ) -
        (Real.log 4 * (A : ℝ) / Real.log (Real.sqrt (A : ℝ)) + Real.sqrt (A : ℝ))) /
        (B : ℝ) ≤
      ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
  dsimp
  let A : ℕ := Nat.floor (Real.exp (Real.rpow T a))
  let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  have hbase := reciprocalPrimesNat_ge_chebyshev A B (by simpa [A] using hA)
    (by simpa [A, B] using hAB)
  have hsub := primeInterval_filter_prime_subset_primeWindow
    (T := T) (a := a) (b := b)
  calc
    (((B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1)) / Real.log (B : ℝ) -
        (Real.log 4 * (A : ℝ) / Real.log (Real.sqrt (A : ℝ)) + Real.sqrt (A : ℝ))) /
        (B : ℝ) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := hbase
    _ ≤ ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      positivity

/- The theta-weighted lower bridge specialized to a real-endpoint window.  This is the preferred
   finite interface for the fixed-loss route: only the endpoint inclusion and `theta` bounds are
   needed, while the local prime-counting asymptotic remains outside Lean. -/
theorem primeWindow_reciprocal_ge_theta_diff_div_log_upper
    {T a b : ℝ}
    (hAB : Nat.floor (Real.exp (Real.rpow T a)) ≤
      Nat.floor (Real.exp (Real.rpow T b)))
    (hA : 1 ≤ Nat.floor (Real.exp (Real.rpow T a)))
    (hB : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    let A : ℕ := Nat.floor (Real.exp (Real.rpow T a))
    let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
    (Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ)) /
        ((B : ℝ) * Real.log (B : ℝ)) ≤
      ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
  dsimp
  let A : ℕ := Nat.floor (Real.exp (Real.rpow T a))
  let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  have hbase := reciprocalPrimesNat_ge_theta_diff_div_log_upper A B
    (by simpa [A, B] using hAB) (by simpa [A] using hA) (by simpa [B] using hB)
  have hsub := primeInterval_filter_prime_subset_primeWindow
    (T := T) (a := a) (b := b)
  calc
    (Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ)) /
        ((B : ℝ) * Real.log (B : ℝ)) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := hbase
    _ ≤ ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      positivity

/- Explicit Chebyshev version at a real window.  The expression is intentionally left with the
   floor endpoints, so the later asymptotic proof can choose its own block partition and handle
   the floor errors explicitly. -/
theorem primeWindow_reciprocal_ge_theta_chebyshev
    {T a b : ℝ}
    (hAB : Nat.floor (Real.exp (Real.rpow T a)) ≤
      Nat.floor (Real.exp (Real.rpow T b)))
    (hA : 1 ≤ Nat.floor (Real.exp (Real.rpow T a)))
    (hB : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    let A : ℕ := Nat.floor (Real.exp (Real.rpow T a))
    let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
    ((B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1) -
        2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) -
        Real.log 4 * (A : ℝ)) /
        ((B : ℝ) * Real.log (B : ℝ)) ≤
      ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
  dsimp
  let A : ℕ := Nat.floor (Real.exp (Real.rpow T a))
  let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  have hbase := reciprocalPrimesNat_ge_theta_chebyshev A B
    (by simpa [A, B] using hAB) (by simpa [A] using hA) (by simpa [B] using hB)
  have hsub := primeInterval_filter_prime_subset_primeWindow
    (T := T) (a := a) (b := b)
  calc
    ((B : ℝ) * Real.log 2 - Real.log ((B : ℝ) + 1) -
        2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) -
        Real.log 4 * (A : ℝ)) /
        ((B : ℝ) * Real.log (B : ℝ)) ≤
      ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := hbase
    _ ≤ ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      positivity

/- Normalized real-window form.  The relative-error hypothesis is stated at the floor endpoints,
   so all rounding effects remain visible to the eventual analytic caller. -/
theorem primeWindow_reciprocal_ge_theta_chebyshev_of_relative_error
    {T a b : ℝ}
    (hAB : Nat.floor (Real.exp (Real.rpow T a)) ≤
      Nat.floor (Real.exp (Real.rpow T b)))
    (hA : 1 ≤ Nat.floor (Real.exp (Real.rpow T a)))
    (hB : 2 ≤ Nat.floor (Real.exp (Real.rpow T b)))
    {η : ℝ}
    (herr :
      Real.log ((Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + 1) +
          2 * Real.sqrt (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) *
            Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) +
          Real.log 4 * (Nat.floor (Real.exp (Real.rpow T a)) : ℝ) ≤
        η * ((Nat.floor (Real.exp (Real.rpow T b)) : ℝ) * Real.log 2)) :
    let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
    (1 - η) * Real.log 2 / Real.log (B : ℝ) ≤
      ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
  dsimp
  let A : ℕ := Nat.floor (Real.exp (Real.rpow T a))
  let B : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  have hbase := reciprocalPrimesNat_ge_theta_chebyshev_of_relative_error A B
    (by simpa [A, B] using hAB) (by simpa [A] using hA) (by simpa [B] using hB)
    (by simpa [A, B] using herr)
  have hsub := primeInterval_filter_prime_subset_primeWindow
    (T := T) (a := a) (b := b)
  calc
    (1 - η) * Real.log 2 / Real.log (B : ℝ) ≤
        ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, ((p : ℝ)⁻¹) := hbase
    _ ≤ ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      positivity

/- A convenient explicit form of the preceding estimate, using the bounded-error Mertens
estimate exported by `Upstream`.  The floor at the moving upper endpoint is retained so that
this lemma is purely formal and does not hide an asymptotic replacement. -/
theorem primeWindow_reciprocal_le_mertens_add_constant
    {T a b C : ℝ} (hT : 0 < T) (_hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) ≤
      (Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C) /
        Real.rpow T a := by
  have hbase := primeWindow_reciprocal_le_mertens (T := T) (a := a) (b := b) hT
  have hA : 0 < Real.rpow T a := Real.rpow_pos_of_pos hT _
  have hdiff :
      PrimitiveSetsAboveX.mertensPartialSum (Nat.floor (Real.exp (Real.rpow T b))) -
          Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) ≤ C := by
    exact le_trans (le_abs_self _) (hMertens hN)
  have hupper :
      PrimitiveSetsAboveX.mertensPartialSum (Nat.floor (Real.exp (Real.rpow T b))) ≤
        Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C := by
    linarith
  calc
    (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) ≤
        PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T b))) / Real.rpow T a := hbase
    _ ≤ (Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C) /
          Real.rpow T a := by
      exact div_le_div_of_nonneg_right hupper hA.le

/-- Unconditional wrapper around the LeanPool Mertens input.  The constant is existential because
the upstream theorem supplies bounded error without fixing a numerical value. -/
theorem primeWindow_reciprocal_le_mertens_default
    {T a b : ℝ} (hT : 0 < T)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    ∃ C : ℝ, 0 < C ∧
      (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) ≤
        (Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C) /
          Real.rpow T a := by
  obtain ⟨C, hC, hMertens⟩ := Upstream.vonMangoldt_mertens_bounded_error
  exact ⟨C, hC,
    primeWindow_reciprocal_le_mertens_add_constant hT hC hMertens hN⟩

/-- A floor-free form of the Mertens wrapper.  It is the convenient input for estimating the
moving window by powers of the main scale. -/
theorem primeWindow_reciprocal_le_rpow_add_constant
    {T a b C : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) ≤
      (Real.rpow T b + C) / Real.rpow T a := by
  have hbase := primeWindow_reciprocal_le_mertens_add_constant
    (T := T) (a := a) (b := b) hT hC hMertens hN
  have hNpos : 0 < (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hN)
  have hlog : Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) ≤ Real.rpow T b := by
    apply (Real.log_le_iff_le_exp hNpos).2
    exact Nat.floor_le (Real.exp_nonneg _)
  have hA : 0 < Real.rpow T a := Real.rpow_pos_of_pos hT _
  calc
    (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) ≤
        (Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C) /
          Real.rpow T a := hbase
    _ ≤ (Real.rpow T b + C) / Real.rpow T a := by
      exact div_le_div_of_nonneg_right (by simpa [add_comm] using add_le_add_right hlog C) hA.le

/-- The preceding power bound vanishes when the lower logarithmic exponent is larger than the
upper one.  This elementary asymptotic lemma is useful for checking parameter choices, although
the source problem deliberately has the opposite ordering in its prime windows. -/
theorem tendsto_rpow_add_div_rpow_zero
    {a b C : ℝ} (ha : 0 < a) (hab : b < a) :
    Tendsto (fun T : ℝ ↦ (T ^ b + C) / T ^ a) atTop (𝓝 0) := by
  have hratio : Tendsto (fun T : ℝ ↦ T ^ b / T ^ a) atTop (𝓝 0) := by
    have hneg : Tendsto (fun T : ℝ ↦ T ^ (-(a - b))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (sub_pos.mpr hab)
    apply hneg.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← Real.rpow_sub hT]
    congr 1
    ring
  have hden : Tendsto (fun T : ℝ ↦ T ^ a) atTop atTop := tendsto_rpow_atTop ha
  have hinv : Tendsto (fun T : ℝ ↦ (T ^ a)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
  have hconst : Tendsto (fun T : ℝ ↦ C / T ^ a) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
  have hsum : Tendsto (fun T : ℝ ↦ T ^ b / T ^ a + C / T ^ a) atTop (𝓝 0) := by
    simpa using hratio.add hconst
  exact Filter.Tendsto.congr'
    (f₁ := fun T : ℝ ↦ T ^ b / T ^ a + C / T ^ a)
    (f₂ := fun T : ℝ ↦ (T ^ b + C) / T ^ a) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      field_simp) hsum

/-- The reciprocal-width contribution factors out of the prime sum. -/
theorem sum_reciprocal_mul_const_eq
    (s : Finset ℕ) (c : ℝ) :
    (∑ p ∈ s, ((p : ℝ)⁻¹) * c) =
      c * (∑ p ∈ s, ((p : ℝ)⁻¹)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem badPairQWindow_reciprocal_le
    (T α β γ δ rho : ℝ) (M r h p : ℕ) :
    (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) ≤
      reciprocalPrimesBetween
        (Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) -
          Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))))
        (Real.exp (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) +
          Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)))) := by
  classical
  unfold reciprocalPrimesBetween
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have hqmem := Finset.mem_filter.mp hq
    have hqPrime := (Finset.mem_filter.mp hqmem.1).2.1
    exact Finset.mem_filter.mpr ⟨hqmem.2, hqPrime⟩
  · intro q hq _
    positivity

/-- On an interval starting at a positive `x`, reciprocal prime mass is at most the number of
primes divided by `x`. -/
theorem reciprocalPrimesBetween_le_count_div (x b : ℝ) (hx : 0 < x) :
    reciprocalPrimesBetween x b ≤ (BrunTitchmarsh.primesBetween x b : ℝ) / x := by
  classical
  let s := (Finset.Icc (Nat.ceil x) (Nat.floor b)).filter Nat.Prime
  have hterm : ∀ p ∈ s, ((p : ℝ)⁻¹) ≤ x⁻¹ := by
    intro p hp
    have hpIcc : p ∈ Finset.Icc (Nat.ceil x) (Nat.floor b) :=
      (Finset.mem_filter.mp hp).1
    have hceil : Nat.ceil x ≤ p := (Finset.mem_Icc.mp hpIcc).1
    have hxp : x ≤ (p : ℝ) :=
      (Nat.le_ceil x).trans (by exact_mod_cast hceil)
    simpa [one_div] using one_div_le_one_div_of_le hx hxp
  calc
    reciprocalPrimesBetween x b = ∑ p ∈ s, ((p : ℝ)⁻¹) := by
      rfl
    _ ≤ ∑ _p ∈ s, x⁻¹ := Finset.sum_le_sum fun p hp ↦ hterm p hp
    _ = (BrunTitchmarsh.primesBetween x b : ℝ) / x := by
      simp [s, BrunTitchmarsh.primesBetween, div_eq_mul_inv]

/-- LeanPool's explicit Brun–Titchmarsh estimate, converted into an explicit upper bound for
the reciprocal mass of primes in `[x, x + y]`. -/
theorem reciprocalPrimesBetween_le_brunTitchmarsh
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    reciprocalPrimesBetween x (x + y) ≤
      (2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3) / x := by
  calc
    reciprocalPrimesBetween x (x + y) ≤
        (BrunTitchmarsh.primesBetween x (x + y) : ℝ) / x :=
      reciprocalPrimesBetween_le_count_div x (x + y) hx
    _ ≤ (2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3) / x := by
      exact div_le_div_of_nonneg_right
        (Erdos878.Upstream.short_interval_prime_count x y z hx hy hz) hx.le

/- Endpoint form used by the short-prime intervals in Erdős's equation (26).  This is only a
   reparameterization of the preceding LeanPool Brun--Titchmarsh wrapper, but avoids repeatedly
   rebuilding the positive-width arithmetic when the interval is given as `(a,b)`. -/
theorem reciprocalPrimesBetween_le_brunTitchmarsh_of_endpoints
    (a b z : ℝ) (ha : 0 < a) (hab : a < b) (hz : 1 < z) :
    reciprocalPrimesBetween a b ≤
      (2 * (b - a) / Real.log z + 6 * z * (1 + Real.log z) ^ 3) / a := by
  have hy : 0 < b - a := sub_pos.mpr hab
  simpa [sub_add_cancel a b] using
    (reciprocalPrimesBetween_le_brunTitchmarsh a (b - a) z ha hy hz)

/- Direct source-shaped wrapper for the prime interval in equation (26).  The interval ordering
   is supplied explicitly because it is the only positivity needed by Brun--Titchmarsh; the
   separate range condition `2 ≤ r ≤ log X / log log X` belongs to the outer finite r-sum. -/
theorem reciprocalPrimesBetween_source_eq26_le_brunTitchmarsh
    (X r z : ℝ) (hX : 1 < X)
    (hll : 1 < Real.log (Real.log X))
    (hwindow : (X / Real.log (Real.log X)) ^ (1 / r) < X ^ (1 / 3))
    (hz : 1 < z) :
    reciprocalPrimesBetween ((X / Real.log (Real.log X)) ^ (1 / r)) (X ^ (1 / 3)) ≤
      (2 * (X ^ (1 / 3) - (X / Real.log (Real.log X)) ^ (1 / r)) / Real.log z +
        6 * z * (1 + Real.log z) ^ 3) /
        ((X / Real.log (Real.log X)) ^ (1 / r)) := by
  have hXpos : 0 < X := by linarith
  have hden : 0 < Real.log (Real.log X) := by linarith
  have ha : 0 < (X / Real.log (Real.log X)) ^ (1 / r) := by
    exact Real.rpow_pos_of_pos (div_pos hXpos hden) _
  exact reciprocalPrimesBetween_le_brunTitchmarsh_of_endpoints
    ((X / Real.log (Real.log X)) ^ (1 / r)) (X ^ (1 / 3)) z ha hwindow hz

/- The integer block `[2^(4i)+1, 2^(4(i+1))]` is contained in the corresponding real
   reciprocal-prime interval.  The one-point gap at the lower endpoint is harmless and is
   handled by monotonicity of finite nonnegative sums. -/
theorem dyadicDisjointPrimeBlock_mass_le_reciprocalBetween (i : ℕ) :
    (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      reciprocalPrimesBetween (dyadicDisjointLowerEndpoint i : ℝ)
        (dyadicDisjointUpperEndpoint i : ℝ) := by
  simp only [dyadicDisjointPrimeBlock, reciprocalPrimesBetween, Nat.ceil_natCast,
    Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpPrime := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨
      le_trans (Nat.le_add_right _ _) (Finset.mem_Icc.mp hpI).1,
      (Finset.mem_Icc.mp hpI).2⟩, hpPrime⟩
  · intro p hp _
    positivity

/- A dyadic specialization useful for the finite block decomposition of Theorem 7.
   Taking `z = √x` in Brun--Titchmarsh gives a reciprocal-prime budget on `[x,2x]`.
   The additive Selberg-sieve term is intentionally retained; summing these bounds over
   dyadic blocks is the remaining analytic step toward the `O(log log X)` estimate in (22). -/
theorem reciprocalPrimesBetween_dyadic_le_brun
    {x : ℝ} (hx : 4 < x) :
    reciprocalPrimesBetween x (2 * x) ≤
      (2 * x / Real.log (Real.sqrt x) +
        6 * Real.sqrt x * (1 + Real.log (Real.sqrt x)) ^ 3) / x := by
  have hxpos : 0 < x := by linarith
  have hsqrt : 1 < Real.sqrt x := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hraw := reciprocalPrimesBetween_le_brunTitchmarsh_of_endpoints
      x (2 * x) (Real.sqrt x) hxpos (by linarith) hsqrt
  convert hraw using 1
  all_goals ring

/- Applying the preceding estimate to the disjoint blocks used elsewhere in this file.  The
   restriction `1 ≤ i` avoids the small block with lower endpoint `1`, where `√x` is not a
   valid Brun parameter. -/
theorem dyadicDisjointPrimeBlock_mass_le_brun (i : ℕ) (hi : 1 ≤ i) :
    (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      (30 * (dyadicDisjointLowerEndpoint i : ℝ) /
          Real.log (Real.sqrt (dyadicDisjointLowerEndpoint i : ℝ)) +
        6 * Real.sqrt (dyadicDisjointLowerEndpoint i : ℝ) *
          (1 + Real.log (Real.sqrt (dyadicDisjointLowerEndpoint i : ℝ))) ^ 3) /
        (dyadicDisjointLowerEndpoint i : ℝ) := by
  let x : ℝ := (dyadicDisjointLowerEndpoint i : ℝ)
  have hx : 16 ≤ x := by
    dsimp [x, dyadicDisjointLowerEndpoint]
    have hi' : 4 ≤ 4 * i := by omega
    have hp : 2 ^ 4 ≤ 2 ^ (4 * i) :=
      Nat.pow_le_pow_right (by norm_num) hi'
    norm_num at hp ⊢
    exact_mod_cast hp
  have hxpos : 0 < x := by linarith
  have hsqrt : 1 < Real.sqrt x := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hmass := dyadicDisjointPrimeBlock_mass_le_reciprocalBetween i
  have hraw := reciprocalPrimesBetween_le_brunTitchmarsh_of_endpoints
      x (16 * x) (Real.sqrt x) hxpos (by linarith) hsqrt
  have hEq : (dyadicDisjointUpperEndpoint i : ℝ) = 16 * x := by
    dsimp [x, dyadicDisjointLowerEndpoint, dyadicDisjointUpperEndpoint]
    rw [show 4 * (i + 1) = 4 * i + 4 by omega, pow_add]
    norm_num [Nat.cast_pow]
    ring
  have hmass' : (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      reciprocalPrimesBetween x (16 * x) := by
    rw [← hEq]
    exact hmass
  calc
    (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
        reciprocalPrimesBetween x (16 * x) := hmass'
    _ ≤ (2 * ((16 * x) - x) / Real.log (Real.sqrt x) +
        6 * Real.sqrt x * (1 + Real.log (Real.sqrt x)) ^ 3) / x := hraw
    _ = (30 * x / Real.log (Real.sqrt x) +
        6 * Real.sqrt x * (1 + Real.log (Real.sqrt x)) ^ 3) / x := by ring
    _ = (30 * (dyadicDisjointLowerEndpoint i : ℝ) /
          Real.log (Real.sqrt (dyadicDisjointLowerEndpoint i : ℝ)) +
        6 * Real.sqrt (dyadicDisjointLowerEndpoint i : ℝ) *
          (1 + Real.log (Real.sqrt (dyadicDisjointLowerEndpoint i : ℝ))) ^ 3) /
        (dyadicDisjointLowerEndpoint i : ℝ) := by rfl

/- The same block estimate in the natural dyadic index.  Since
   `log √(2^(4i)) = 2 i log 2`, the main term is exactly `15/(i log 2)` and the residual
   Selberg term is exponentially small in `i`.  This is the form intended for a future finite
   summation over `i`; no convergence claim is hidden in this pointwise statement. -/
theorem dyadicDisjointPrimeBlock_mass_le_brun_simplified (i : ℕ) (hi : 1 ≤ i) :
    (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      15 / ((i : ℝ) * Real.log 2) +
      6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
        ((2 : ℝ) ^ (2 * i)) := by
  have hraw := dyadicDisjointPrimeBlock_mass_le_brun i hi
  let x : ℝ := (dyadicDisjointLowerEndpoint i : ℝ)
  have hx : x = (2 : ℝ) ^ (4 * i) := by
    dsimp [x, dyadicDisjointLowerEndpoint]
    norm_num [Nat.cast_pow]
  have hsqrt : Real.sqrt x = (2 : ℝ) ^ (2 * i) := by
    rw [hx]
    have hpow : (2 : ℝ) ^ (4 * i) = ((2 : ℝ) ^ (2 * i)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow, Real.sqrt_sq]
    positivity
  have hlog : Real.log (Real.sqrt x) = (2 * (i : ℝ)) * Real.log 2 := by
    rw [hsqrt, Real.log_pow]
    norm_num
  have hipos : 0 < (i : ℝ) := by
    exact_mod_cast (show 0 < i by omega)
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [show (dyadicDisjointLowerEndpoint i : ℝ) = x by rfl] at hraw
  rw [hlog, hsqrt] at hraw
  have hpowpos : 0 < (2 : ℝ) ^ (2 * i) := by positivity
  have hEq :
      (30 * x / ((2 * (i : ℝ)) * Real.log 2) +
        6 * (2 : ℝ) ^ (2 * i) *
          (1 + (2 * (i : ℝ)) * Real.log 2) ^ 3) / x =
      15 / ((i : ℝ) * Real.log 2) +
      6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
        ((2 : ℝ) ^ (2 * i)) := by
    rw [hx]
    field_simp [hipos.ne', hlog2, hpowpos.ne']
    ring
  exact hraw.trans_eq hEq

/- Finite block-sum form.  It keeps the harmonic main term and the exponentially decaying
   Selberg remainder separate, so later callers may discharge the remainder by any preferred
   summability argument (elementary induction, a geometric envelope, or an imported estimate). -/
theorem dyadicDisjointPrimeBlock_mass_sum_le_brun
    (s : Finset ℕ) (hpos : ∀ i ∈ s, 1 ≤ i) :
    (∑ i ∈ s, ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      (15 / Real.log 2) * (∑ i ∈ s, ((i : ℝ)⁻¹)) +
      ∑ i ∈ s, (6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
        ((2 : ℝ) ^ (2 * i))) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    (∑ i ∈ s, ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
        ∑ i ∈ s, (15 / ((i : ℝ) * Real.log 2) +
          6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
            ((2 : ℝ) ^ (2 * i))) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : 1 ≤ i
      · exact dyadicDisjointPrimeBlock_mass_le_brun_simplified i h
      · have hi0 : i < 1 := Nat.lt_of_not_ge h
        exact False.elim ((Nat.not_lt_of_ge (hpos i hi)) hi0)
    _ = (15 / Real.log 2) * (∑ i ∈ s, ((i : ℝ)⁻¹)) +
        ∑ i ∈ s, (6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
          ((2 : ℝ) ^ (2 * i))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi1 : 0 < i := lt_of_lt_of_le Nat.zero_lt_one (hpos i hi)
      have hipos : 0 < (i : ℝ) := by exact_mod_cast hi1
      field_simp [hipos.ne', hlog2.ne']

/- A small elementary envelope for the Selberg remainder.  The induction starts at `10`, where
   `i^3 ≤ 2^i`, and the step uses `(i+1)^3 ≤ 2 i^3`; this is deliberately proved in `Nat` so
   the subsequent real estimate is cast-safe. -/
theorem nat_cube_le_two_pow_of_ge (i : ℕ) (hi : 10 ≤ i) : i ^ 3 ≤ 2 ^ i := by
  induction i, hi using Nat.le_induction with
  | base => norm_num
  | succ i hi ih =>
    have hi4 : 4 ≤ i := by omega
    have hpoly : (i + 1 : ℕ) ^ 3 ≤ 2 * i ^ 3 := by
      norm_num [pow_succ]
      nlinarith
    calc
      (i + 1 : ℕ) ^ 3 ≤ 2 * i ^ 3 := hpoly
      _ ≤ 2 * 2 ^ i := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (i + 1) := by rw [pow_succ, Nat.mul_comm]

/- For `i≥10`, the cubic Brun remainder is bounded by a geometric term. -/
theorem dyadicBrun_error_le_inv_pow_two (i : ℕ) (hi : 10 ≤ i) :
    6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
        ((2 : ℝ) ^ (2 * i)) ≤ 162 / ((2 : ℝ) ^ i) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2lt : Real.log (2 : ℝ) < 1 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    have h := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
    nlinarith
  have hipos : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hpos2i : 0 < 2 * (i : ℝ) := by positivity
  have hprod0 := mul_lt_mul_of_pos_left hlog2lt hpos2i
  have hprod : 2 * (i : ℝ) * Real.log 2 < 2 * (i : ℝ) := by
    simpa using hprod0
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by
    exact_mod_cast (show 1 ≤ i from le_trans (by norm_num) hi)
  have hlin : 1 + 2 * (i : ℝ) * Real.log 2 ≤ 3 * (i : ℝ) := by
    nlinarith [hprod]
  have hcub : (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 ≤
      (3 * (i : ℝ)) ^ 3 := by
    gcongr
  have hnat := nat_cube_le_two_pow_of_ge i hi
  have hpow : (i : ℝ) ^ 3 ≤ (2 : ℝ) ^ i := by exact_mod_cast hnat
  have hnum : 6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 ≤
      162 * (2 : ℝ) ^ i := by
    calc
      6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 ≤ 6 * (3 * (i : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left hcub (by norm_num)
      _ = 162 * (i : ℝ) ^ 3 := by ring
      _ ≤ 162 * (2 : ℝ) ^ i := by gcongr
  have hden : 0 < (2 : ℝ) ^ (2 * i) := by positivity
  have hdiv := div_le_div_of_nonneg_right hnum hden.le
  calc
    6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
        ((2 : ℝ) ^ (2 * i)) ≤
      (162 * (2 : ℝ) ^ i) / ((2 : ℝ) ^ (2 * i)) := hdiv
    _ = 162 / ((2 : ℝ) ^ i) := by
      rw [show 2 * i = i + i by omega, pow_add]
      field_simp

/- The geometric tail of the remainder is uniformly bounded. -/
theorem sum_inv_pow_two_le_two (m : ℕ) :
    (∑ i ∈ Finset.range m, 1 / ((2 : ℝ) ^ i)) ≤ 2 := by
  have hgeom : (1 - (1 / 2 : ℝ)) *
      (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i) =
      1 - (1 / 2 : ℝ) ^ m := by
    have h := geom_sum_mul (1 / 2 : ℝ) m
    nlinarith [h]
  have hsum : (∑ i ∈ Finset.range m, 1 / ((2 : ℝ) ^ i)) =
      ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [one_div, inv_pow]
  rw [hsum]
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
  have hle : (1 / 2 : ℝ) ^ m ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [hgeom]

theorem sum_dyadicBrun_error_filter_le (m : ℕ) :
    (∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i),
      6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
        ((2 : ℝ) ^ (2 * i))) ≤ 324 := by
  calc
    (∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i),
        6 * (1 + 2 * (i : ℝ) * Real.log 2) ^ 3 /
          ((2 : ℝ) ^ (2 * i))) ≤
        ∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i),
          162 / ((2 : ℝ) ^ i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact dyadicBrun_error_le_inv_pow_two i (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ Finset.range m, 162 / ((2 : ℝ) ^ i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact (Finset.mem_filter.mp hi).1
      · intro i hi hnot
        positivity
    _ = 162 * (∑ i ∈ Finset.range m, 1 / ((2 : ℝ) ^ i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ 162 * 2 := by
      gcongr
      exact sum_inv_pow_two_le_two m
    _ = 324 := by norm_num

/- Combining the pointwise Brun estimate with the geometric envelope gives a finite block sum
   bound whose only uncompressed part is the reciprocal harmonic sum over the chosen indices. -/
theorem dyadicDisjointPrimeBlock_mass_sum_le_brun_with_error_bound (m : ℕ) :
    (∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i),
      ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      (15 / Real.log 2) *
          (∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i), ((i : ℝ)⁻¹)) + 324 := by
  have hmain := dyadicDisjointPrimeBlock_mass_sum_le_brun
    ((Finset.range m).filter (fun i ↦ 10 ≤ i)) (by
      intro i hi
      exact le_trans (by norm_num) (Finset.mem_filter.mp hi).2)
  have herror := sum_dyadicBrun_error_filter_le m
  have hmain' := add_le_add_left herror
    ((15 / Real.log 2) *
      (∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i), ((i : ℝ)⁻¹)))
  exact hmain.trans (by simpa [add_comm, add_left_comm, add_assoc] using hmain')

/- The filtered reciprocal sum is a sub-sum of the harmonic block `H_m`.  This is the precise
   finite `O(log m)` consequence of the dyadic Brun kernel. -/
theorem sum_filtered_inv_le_harmonic (m : ℕ) :
    (∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i), ((i : ℝ)⁻¹)) ≤
      (harmonic m : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have hiF := Finset.mem_filter.mp hi
    have him : i < m := Finset.mem_range.mp hiF.1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi hnot
    positivity

theorem dyadicDisjointPrimeBlock_mass_sum_le_brun_with_harmonic (m : ℕ) :
    (∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i),
      ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      (15 / Real.log 2) * (harmonic m : ℝ) + 324 := by
  have hprev := dyadicDisjointPrimeBlock_mass_sum_le_brun_with_error_bound m
  have hcoef : 0 ≤ 15 / Real.log (2 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (sum_filtered_inv_le_harmonic m) hcoef
  have hadd := add_le_add_right hmul (324 : ℝ)
  exact hprev.trans (by simpa [add_comm, add_left_comm, add_assoc] using hadd)

/- The preceding tail estimate lifts to the whole disjoint family after separating the
   finitely many indices below `10`.  This is the convenient finite `O(log m)` upper bound
   used when a cutoff is covered by the dyadic family. -/
theorem dyadicDisjointPrimeFamily_mass_le_harmonic_brun (m : ℕ) (hm : 10 ≤ m) :
    (∑ p ∈ dyadicDisjointPrimeFamily m, ((p : ℝ)⁻¹)) ≤
      (∑ i ∈ Finset.range 10,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
      (15 / Real.log 2) * (harmonic m : ℝ) + 324 := by
  rw [dyadicDisjointPrimeFamily_mass_eq]
  have hsplit :
      (∑ i ∈ Finset.range m,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) =
      (∑ i ∈ Finset.range 10,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
      ∑ i ∈ (Finset.range m).filter (fun i ↦ 10 ≤ i),
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹) := by
    rw [← Finset.sum_range_add_sum_Ico _ hm]
    apply congrArg (fun z =>
      (∑ i ∈ Finset.range 10,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) + z)
    have hfilter : (Finset.range m).filter (fun i ↦ 10 ≤ i) = Finset.Ico 10 m := by
      ext i
      simp [Finset.mem_Ico, and_comm]
    rw [hfilter]
  rw [hsplit]
  have htail := dyadicDisjointPrimeBlock_mass_sum_le_brun_with_harmonic m
  linarith

/- A cutoff `Y` is covered by the first `Nat.log 16 Y + 1` disjoint dyadic blocks.
   Combining the cover with the preceding family bound yields a fully finite reciprocal-prime
   estimate, with the only remaining analytic work being the comparison of this harmonic index
   with the desired logarithmic scale. -/
theorem primesLE_mass_le_dyadic_harmonic (Y : ℕ)
    (hY : 10 ≤ Nat.log 16 Y + 1) :
    (∑ p ∈ Nat.primesLE Y, ((p : ℝ)⁻¹)) ≤
      (∑ i ∈ Finset.range 10,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
      (15 / Real.log 2) * (harmonic (Nat.log 16 Y + 1) : ℝ) + 324 := by
  have hcover :
      (∑ p ∈ Nat.primesLE Y, ((p : ℝ)⁻¹)) ≤
        (∑ p ∈ dyadicDisjointPrimeFamily (Nat.log 16 Y + 1), ((p : ℝ)⁻¹)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact primesLE_subset_dyadicDisjointPrimeFamily_succ_log Y
    · intro p hp hnot
      positivity
  have hupper := dyadicDisjointPrimeFamily_mass_le_harmonic_brun
    (Nat.log 16 Y + 1) hY
  exact hcover.trans hupper

/- Replacing the finite harmonic number by its elementary logarithmic majorant makes the nested
   scale explicit.  This is the form to compare with the paper's later `log log`/`log log log`
   normalizations once the cutoff `Y` is instantiated. -/
theorem primesLE_mass_le_dyadic_log (Y : ℕ)
    (hY : 10 ≤ Nat.log 16 Y + 1) :
    (∑ p ∈ Nat.primesLE Y, ((p : ℝ)⁻¹)) ≤
      (∑ i ∈ Finset.range 10,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
      (15 / Real.log 2) * (1 + Real.log ((Nat.log 16 Y + 1 : ℕ) : ℝ)) + 324 := by
  have hbase := primesLE_mass_le_dyadic_harmonic Y hY
  have hharm : (harmonic (Nat.log 16 Y + 1) : ℝ) ≤
      1 + Real.log ((Nat.log 16 Y + 1 : ℕ) : ℝ) := by
    simpa only [Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
      (harmonic_le_one_add_log (Nat.log 16 Y + 1))
  have hcoef : 0 ≤ 15 / Real.log (2 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hharm hcoef
  have hadd := add_le_add_right hmul
    ((∑ i ∈ Finset.range 10,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) + 324)
  linarith

/- A prime-counting alternative for a single disjoint block.  If the global estimate
   `π(U) ≤ C U/log U` is supplied at the block endpoint `U=2^(4(i+1))`, the reciprocal mass is
   at most `4 C / ((i+1) log 2)`.  This is the exact finite input needed to replace the
   Brun--Titchmarsh route by LeanPool's global `π` bound. -/
theorem dyadicDisjointPrimeBlock_mass_le_primeCounting_bound
    (i : ℕ) (C : ℝ)
    (hpi : (Nat.primeCounting (dyadicDisjointUpperEndpoint i) : ℝ) ≤
      C * (dyadicDisjointUpperEndpoint i : ℝ) /
        Real.log (dyadicDisjointUpperEndpoint i : ℝ)) :
    (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      4 * C / (((i + 1 : ℕ) : ℝ) * Real.log 2) := by
  let S := dyadicDisjointPrimeBlock i
  let L := dyadicDisjointLowerEndpoint i
  let U := dyadicDisjointUpperEndpoint i
  have hLpos : 0 < L := by
    dsimp [L, dyadicDisjointLowerEndpoint]
    positivity
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hLpos
  have hSsub : S ⊆ Nat.primesLE U := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpI := Finset.mem_Icc.mp hp'.1
    exact Nat.mem_primesLE.mpr ⟨hpI.2, hp'.2⟩
  have hcardNat : S.card ≤ Nat.primeCounting U := by
    have hc := Finset.card_le_card hSsub
    simpa [Nat.primesLE_card_eq_primeCounting] using hc
  have hcard : (S.card : ℝ) ≤ (Nat.primeCounting U : ℝ) := by
    exact_mod_cast hcardNat
  have hmass_card : (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤ (S.card : ℝ) / (L : ℝ) := by
    have hpoint : ∀ p ∈ S, (L : ℝ) * ((p : ℝ)⁻¹) ≤ (1 : ℝ) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpI := Finset.mem_Icc.mp hp'.1
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp'.2.pos
      have hple : (L : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_add_right _ _) hpI.1)
      have hdiv : (L : ℝ) / (p : ℝ) ≤ (1 : ℝ) := by
        exact (div_le_iff₀ hpR).2 (by simpa using hple)
      simpa [div_eq_mul_inv] using hdiv
    have hsum : (L : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤ (S.card : ℝ) := by
      calc
        (L : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) =
            ∑ p ∈ S, (L : ℝ) * ((p : ℝ)⁻¹) := by rw [Finset.mul_sum]
        _ ≤ ∑ _p ∈ S, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
        _ = (S.card : ℝ) := by simp
    apply (le_div_iff₀ hLreal).2
    simpa [mul_comm] using hsum
  have hmass_pi : (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤
      (Nat.primeCounting U : ℝ) / (L : ℝ) := by
    apply hmass_card.trans
    gcongr
  have hpi' : (Nat.primeCounting U : ℝ) / (L : ℝ) ≤
      (C * (U : ℝ) / Real.log (U : ℝ)) / (L : ℝ) := by
    exact div_le_div_of_nonneg_right hpi hLreal.le
  have hUeq : (U : ℝ) = 16 * (L : ℝ) := by
    dsimp [L, U, dyadicDisjointLowerEndpoint, dyadicDisjointUpperEndpoint]
    rw [show 4 * (i + 1) = 4 * i + 4 by omega, pow_add]
    norm_num [Nat.cast_pow]
    ring
  have hlogU : Real.log (U : ℝ) = (4 * ((i + 1 : ℕ) : ℝ)) * Real.log 2 := by
    dsimp [U, dyadicDisjointUpperEndpoint]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num [Nat.cast_mul, Nat.cast_add]
  rw [hlogU] at hpi'
  rw [hUeq] at hpi'
  calc
    (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤ (Nat.primeCounting U : ℝ) / (L : ℝ) := hmass_pi
    _ ≤ (C * (16 * (L : ℝ)) /
          (4 * ((i + 1 : ℕ) : ℝ) * Real.log 2)) / (L : ℝ) := hpi'
    _ = 4 * C / (((i + 1 : ℕ) : ℝ) * Real.log 2) := by
      have hi : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
      have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
      field_simp [hLreal.ne', hi.ne', hlog2]
      ring

/- LeanPool's global prime-counting estimate can therefore be applied on every sufficiently late
   dyadic block.  This packages the endpoint side condition `U_i ≥ N` and leaves an eventual
   reciprocal-mass bound with one fixed nonnegative constant. -/
theorem eventually_dyadicDisjointPrimeBlock_mass_le_primeCounting_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i : ℕ in atTop,
        (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
          4 * C / (((i + 1 : ℕ) : ℝ) * Real.log 2) := by
  obtain ⟨N, C, hC, hpi⟩ := Upstream.primeCounting_le_mul_bound_nonneg
  have hUevent : ∀ᶠ i : ℕ in atTop,
      N ≤ dyadicDisjointUpperEndpoint i :=
    tendsto_dyadicDisjointUpperEndpoint.eventually (eventually_ge_atTop N)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hUevent] with i hi
  exact dyadicDisjointPrimeBlock_mass_le_primeCounting_bound i C (hpi _ hi)

/- Finite sum form for the global prime-counting certificate.  It is intentionally stated with
   the endpoint hypotheses exposed; a later eventual wrapper can instantiate them on the tail
   of any chosen dyadic family. -/
theorem dyadicDisjointPrimeBlock_mass_sum_le_primeCounting_bound
    (s : Finset ℕ) (C : ℝ)
    (hpi : ∀ i ∈ s,
      (Nat.primeCounting (dyadicDisjointUpperEndpoint i) : ℝ) ≤
        C * (dyadicDisjointUpperEndpoint i : ℝ) /
          Real.log (dyadicDisjointUpperEndpoint i : ℝ)) :
    (∑ i ∈ s, ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
      (4 * C / Real.log 2) *
        (∑ i ∈ s, (((i + 1 : ℕ) : ℝ)⁻¹)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpoint : ∀ i ∈ s,
      (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
        (4 * C / Real.log 2) * (((i + 1 : ℕ) : ℝ)⁻¹) := by
    intro i hi
    have hi' := dyadicDisjointPrimeBlock_mass_le_primeCounting_bound i C (hpi i hi)
    have hI : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    calc
      (∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
          4 * C / (((i + 1 : ℕ) : ℝ) * Real.log 2) := hi'
      _ = (4 * C / Real.log 2) * (((i + 1 : ℕ) : ℝ)⁻¹) := by
        field_simp [hI.ne', hlog2.ne']
  calc
    (∑ i ∈ s, ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) ≤
        ∑ i ∈ s, (4 * C / Real.log 2) * (((i + 1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hpoint i hi
    _ = (4 * C / Real.log 2) *
        (∑ i ∈ s, (((i + 1 : ℕ) : ℝ)⁻¹)) := by rw [Finset.mul_sum]

/-- Explicit specialization to a logarithmic window. Unlike the informal `≪ w / U` shorthand,
this statement retains the additive Selberg-sieve error. Controlling that second term uniformly
is an indispensable part of the bad-pair argument. -/
theorem reciprocal_log_window_le_explicit
    (U w : ℝ) (hw : 0 < w) (hUw : w < U) :
    reciprocalPrimesBetween (Real.exp (U - w)) (Real.exp (U + w)) ≤
      (2 * (Real.exp (U + w) - Real.exp (U - w)) / (U / 2) +
        6 * Real.exp (U / 2) * (1 + U / 2) ^ 3) / Real.exp (U - w) := by
  have hU : 0 < U := hw.trans hUw
  have hx : 0 < Real.exp (U - w) := Real.exp_pos _
  have hy : 0 < Real.exp (U + w) - Real.exp (U - w) := by
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hz : 1 < Real.exp (U / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  simpa [Real.log_exp] using
    reciprocalPrimesBetween_le_brunTitchmarsh
      (Real.exp (U - w))
      (Real.exp (U + w) - Real.exp (U - w))
      (Real.exp (U / 2)) hx hy hz

/-- The explicit Selberg/Brun--Titchmarsh error expression for one logarithmic q-window. -/
def badPairQWindowBrunBound (M r h p : ℕ) : ℝ :=
  let U : ℝ := ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)
  let w : ℝ := Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))
  (2 * (Real.exp (U + w) - Real.exp (U - w)) / (U / 2) +
      6 * Real.exp (U / 2) * (1 + U / 2) ^ 3) / Real.exp (U - w)

/-- Algebraic form of the Brun--Titchmarsh majorant.  Separating the main width term from
the additive sieve error makes the later `(r,h,p)` summation explicit. -/
theorem badPairQWindowBrunBound_eq_decomposed
    {M r h p : ℕ} (hM : 0 < M) (hr : 0 < r) (hh : 0 < h) (hp : 1 < p) :
    badPairQWindowBrunBound M r h p =
      let U : ℝ := ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)
      let w : ℝ := Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))
      4 * (Real.exp (2 * w) - 1) / U +
        6 * Real.exp (-U / 2 + w) * (1 + U / 2) ^ 3 := by
  let U : ℝ := ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)
  let w : ℝ := Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hlog : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp)
  have hU : 0 < U := by
    dsimp [U]
    exact mul_pos (div_pos hhR hrR) hlog
  have hU0 : U ≠ 0 := ne_of_gt hU
  have hExp : Real.exp (U - w) ≠ 0 := Real.exp_ne_zero _
  have hratio : Real.exp (U + w) / Real.exp (U - w) = Real.exp (2 * w) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hratio_mul : Real.exp (U + w) = Real.exp (2 * w) * Real.exp (U - w) :=
    (div_eq_iff hExp).mp hratio
  have hfirst :
      (2 * (Real.exp (U + w) - Real.exp (U - w)) / (U / 2)) /
          Real.exp (U - w) =
        4 * (Real.exp (2 * w) - 1) / U := by
    field_simp [hU0, hExp]
    rw [hratio_mul]
    ring
  have hsecond :
      (6 * Real.exp (U / 2) * (1 + U / 2) ^ 3) / Real.exp (U - w) =
        6 * Real.exp (-U / 2 + w) * (1 + U / 2) ^ 3 := by
    have hratio' : Real.exp (U / 2) / Real.exp (U - w) =
        Real.exp (-U / 2 + w) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    have hratio'_mul : Real.exp (U / 2) =
        Real.exp (-U / 2 + w) * Real.exp (U - w) :=
      (div_eq_iff hExp).mp hratio'
    field_simp [hExp]
    rw [hratio'_mul]
    ring_nf
  dsimp [badPairQWindowBrunBound, U, w]
  rw [← hfirst, ← hsecond]
  ring

/-- A uniform elementary estimate for one positive `(r,h,p)` block.  The first term is the
reciprocal-width contribution, while the second retains the exponentially decaying sieve error.
The two side conditions are deliberately explicit: later parameter estimates must prove that the
window half-width is small and that it is at most one quarter of the logarithmic centre. -/
theorem badPairQWindowBrunBound_le_main_plus_decay
    {M r h p : ℕ} (hM : 0 < M) (hr : 0 < r) (hh : 0 < h) (hp : 1 < p)
    (hw : 2 * (Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) ≤ 1)
    (hwu : 4 * (Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) ≤
      ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) :
    badPairQWindowBrunBound M r h p ≤
      16 / ((h : ℝ) * (M : ℝ)) +
        6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
          (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3 := by
  let U : ℝ := ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)
  let w : ℝ := Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hlog : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp)
  have hU : 0 < U := by
    dsimp [U]
    exact mul_pos (div_pos hhR hrR) hlog
  have hU0 : U ≠ 0 := ne_of_gt hU
  have hwpos : 0 < w := by
    dsimp [w]
    exact div_pos hlog (mul_pos hrR hMR)
  have hlin : Real.exp (2 * w) - 1 ≤ 4 * w := by
    have habs := Real.abs_exp_sub_one_le (show |2 * w| ≤ 1 by
      simpa [abs_of_pos hwpos] using hw)
    have hexp : 0 ≤ Real.exp (2 * w) - 1 := by
      linarith [Real.add_one_le_exp (2 * w)]
    rw [abs_of_nonneg hexp] at habs
    have h2w : 0 < 2 * w := mul_pos (by norm_num) hwpos
    have htmp : Real.exp (2 * w) - 1 ≤ 2 * (2 * w) := by
      simpa [abs_of_pos h2w] using habs
    nlinarith [htmp]
  have hwU : w / U = 1 / ((h : ℝ) * (M : ℝ)) := by
    dsimp [U, w]
    field_simp [hrR.ne', hMR.ne', hhR.ne', hlog.ne']
  have hmain : 4 * (Real.exp (2 * w) - 1) / U ≤
      16 / ((h : ℝ) * (M : ℝ)) := by
    calc
      4 * (Real.exp (2 * w) - 1) / U ≤ 4 * (4 * w) / U := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlin (by norm_num)) hU.le
      _ = 16 * (w / U) := by ring
      _ = 16 / ((h : ℝ) * (M : ℝ)) := by rw [hwU]; ring
  have herr : 6 * Real.exp (-U / 2 + w) * (1 + U / 2) ^ 3 ≤
      6 * Real.exp (-U / 4) * (1 + U / 2) ^ 3 := by
    have hexp : Real.exp (-U / 2 + w) ≤ Real.exp (-U / 4) := by
      apply Real.exp_le_exp.mpr
      have hwu' : 4 * w ≤ U := by simpa [U, w] using hwu
      linarith [hwu']
    gcongr
  have hdecomp := badPairQWindowBrunBound_eq_decomposed hM hr hh hp
  have hdecomp' :
      badPairQWindowBrunBound M r h p =
        4 * (Real.exp (2 * w) - 1) / U +
          6 * Real.exp (-U / 2 + w) * (1 + U / 2) ^ 3 := by
    simpa [U, w] using hdecomp
  calc
    badPairQWindowBrunBound M r h p =
        4 * (Real.exp (2 * w) - 1) / U +
          6 * Real.exp (-U / 2 + w) * (1 + U / 2) ^ 3 := hdecomp'
    _ ≤ 16 / ((h : ℝ) * (M : ℝ)) +
          6 * Real.exp (-U / 4) * (1 + U / 2) ^ 3 := add_le_add hmain herr
    _ = 16 / ((h : ℝ) * (M : ℝ)) +
          6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
            (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3 := by
      rfl

/-- The quarter-centre condition follows from the purely arithmetic bound `4 ≤ h M`.  Keeping
this conversion separate lets the parameter proof use natural-number range hypotheses directly. -/
theorem badPairQWindowBrunBound_le_main_plus_decay_of_width
    {M r h p : ℕ} (hM4 : 4 ≤ M) (hr : 0 < r) (hh : 0 < h) (hp : 1 < p)
    (hwidth : 2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    badPairQWindowBrunBound M r h p ≤
      16 / ((h : ℝ) * (M : ℝ)) +
        6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
          (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3 := by
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM4
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast (show 1 ≤ h by omega)
  have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
  have hMR : 0 ≤ (M : ℝ) := by positivity
  have hprod : (4 : ℝ) ≤ (h : ℝ) * (M : ℝ) := by
    have hmul : (M : ℝ) ≤ (h : ℝ) * (M : ℝ) := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hh1 hMR
    exact hM4R.trans hmul
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hMRpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hlog : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp)
  have hwu : 4 * (Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) ≤
      ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
    have hprodlog : 4 * Real.log (p : ℝ) ≤
        ((h : ℝ) * (M : ℝ)) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hprod hlog.le
    have hdiv : (4 * Real.log (p : ℝ)) / (M : ℝ) ≤
        (h : ℝ) * Real.log (p : ℝ) := by
      apply (div_le_iff₀ hMRpos).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hprodlog
    calc
      4 * (Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) =
          ((4 * Real.log (p : ℝ)) / (M : ℝ)) / (r : ℝ) := by
        field_simp [hrR.ne', hMRpos.ne']
      _ ≤ ((h : ℝ) * Real.log (p : ℝ)) / (r : ℝ) :=
        (div_le_div_iff_of_pos_right hrR).2 hdiv
      _ = ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by ring
  have hw : 2 * (Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) ≤ 1 := by
    have hwidth' : (2 * Real.log (p : ℝ)) /
        ((r : ℝ) * (M : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (mul_pos hrR hMRpos)).2
      simpa [one_mul] using hwidth
    calc
      2 * (Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))) =
          (2 * Real.log (p : ℝ)) / ((r : ℝ) * (M : ℝ)) := by ring
      _ ≤ 1 := hwidth'
  exact badPairQWindowBrunBound_le_main_plus_decay hM hr hh hp
    hw hwu

/-- The explicit q-window majorant with the degenerate `r=0` and `h=0` cases removed. -/
def badPairQWindowBrunMajorant (M r h p : ℕ) : ℝ :=
  if r = 0 ∨ h = 0 then 0 else badPairQWindowBrunBound M r h p

/-- The decomposed majorant, with the degenerate indices assigned zero just as in
`badPairQWindowBrunMajorant`. -/
def badPairQWindowBrunDecayMajorant (M r h p : ℕ) : ℝ :=
  if r = 0 ∨ h = 0 then 0 else
    16 / ((h : ℝ) * (M : ℝ)) +
      6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
        (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3

theorem badPairQWindowBrunMajorant_eq_bound_of_pos
    {M r h p : ℕ} (hr : 0 < r) (hh : 0 < h) :
    badPairQWindowBrunMajorant M r h p = badPairQWindowBrunBound M r h p := by
  simp [badPairQWindowBrunMajorant, Nat.ne_of_gt hr, Nat.ne_of_gt hh]

theorem badPairQWindowBrunMajorant_le_decayMajorant
    {M r h p : ℕ} (hM4 : 4 ≤ M) (hr : 0 < r) (hh : 0 < h) (hp : 1 < p)
    (hwidth : 2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    badPairQWindowBrunMajorant M r h p ≤
      badPairQWindowBrunDecayMajorant M r h p := by
  rw [badPairQWindowBrunMajorant_eq_bound_of_pos hr hh]
  simp [badPairQWindowBrunDecayMajorant, Nat.ne_of_gt hr, Nat.ne_of_gt hh]
  exact badPairQWindowBrunBound_le_main_plus_decay_of_width hM4 hr hh hp hwidth

/- The same bridge with the exact logarithmic centre and half-width used by `badPairQWindow`.
This is the form needed before summing over `p`, `r`, and `h`; no asymptotic estimate is hidden in
the specialization. -/
theorem badPairQWindow_reciprocal_le_explicit
    (T α β γ δ rho : ℝ) (M r h p : ℕ)
    (hw : 0 < Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)))
    (hUw : Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) <
      ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) :
    (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) ≤
      badPairQWindowBrunBound M r h p := by
  let U : ℝ := ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)
  let w : ℝ := Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ))
  have hwindow := badPairQWindow_reciprocal_le T α β γ δ rho M r h p
  have hexplicit := reciprocal_log_window_le_explicit U w hw hUw
  exact hwindow.trans (by simpa [badPairQWindowBrunBound, U, w] using hexplicit)

/- The p-sliced block has a one-dimensional weight bound.  Together with
`badPairBlocksPrimeDependent`, this is the finite bridge that preserves the logarithmic
`denominatorCutoff p rho` instead of replacing it by a global `T^beta` range. -/
theorem badPairBlockAtPrimeWeight_le_brunTitchmarsh
    (T α β γ δ rho : ℝ) (M p r h : ℕ)
    (hp : p ∈ primeWindow T α β) (hM : 1 < M) (hr : 0 < r) (hh : 0 < h) :
    pairReciprocalWeight (badPairBlockAtPrime T α β γ δ rho M p r h) ≤
      ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
  have hsubset := badPairBlockAtPrime_subset_qWindow_image
    T α β γ δ rho M p r h
  have hwindow := badPairQWindow_hypotheses_of_prime_window hp hM hr hh
  calc
    pairReciprocalWeight (badPairBlockAtPrime T α β γ δ rho M p r h) ≤
        pairReciprocalWeight
          ((badPairQWindow T α β γ δ rho M r h p).image (fun q ↦ (p, q))) :=
      pairReciprocalWeight_mono hsubset
    _ = ((p : ℝ)⁻¹) *
          (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) :=
      pairReciprocalWeight_image_fixed_left p
        (badPairQWindow T α β γ δ rho M r h p)
    _ ≤ ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
      apply mul_le_mul_of_nonneg_left
      · exact badPairQWindow_reciprocal_le_explicit T α β γ δ rho M r h p
          hwindow.1 hwindow.2
      · positivity

/- Combining the p-sliced block estimate with the p-dependent finite cover gives the exact
majorant whose main term can be rewritten using `pDependent_main_term_reorder`. -/
theorem badPairWeight_le_primeDependent_brunTitchmarsh
    (T α β γ δ rho : ℝ) (M : ℕ) (R : ℕ → ℕ) (H : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hM : 1 < M)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h)
    (hR : ∀ ⦃p : ℕ⦄, p ∈ primeWindow T α β →
      denominatorCutoff p rho ≤ R p) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (R p),
          ∑ h ∈ Finset.range H,
            ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := by
  have hbase := badPairWeight_le_primeDependent_block_sum
    T α β γ δ rho M R H hcover hR
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        ∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (R p),
            ∑ h ∈ Finset.range H,
              pairReciprocalWeight
                (badPairBlockAtPrime T α β γ δ rho M p r h) := hbase
    _ ≤ ∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (R p),
            ∑ h ∈ Finset.range H,
              ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro h hh
      by_cases hr0 : r = 0
      · subst r
        simp [badPairBlockAtPrime, badPairBlock_zero_r_empty,
          badPairQWindowBrunMajorant, pairReciprocalWeight]
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
        by_cases hh0 : h = 0
        · subst h
          have hempty := badPairBlock_h_zero_empty_of_ordered_windows
            T α β γ δ rho M r hT hβγ hM hrpos
          simp [badPairBlockAtPrime, hempty, badPairQWindowBrunMajorant,
            pairReciprocalWeight, hr0]
        · have hhpos : 0 < h := Nat.pos_of_ne_zero hh0
          simpa [badPairQWindowBrunMajorant_eq_bound_of_pos hrpos hhpos] using
            (badPairBlockAtPrimeWeight_le_brunTitchmarsh
              T α β γ δ rho M p r h hp hM hrpos hhpos)

/- The report-scale hypotheses already supply the h-bound needed by the p-dependent cover.  The
r-bound is not reintroduced globally: it remains the literal `denominatorCutoff p rho` coming
from `isBadApprox`. -/
theorem badPairs_cover_primeDependent_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α) :
    ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r, ∃ h < reportHBound T α β δ rho M,
          isBadApprox rho M pq.1 pq.2 r h := by
  have hsubset := badPairs_subset_badPairBlocks_of_report_bounds
    T α β γ δ rho M hT hβγ hrho hM hL hpositive
  have hcover := badPairs_cover_of_subset_badPairBlocks
    T α β γ δ rho M (reportRBound T β rho)
      (reportHBound T α β δ rho M) hsubset
  intro pq hpq
  obtain ⟨r, hrR, h, hhH, hbad⟩ := hcover hpq
  exact ⟨r, h, hhH, hbad⟩

theorem badPairWeight_le_primeDependent_brunTitchmarsh_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
            ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := by
  apply badPairWeight_le_primeDependent_brunTitchmarsh
    T α β γ δ rho M (fun p ↦ denominatorCutoff p rho)
      (reportHBound T α β δ rho M) hT hβγ hM
  · exact badPairs_cover_primeDependent_report_bounds
      T α β γ δ rho M hT hβγ hrho hM hL hpositive
  · intro p hp
    exact le_rfl

/- Decay form of the p-dependent report-scale bound.  The lower h-cutoff is retained as an
indicator, while the p-dependent r-range is retained in the outer sum.  This is the exact finite
expression to which the analytic estimate
`sum (log p)/p = O(T^beta)` can be applied. -/
theorem badPairWeight_le_primeDependent_decay_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM4 : 4 ≤ M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α)
    (hwidth : ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
            if primeWindowHLower T β γ M r ≤ h then
              ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p
            else 0 := by
  have hMgt : 1 < M := by omega
  have hcover := badPairs_cover_primeDependent_report_bounds
    T α β γ δ rho M hT hβγ hrho hMgt hL hpositive
  have hbase := badPairWeight_le_primeDependent_block_sum
    T α β γ δ rho M (fun p ↦ denominatorCutoff p rho)
      (reportHBound T α β δ rho M) hcover (by intro p hp; exact le_rfl)
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        ∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
              pairReciprocalWeight
                (badPairBlockAtPrime T α β γ δ rho M p r h) := hbase
    _ ≤ ∑ p ∈ primeWindow T α β,
          ∑ r ∈ Finset.range (denominatorCutoff p rho),
            ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
              if primeWindowHLower T β γ M r ≤ h then
                ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p
              else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro h hh
      by_cases hlow : primeWindowHLower T β γ M r ≤ h
      · simp [hlow]
        by_cases hr0 : r = 0
        · subst r
          simp [badPairBlockAtPrime, badPairBlock_zero_r_empty,
            badPairQWindowBrunDecayMajorant, pairReciprocalWeight]
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          by_cases hh0 : h = 0
          · subst h
            have hempty := badPairBlock_h_zero_empty_of_ordered_windows
              T α β γ δ rho M r hT hβγ hMgt hrpos
            simp [badPairBlockAtPrime, hempty, badPairQWindowBrunDecayMajorant,
              pairReciprocalWeight, hr0]
          · have hhpos : 0 < h := Nat.pos_of_ne_zero hh0
            have hblock := badPairBlockAtPrimeWeight_le_brunTitchmarsh
              T α β γ δ rho M p r h hp hMgt hrpos hhpos
            have hdecay := badPairQWindowBrunMajorant_le_decayMajorant
              hM4 hrpos hhpos (Finset.mem_filter.mp hp).2.1.one_lt
                (hwidth p hp r hrpos)
            have hmul : ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p ≤
                ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p := by
              exact mul_le_mul_of_nonneg_left hdecay (by positivity)
            have hblock' :
                pairReciprocalWeight
                    (badPairBlockAtPrime T α β γ δ rho M p r h) ≤
                  ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := by
              simpa [badPairQWindowBrunMajorant_eq_bound_of_pos hrpos hhpos] using hblock
            exact hblock'.trans hmul
      · simp [hlow]
        have hempty := badPairBlock_empty_below_primeWindowHLower
          (T := T) (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho)
          (M := M) (r := r) (h := h) hT (Nat.zero_lt_of_lt hMgt)
            (Nat.lt_of_not_ge hlow)
        simp [badPairBlockAtPrime, hempty, pairReciprocalWeight]

/-- A fixed rational-approximation block is bounded by the sum of its explicit q-window errors.
The hypotheses deliberately expose the positivity and relative-width checks that the final
parameter-summation proof must discharge uniformly. -/
theorem badPairBlockWeight_le_brunTitchmarsh_sum
    (T α β γ δ rho : ℝ) (M r h : ℕ)
    (hwindow : ∀ p ∈ primeWindow T α β,
      0 < Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) ∧
        Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) <
          ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) :
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
  calc
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
        pairReciprocalWeight (badPairBlockQWindows T α β γ δ rho M r h) :=
      badPairBlockWeight_le_qWindows T α β γ δ rho M r h
    _ ≤ ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) *
          (∑ q ∈ badPairQWindow T α β γ δ rho M r h p, ((q : ℝ)⁻¹)) :=
      pairReciprocalWeight_qWindows_le T α β γ δ rho M r h
    _ ≤ ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · exact badPairQWindow_reciprocal_le_explicit T α β γ δ rho M r h p
          (hwindow p hp).1 (hwindow p hp).2
      · positivity

theorem badPairBlockWeight_le_brunTitchmarsh_sum_of_parameters
    (T α β γ δ rho : ℝ) (M r h : ℕ)
    (hM : 1 < M) (hr : 0 < r) (hh : 0 < h) :
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
  exact badPairBlockWeight_le_brunTitchmarsh_sum T α β γ δ rho M r h
    (fun p hp ↦ badPairQWindow_hypotheses_of_prime_window hp hM hr hh)

/-- Block-level version of the elementary decomposition.  It exposes the exact finite sum that
must later be estimated; no prime-counting or asymptotic assertion is hidden here. -/
theorem badPairBlockWeight_le_main_plus_decay_sum
    (T α β γ δ rho : ℝ) {M r h : ℕ} (hM4 : 4 ≤ M) (hr : 0 < r) (hh : 0 < h)
    (hwidth : ∀ p ∈ primeWindow T α β,
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) *
          (16 / ((h : ℝ) * (M : ℝ)) +
            6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
              (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3) := by
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM4
  have hbase := badPairBlockWeight_le_brunTitchmarsh_sum_of_parameters
    T α β γ δ rho M r h (by omega) hr hh
  calc
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := hbase
    _ ≤ ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) *
          (16 / ((h : ℝ) * (M : ℝ)) +
            6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
              (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · exact badPairQWindowBrunBound_le_main_plus_decay_of_width hM4 hr hh
          (Finset.mem_filter.mp hp).2.1.one_lt (hwidth p hp)
      · positivity

/-- Source-scale eventual form of the block estimate.  It is still a finite sum, but all
window-width side conditions have now been discharged from `beta + delta < 1`. -/
theorem eventually_badPairBlockWeight_le_main_plus_decay_sum_of_report_scale
    {α beta delta : ℝ} {Tgamma rho : ℝ} {r h : ℕ}
    (hbeta : 0 ≤ beta) (hbetadelta : beta + delta < 1)
    (hr : 0 < r) (hh : 0 < h) :
    ∀ᶠ T : ℝ in atTop,
      pairReciprocalWeight
          (badPairBlock T α beta Tgamma delta rho
            (reportApproximationScale T delta) r h) ≤
        ∑ p ∈ primeWindow T α beta,
          ((p : ℝ)⁻¹) *
            (16 / ((h : ℝ) * (reportApproximationScale T delta : ℝ)) +
              6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
                (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3) := by
  have hdelta : delta < 1 := by linarith
  filter_upwards [eventually_reportApproximationScale_ge_four hdelta,
    eventually_primeWindow_width_of_reportApproximationScale hbeta hbetadelta]
    with T hM4 hwidth
  have hM4nat : 4 ≤ reportApproximationScale T delta := by exact_mod_cast hM4
  exact badPairBlockWeight_le_main_plus_decay_sum T α beta Tgamma delta rho
    hM4nat hr hh (fun p hp ↦ hwidth p hp r hr)

theorem badPairBlockWeight_le_brunTitchmarsh_majorant_of_ordered_parameters
    (T α β γ δ rho : ℝ) (M r h : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hM : 1 < M) :
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
      ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := by
  by_cases hr0 : r = 0
  · subst r
    rw [badPairBlock_zero_r_empty]
    simp [pairReciprocalWeight, badPairQWindowBrunMajorant]
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    by_cases hh0 : h = 0
    · subst h
      rw [badPairBlock_h_zero_empty_of_ordered_windows T α β γ δ rho M r
        hT hβγ hM hr]
      simp [pairReciprocalWeight, badPairQWindowBrunMajorant, hr0]
    · have hh : 0 < h := Nat.pos_of_ne_zero hh0
      have hbase := badPairBlockWeight_le_brunTitchmarsh_sum_of_parameters
        T α β γ δ rho M r h hM hr hh
      simpa [badPairQWindowBrunMajorant, hh0, hr0] using hbase

theorem badPairWeight_le_brunTitchmarsh_majorant_sum_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range (reportRBound T β rho),
        ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
          ∑ p ∈ primeWindow T α β,
            ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := by
  have hsubset := badPairs_subset_badPairBlocks_of_report_bounds T α β γ δ rho M
      hT hβγ hrho hM hL hpositive
  exact badPairWeight_le_parameter_sum_of_bounds T α β γ δ rho M
    (reportRBound T β rho) (reportHBound T α β δ rho M)
    (badPairs_cover_of_subset_badPairBlocks T α β γ δ rho M
      (reportRBound T β rho) (reportHBound T α β δ rho M) hsubset)
    (fun r h ↦ ∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p)
    (by
      intro r h hrR hhH
      exact badPairBlockWeight_le_brunTitchmarsh_majorant_of_ordered_parameters
        T α β γ δ rho M r h hT hβγ hM)

/-- Report-scale outer bound after replacing every positive-index Brun term by the explicit
main-plus-decay expression.  The only remaining input is the elementary width inequality for the
first prime window. -/
theorem badPairWeight_le_brunTitchmarsh_decay_majorant_sum_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM4 : 4 ≤ M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α)
    (hwidth : ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range (reportRBound T β rho),
        ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
          ∑ p ∈ primeWindow T α β,
            ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p := by
  have hupper := badPairWeight_le_brunTitchmarsh_majorant_sum_of_report_bounds
    T α β γ δ rho M hT hβγ hrho (by omega) hL hpositive
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        ∑ r ∈ Finset.range (reportRBound T β rho),
          ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
            ∑ p ∈ primeWindow T α β,
              ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := hupper
    _ ≤ ∑ r ∈ Finset.range (reportRBound T β rho),
        ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
          ∑ p ∈ primeWindow T α β,
            ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p := by
      apply Finset.sum_le_sum
      intro r hrR
      apply Finset.sum_le_sum
      intro h hhH
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · by_cases hz : r = 0 ∨ h = 0
        · simp [badPairQWindowBrunMajorant, badPairQWindowBrunDecayMajorant, hz]
        · have hr : 0 < r := Nat.pos_of_ne_zero (fun hr0 ↦ hz (Or.inl hr0))
          have hh : 0 < h := Nat.pos_of_ne_zero (fun hh0 ↦ hz (Or.inr hh0))
          exact badPairQWindowBrunMajorant_le_decayMajorant hM4 hr hh
            (Finset.mem_filter.mp hp).2.1.one_lt (hwidth p hp r hr)
      · positivity

/-- Final squeeze wrapper using the decomposed report-scale majorant.  Once the displayed decay
sum is shown to tend to zero, this theorem supplies the bad-pair conclusion without any further
finite-cover bookkeeping. -/
theorem tendsto_badPairWeight_zero_of_report_decay_majorant
    {alpha beta gamma delta rho : ℝ} (bound : ℝ → ℝ)
    (hbeta : 0 ≤ beta) (hbetadelta : beta + delta < 1)
    (hβγ : beta ≤ gamma) (hrho : 0 < rho)
    (hsum : ∀ᶠ T : ℝ in atTop,
      (∑ r ∈ Finset.range (reportRBound T beta rho),
        ∑ h ∈ Finset.range (reportHAtReportScale T alpha beta delta rho),
          ∑ p ∈ primeWindow T alpha beta,
            ((p : ℝ)⁻¹) *
              badPairQWindowBrunDecayMajorant
                (reportApproximationScale T delta) r h p) ≤ bound T)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    Tendsto
      (fun T ↦ pairReciprocalWeight
        (badPairsAtReportScale T alpha beta gamma delta rho))
      atTop (𝓝 0) := by
  have hdelta : delta < 1 := by linarith
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop _
  have hM : ∀ᶠ T : ℝ in atTop, 1 < reportApproximationScale T delta := by
    filter_upwards [eventually_reportApproximationScale_ge_four hdelta] with T hM4
    have hM4nat : 4 ≤ reportApproximationScale T delta := by exact_mod_cast hM4
    omega
  have hsum' : ∀ᶠ T : ℝ in atTop,
      (∑ r ∈ Finset.range (reportRBound T beta rho),
        ∑ h ∈ Finset.range (reportHBound T alpha beta delta rho
          (reportApproximationScale T delta)),
          ∑ p ∈ primeWindow T alpha beta,
            ((p : ℝ)⁻¹) *
              badPairQWindowBrunMajorant
                (reportApproximationScale T delta) r h p) ≤ bound T := by
    filter_upwards [hsum, eventually_reportApproximationScale_ge_four hdelta,
      eventually_primeWindow_width_of_reportApproximationScale hbeta hbetadelta,
      hT] with T hsumT hM4 hwidth hT1
    have hM4nat : 4 ≤ reportApproximationScale T delta := by exact_mod_cast hM4
    have hL : 0 < Real.rpow T alpha :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT1) _
    have hpositive : 0 < Real.rpow T delta / Real.rpow T alpha :=
      report_endpoint_ratio_pos (lt_of_lt_of_le zero_lt_one hT1)
    have hmajorant := badPairWeight_le_brunTitchmarsh_majorant_sum_of_report_bounds
      T alpha beta gamma delta rho (reportApproximationScale T delta)
      hT1 hβγ hrho (by omega) hL hpositive
    have hmajorant_le_decay :
        (∑ r ∈ Finset.range (reportRBound T beta rho),
          ∑ h ∈ Finset.range (reportHBound T alpha beta delta rho
            (reportApproximationScale T delta)),
            ∑ p ∈ primeWindow T alpha beta,
              ((p : ℝ)⁻¹) *
                badPairQWindowBrunMajorant
                  (reportApproximationScale T delta) r h p) ≤
          ∑ r ∈ Finset.range (reportRBound T beta rho),
            ∑ h ∈ Finset.range (reportHBound T alpha beta delta rho
              (reportApproximationScale T delta)),
              ∑ p ∈ primeWindow T alpha beta,
                ((p : ℝ)⁻¹) *
                  badPairQWindowBrunDecayMajorant
                    (reportApproximationScale T delta) r h p := by
      apply Finset.sum_le_sum
      intro r hrR
      apply Finset.sum_le_sum
      intro h hhH
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · by_cases hz : r = 0 ∨ h = 0
        · simp [badPairQWindowBrunMajorant, badPairQWindowBrunDecayMajorant, hz]
        · have hr : 0 < r := Nat.pos_of_ne_zero (fun hr0 ↦ hz (Or.inl hr0))
          have hh : 0 < h := Nat.pos_of_ne_zero (fun hh0 ↦ hz (Or.inr hh0))
          exact badPairQWindowBrunMajorant_le_decayMajorant hM4nat hr hh
            (Finset.mem_filter.mp hp).2.1.one_lt (hwidth p hp r hr)
      · positivity
    have hsumT' :
        (∑ r ∈ Finset.range (reportRBound T beta rho),
          ∑ h ∈ Finset.range (reportHBound T alpha beta delta rho
            (reportApproximationScale T delta)),
            ∑ p ∈ primeWindow T alpha beta,
              ((p : ℝ)⁻¹) *
                badPairQWindowBrunDecayMajorant
                  (reportApproximationScale T delta) r h p) ≤ bound T := by
      simpa [reportHAtReportScale] using hsumT
    exact hmajorant_le_decay.trans hsumT'
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun T ↦
      pairReciprocalWeight_nonneg
        (badPairsAtReportScale T alpha beta gamma delta rho))
  · filter_upwards [hT, hM, hsum'] with T hT1 hMT hsumT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hL : 0 < Real.rpow T alpha := Real.rpow_pos_of_pos hTpos _
    have hpositive : 0 < Real.rpow T delta / Real.rpow T alpha :=
      report_endpoint_ratio_pos hTpos
    exact (badPairWeight_le_brunTitchmarsh_majorant_sum_of_report_bounds
      T alpha beta gamma delta rho (reportApproximationScale T delta)
      hT1 hβγ hrho hMT hL hpositive).trans hsumT
  · exact hbound

/- The source-scale endpoint: the only remaining analytic input is an eventual upper bound for the
explicit triple sum.  The finite cover, all degenerate indices, and the final squeeze are handled
here without fixing `M`. -/
theorem tendsto_badPairWeight_zero_of_report_majorant
    {alpha beta gamma delta rho : ℝ} (bound : ℝ → ℝ)
    (hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T)
    (hM : ∀ᶠ T : ℝ in atTop, 1 < reportApproximationScale T delta)
    (hβγ : beta ≤ gamma) (hrho : 0 < rho)
    (hsum : ∀ᶠ T : ℝ in atTop,
      (∑ r ∈ Finset.range (reportRBound T beta rho),
        ∑ h ∈ Finset.range (reportHAtReportScale T alpha beta delta rho),
          ∑ p ∈ primeWindow T alpha beta,
            ((p : ℝ)⁻¹) *
              badPairQWindowBrunMajorant (reportApproximationScale T delta) r h p) ≤
        bound T)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    Tendsto
      (fun T ↦ pairReciprocalWeight
        (badPairsAtReportScale T alpha beta gamma delta rho))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun T ↦
      pairReciprocalWeight_nonneg
        (badPairsAtReportScale T alpha beta gamma delta rho))
  · filter_upwards [hT, hM, hsum] with T hT hM hsumT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hL : 0 < Real.rpow T alpha := Real.rpow_pos_of_pos hTpos _
    have hpositive : 0 < Real.rpow T delta / Real.rpow T alpha :=
      report_endpoint_ratio_pos hTpos
    have hupper := badPairWeight_le_brunTitchmarsh_majorant_sum_of_report_bounds
      T alpha beta gamma delta rho (reportApproximationScale T delta)
      hT hβγ hrho hM hL hpositive
    have hsumT' :
        (∑ r ∈ Finset.range (reportRBound T beta rho),
          ∑ h ∈ Finset.range (reportHBound T alpha beta delta rho
            (reportApproximationScale T delta)),
            ∑ p ∈ primeWindow T alpha beta,
              ((p : ℝ)⁻¹) *
                badPairQWindowBrunMajorant (reportApproximationScale T delta) r h p) ≤
          bound T := by
      simpa [reportHAtReportScale] using hsumT
    simpa [badPairsAtReportScale, badPairsWithScale] using hupper.trans hsumT'
  · exact hbound

/- The finite outer sum has no hidden analytic step: once the block estimate is supplied on the
 chosen ranges, `badPairWeight_le_parameter_sum_of_bounds` transports it to the whole bad family.
Keeping this theorem separate is useful when the eventual uniform estimate uses a different
majorant for the small and large `(r,h)` regimes. -/
theorem badPairWeight_le_brunTitchmarsh_parameter_sum
    (T α β γ δ rho : ℝ) (M R H : ℕ)
    (hcover : ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T α β γ δ rho M →
        ∃ r < R, ∃ h < H, isBadApprox rho M pq.1 pq.2 r h)
    (hblock : ∀ ⦃r h : ℕ⦄, r < R → h < H →
      pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range R, ∑ h ∈ Finset.range H,
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
  exact badPairWeight_le_parameter_sum_of_bounds T α β γ δ rho M R H hcover
    (fun r h ↦ ∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p) hblock

/- A source-parameter specialization: the finite cover is now discharged from the ordered prime
windows and the report's `r`/`h` endpoint inequalities, leaving only the positive-block Brun
majorant as an analytic input. -/
theorem badPairWeight_le_brunTitchmarsh_parameter_sum_of_ordered_windows
    (T α β γ δ rho : ℝ) (M H : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hH : ∀ ⦃r : ℕ⦄, r < reportRBound T β rho →
      (r : ℝ) * (Real.rpow T δ / Real.rpow T α) + 1 / (M : ℝ) < (H : ℝ))
    (hblock : ∀ ⦃r h : ℕ⦄,
      r < reportRBound T β rho → h < H →
      pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range (reportRBound T β rho), ∑ h ∈ Finset.range H,
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
  have hsubset := badPairs_subset_badPairBlocks_of_ordered_windows T α β γ δ rho M H
      hT hβγ hrho hM hL hH
  exact badPairWeight_le_brunTitchmarsh_parameter_sum T α β γ δ rho M
    (reportRBound T β rho) H
    (badPairs_cover_of_subset_badPairBlocks T α β γ δ rho M
      (reportRBound T β rho) H hsubset)
    hblock

theorem badPairWeight_le_brunTitchmarsh_parameter_sum_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α)
    (hblock : ∀ ⦃r h : ℕ⦄,
      r < reportRBound T β rho → h < reportHBound T α β δ rho M →
      pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range (reportRBound T β rho),
        ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
          ∑ p ∈ primeWindow T α β,
            ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p := by
  exact badPairWeight_le_brunTitchmarsh_parameter_sum_of_ordered_windows
    T α β γ δ rho M (reportHBound T α β δ rho M) hT hβγ hrho hM hL
    (by
      intro r hr
      exact reportHBound_condition hr hpositive) hblock

/- Report-scale version retaining the lower h cutoff forced by the complementary q-window.  This
is the form to use for the actual decay sum; replacing the conditional term by an unrestricted
sum would erase the exponential gain from the q-window's lower endpoint. -/
theorem badPairWeight_le_brunTitchmarsh_parameter_sum_of_report_bounds_lower_h
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM : 1 < M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range (reportRBound T β rho),
        ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
          if primeWindowHLower T β γ M r ≤ h then
            ∑ p ∈ primeWindow T α β,
              ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p
          else 0 := by
  have hsubset := badPairs_subset_badPairBlocks_of_report_bounds T α β γ δ rho M
      hT hβγ hrho hM hL hpositive
  apply badPairWeight_le_parameter_sum_of_bounds_lower_h T α β γ δ rho M
    (reportRBound T β rho) (reportHBound T α β δ rho M)
    hT (Nat.zero_lt_of_lt hM)
    (badPairs_cover_of_subset_badPairBlocks T α β γ δ rho M
      (reportRBound T β rho) (reportHBound T α β δ rho M) hsubset)
    (fun r h ↦ ∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p)
  intro r h hrR hlow hhH
  exact badPairBlockWeight_le_brunTitchmarsh_majorant_of_ordered_parameters
    T α β γ δ rho M r h hT hβγ hM

/- The decay-majorant form with the same lower cutoff.  Degenerate indices are handled by their
zero majorants; positive indices use the width estimate already proved above. -/
theorem badPairWeight_le_brunTitchmarsh_decay_majorant_sum_of_report_bounds_lower_h
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM4 : 4 ≤ M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α)
    (hwidth : ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      ∑ r ∈ Finset.range (reportRBound T β rho),
        ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
          if primeWindowHLower T β γ M r ≤ h then
            ∑ p ∈ primeWindow T α β,
              ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p
          else 0 := by
  have hsubset := badPairs_subset_badPairBlocks_of_report_bounds T α β γ δ rho M
      hT hβγ hrho (by omega) hL hpositive
  apply badPairWeight_le_parameter_sum_of_bounds_lower_h T α β γ δ rho M
    (reportRBound T β rho) (reportHBound T α β δ rho M)
    hT (by exact_mod_cast (show 0 < M by omega))
    (badPairs_cover_of_subset_badPairBlocks T α β γ δ rho M
      (reportRBound T β rho) (reportHBound T α β δ rho M) hsubset)
    (fun r h ↦ ∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p)
  intro r h hrR hlow hhH
  have hmajor := badPairBlockWeight_le_brunTitchmarsh_majorant_of_ordered_parameters
    T α β γ δ rho M r h hT hβγ (by omega)
  calc
    pairReciprocalWeight (badPairBlock T α β γ δ rho M r h) ≤
        ∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * badPairQWindowBrunMajorant M r h p := hmajor
    _ ≤ ∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M r h p := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · by_cases hr0 : r = 0
        · simp [badPairQWindowBrunMajorant, badPairQWindowBrunDecayMajorant, hr0]
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          by_cases hh0 : h = 0
          · simp [badPairQWindowBrunMajorant, badPairQWindowBrunDecayMajorant, hr0, hh0]
          · have hhpos : 0 < h := Nat.pos_of_ne_zero hh0
            exact badPairQWindowBrunMajorant_le_decayMajorant hM4 hrpos hhpos
              (Finset.mem_filter.mp hp).2.1.one_lt (hwidth p hp r hrpos)
      · positivity

/- Final squeeze using the filtered decay sum.  This wrapper is identical in purpose to the
unfiltered one above, but its analytic hypothesis now contains the q-window-implied lower h cutoff. -/
theorem tendsto_badPairWeight_zero_of_report_decay_majorant_lower_h
    {alpha beta gamma delta rho : ℝ} (bound : ℝ → ℝ)
    (hbeta : 0 ≤ beta) (hbetadelta : beta + delta < 1)
    (hβγ : beta ≤ gamma) (hrho : 0 < rho)
    (hsum : ∀ᶠ T : ℝ in atTop,
      (∑ r ∈ Finset.range (reportRBound T beta rho),
        ∑ h ∈ Finset.range (reportHAtReportScale T alpha beta delta rho),
          if primeWindowHLower T beta gamma
              (reportApproximationScale T delta) r ≤ h then
            ∑ p ∈ primeWindow T alpha beta,
              ((p : ℝ)⁻¹) *
                badPairQWindowBrunDecayMajorant
                  (reportApproximationScale T delta) r h p
          else 0) ≤ bound T)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    Tendsto
      (fun T ↦ pairReciprocalWeight
        (badPairsAtReportScale T alpha beta gamma delta rho))
      atTop (𝓝 0) := by
  have hdelta : delta < 1 := by linarith
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop _
  have hM : ∀ᶠ T : ℝ in atTop, 1 < reportApproximationScale T delta := by
    exact eventually_reportApproximationScale_gt_one hdelta
  have hM4 : ∀ᶠ T : ℝ in atTop, 4 ≤ (reportApproximationScale T delta : ℝ) :=
    eventually_reportApproximationScale_ge_four hdelta
  have hwidth : ∀ᶠ T : ℝ in atTop,
      ∀ p ∈ primeWindow T alpha beta, ∀ r : ℕ, 0 < r →
        2 * Real.log (p : ℝ) ≤ (r : ℝ) *
          (reportApproximationScale T delta : ℝ) := by
    exact eventually_primeWindow_width_of_reportApproximationScale hbeta hbetadelta
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun T ↦
      pairReciprocalWeight_nonneg
        (badPairsAtReportScale T alpha beta gamma delta rho))
  · filter_upwards [hT, hM, hM4, hwidth, hsum] with T hT1 hMT hM4T hwidthT hsumT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hL : 0 < Real.rpow T alpha := Real.rpow_pos_of_pos hTpos _
    have hpositive : 0 < Real.rpow T delta / Real.rpow T alpha :=
      report_endpoint_ratio_pos hTpos
    have hM4nat : 4 ≤ reportApproximationScale T delta := by exact_mod_cast hM4T
    have hupper := badPairWeight_le_brunTitchmarsh_decay_majorant_sum_of_report_bounds_lower_h
      T alpha beta gamma delta rho (reportApproximationScale T delta)
      hT1 hβγ hrho hM4nat hL hpositive
      (fun p hp r hr ↦ hwidthT p hp r hr)
    have hsumT' :
        (∑ r ∈ Finset.range (reportRBound T beta rho),
          ∑ h ∈ Finset.range (reportHBound T alpha beta delta rho
            (reportApproximationScale T delta)),
            if primeWindowHLower T beta gamma
                (reportApproximationScale T delta) r ≤ h then
              ∑ p ∈ primeWindow T alpha beta,
                ((p : ℝ)⁻¹) *
                  badPairQWindowBrunDecayMajorant
                    (reportApproximationScale T delta) r h p
            else 0) ≤ bound T := by
      simpa [reportHAtReportScale] using hsumT
    exact hupper.trans hsumT'
  · exact hbound

/- The analytic ranges normally depend on the main scale `T`.  This version packages that
dependence explicitly: after a uniform estimate for the displayed finite triple sum is supplied,
the squeeze to zero is completely formal. -/
theorem tendsto_badPairWeight_zero_of_brunTitchmarsh_parameter_sum
    {alpha beta gamma delta rho : ℝ} {M : ℕ}
    (R H : ℝ → ℕ) (bound : ℝ → ℝ)
    (hcover : ∀ T, ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairs T alpha beta gamma delta rho M →
        ∃ r < R T, ∃ h < H T, isBadApprox rho M pq.1 pq.2 r h)
    (hblock : ∀ T, ∀ ⦃r h : ℕ⦄, r < R T → h < H T →
      pairReciprocalWeight (badPairBlock T alpha beta gamma delta rho M r h) ≤
        ∑ p ∈ primeWindow T alpha beta,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p)
    (hsum : ∀ T,
      (∑ r ∈ Finset.range (R T), ∑ h ∈ Finset.range (H T),
        ∑ p ∈ primeWindow T alpha beta,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound M r h p) ≤ bound T)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    Tendsto
      (fun T ↦ pairReciprocalWeight (badPairs T alpha beta gamma delta rho M))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun T ↦
      pairReciprocalWeight_nonneg (badPairs T alpha beta gamma delta rho M))
  · exact Filter.Eventually.of_forall (fun T ↦
      (badPairWeight_le_brunTitchmarsh_parameter_sum
        T alpha beta gamma delta rho M (R T) (H T) (hcover T) (hblock T)).trans
        (hsum T))
  · exact hbound

/- The report's actual choice has `M = M(T)`, not a fixed natural number.  This wrapper keeps that
scale dependence in the statement, so the eventual analytic estimate cannot accidentally prove a
different fixed-`M` assertion. -/
theorem tendsto_badPairWeight_zero_of_brunTitchmarsh_parameter_sum_with_scale
    {alpha beta gamma delta rho : ℝ}
    (M R H : ℝ → ℕ) (bound : ℝ → ℝ)
    (hcover : ∀ T, ∀ ⦃pq : ℕ × ℕ⦄,
      pq ∈ badPairsWithScale T alpha beta gamma delta rho M →
        ∃ r < R T, ∃ h < H T, isBadApprox (rho) (M T) pq.1 pq.2 r h)
    (hblock : ∀ T, ∀ ⦃r h : ℕ⦄, r < R T → h < H T →
      pairReciprocalWeight
          (badPairBlock T alpha beta gamma delta rho (M T) r h) ≤
        ∑ p ∈ primeWindow T alpha beta,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound (M T) r h p)
    (hsum : ∀ T,
      (∑ r ∈ Finset.range (R T), ∑ h ∈ Finset.range (H T),
        ∑ p ∈ primeWindow T alpha beta,
          ((p : ℝ)⁻¹) * badPairQWindowBrunBound (M T) r h p) ≤ bound T)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    Tendsto
      (fun T ↦ pairReciprocalWeight
        (badPairsWithScale T alpha beta gamma delta rho M))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun T ↦
      pairReciprocalWeight_nonneg
        (badPairsWithScale T alpha beta gamma delta rho M))
  · exact Filter.Eventually.of_forall (fun T ↦ by
      have hparam := badPairWeight_le_brunTitchmarsh_parameter_sum
        T alpha beta gamma delta rho (M T) (R T) (H T)
        (by
          intro pq hpq
          exact hcover T (by simpa [badPairsWithScale] using hpq))
        (hblock T)
      simpa [badPairsWithScale] using hparam.trans (hsum T))
  · exact hbound

/- The first term of the Brun majorant has no dependence on `r` except through the allowed
`p`-dependent range `r < R p`.  This finite identity records the intended change of summation
order.  It is the algebraic interface needed before inserting `R p = ceil (4 log p / rho)`;
no asymptotic estimate is hidden here. -/
theorem pDependent_main_term_reorder
    (s : Finset ℕ) (R : ℕ → ℕ) (H M : ℕ) (hM : 0 < M) :
    (∑ p ∈ s, ∑ _r ∈ Finset.range (R p),
      ∑ h ∈ Finset.Icc 1 H,
        ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) =
      (16 / (M : ℝ)) *
        ∑ p ∈ s, ((p : ℝ)⁻¹) * (R p : ℝ) *
          (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
  classical
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  calc
    (∑ p ∈ s, ∑ r ∈ Finset.range (R p),
        ∑ h ∈ Finset.Icc 1 H,
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) =
        ∑ p ∈ s, (R p : ℝ) *
          (∑ h ∈ Finset.Icc 1 H,
            ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ = ∑ p ∈ s, (16 / (M : ℝ)) * ((p : ℝ)⁻¹) * (R p : ℝ) *
          (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.mul_sum]
      have hsum :
          (∑ h ∈ Finset.Icc 1 H, 16 / ((h : ℝ) * (M : ℝ))) =
            (16 / (M : ℝ)) * (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        have hhpos : (h : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1))
        field_simp [hhpos, hMreal]
      rw [hsum]
      ring
    _ = (16 / (M : ℝ)) *
          ∑ p ∈ s, ((p : ℝ)⁻¹) * (R p : ℝ) *
            (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/- The denominator count itself is logarithmic.  This is the finite weighted estimate that
turns the p-dependent range into the von Mangoldt-friendly weight `log p / p`. -/
theorem sum_reciprocal_mul_denominatorCutoff_le_log_weight
    (s : Finset ℕ) (rho : ℝ) (hrho : 0 < rho)
    (hprime : ∀ p ∈ s, 1 < p) :
    (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) ≤
      (4 / rho) *
          (∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)) +
        ∑ p ∈ s, ((p : ℝ)⁻¹) := by
  classical
  calc
    (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) ≤
        ∑ p ∈ s,
          ((4 / rho) * (Real.log (p : ℝ) / (p : ℝ)) +
            ((p : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hcut := denominatorCutoff_cast_lt_log (hprime p hp) hrho
      have hpnonneg : 0 ≤ (p : ℝ)⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hcut) hpnonneg
      calc
        ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ) ≤
            ((p : ℝ)⁻¹) * (4 * Real.log (p : ℝ) / rho + 1) := hmul
        _ = (4 / rho) * (Real.log (p : ℝ) / (p : ℝ)) +
              ((p : ℝ)⁻¹) := by
          have hp0 : (p : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hprime p hp)))
          have hrho0 : rho ≠ 0 := ne_of_gt hrho
          field_simp [hp0, hrho0]
    _ = (4 / rho) *
          (∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)) +
        ∑ p ∈ s, ((p : ℝ)⁻¹) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/- After the finite reordering, the first Brun--Titchmarsh term is controlled by exactly the
two prime weights for which the upstream Mertens interface is available. -/
theorem pDependent_main_term_le_log_weight
    (s : Finset ℕ) (rho : ℝ) (M H : ℕ)
    (hrho : 0 < rho) (hM : 0 < M)
    (hprime : ∀ p ∈ s, 1 < p) :
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.Icc 1 H,
        ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) ≤
      (16 / (M : ℝ)) *
        ((4 / rho) * (∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)) +
          ∑ p ∈ s, ((p : ℝ)⁻¹)) *
        (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
  have hrewrite := pDependent_main_term_reorder
    s (fun p ↦ denominatorCutoff p rho) H M hM
  have hden := sum_reciprocal_mul_denominatorCutoff_le_log_weight
    s rho hrho hprime
  calc
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.Icc 1 H,
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) =
        (16 / (M : ℝ)) *
          (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
          (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
      calc
        _ = (16 / (M : ℝ)) *
            ∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ) *
              (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := hrewrite
        _ = (16 / (M : ℝ)) *
            (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
              (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
          rw [mul_assoc, Finset.sum_mul]
    _ ≤ (16 / (M : ℝ)) *
          ((4 / rho) * (∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)) +
            ∑ p ∈ s, ((p : ℝ)⁻¹)) *
          (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hden (by positivity)
      · positivity

/- The finite split uses `range H`, whereas the reciprocal-width estimate is stated on
`Icc 1 H`.  The missing `h=0` term is exactly zero; deleting it leaves a subset of `Icc 1 H`,
so the comparison is purely order-theoretic and does not use any asymptotics. -/
theorem pDependent_main_range_le_Icc
    (s : Finset ℕ) (rho : ℝ) (M H : ℕ) :
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) ≤
      (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.Icc 1 H,
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro r hr
  by_cases hH : H = 0
  · subst H
    simp
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    let f : ℕ → ℝ := fun h ↦
      ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))
    have hzero : f 0 = 0 := by
      simp [f]
    have hmem0 : 0 ∈ Finset.range H := Finset.mem_range.mpr hHpos
    have hsum_erase :
        (∑ h ∈ (Finset.range H).erase 0, f h) + f 0 =
          ∑ h ∈ Finset.range H, f h :=
      Finset.sum_erase_add (Finset.range H) f hmem0
    have hsubset : (Finset.range H).erase 0 ⊆ Finset.Icc 1 H := by
      intro h hh
      have hh_range : h ∈ Finset.range H := Finset.erase_subset 0 _ hh
      have hh_ne : h ≠ 0 := by
        intro hh0
        subst h
        exact (Finset.mem_erase.mp hh).1 rfl
      have hh_pos : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr hh_ne
      exact Finset.mem_Icc.mpr ⟨hh_pos, Finset.mem_range.mp hh_range |>.le⟩
    have hnonneg : ∀ h ∈ Finset.Icc 1 H, h ∉ (Finset.range H).erase 0 →
        0 ≤ f h := by
      intro h hh hnot
      positivity
    have hineq :
        (∑ h ∈ (Finset.range H).erase 0, f h) ≤
          ∑ h ∈ Finset.Icc 1 H, f h :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    have hleft : (∑ h ∈ Finset.range H, f h) =
        ∑ h ∈ (Finset.range H).erase 0, f h := by
      rw [← hsum_erase, hzero, add_zero]
    rw [hleft]
    simpa [f] using hineq

/- Prime terms of the von Mangoldt Mertens sum are exactly `log p / p`.  This one-sided
inequality is enough for the p-dependent main term and deliberately avoids a prime-power
subtraction argument. -/
theorem sum_log_prime_div_le_mertens
    {s : Finset ℕ} {N : ℕ}
    (hsubset : s ⊆ Finset.Icc 1 N)
    (hprime : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)) ≤
      PrimitiveSetsAboveX.mertensPartialSum N := by
  classical
  calc
    (∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)) =
        ∑ p ∈ s, ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (hprime p hp)]
    _ ≤ ∑ p ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp _
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    _ = PrimitiveSetsAboveX.mertensPartialSum N := by
      rfl

/- An elementary alternative to the von Mangoldt bridge, ported from the verified
LongGapsBetweenPrimes development.  It uses only the Chebyshev theta bound and the divisor
identity, so the logarithmically weighted prime sum has an explicit `log 4` constant. -/
lemma sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by
  have hfilter : N.primesLE.filter (fun p ↦ p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1.2, h.2, hn.ne'⟩,
      fun h => ⟨⟨(Nat.le_of_dvd hn h.2.1).trans hnN, h.1⟩, h.2.1⟩⟩
  rw [← Finset.sum_filter, hfilter, ← Real.log_prod (fun p hp ↦
    Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp ↦
      Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hp).1.pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem sum_prime_log_div_le_log4 {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount (p : ℕ) (_hp : p ∈ N.primesLE) :
      (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
      (Nat.sub_one_lt_floor ((N : ℝ) / p)).le
  have hsum : (∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.range N,
          if p ∣ n + 1 then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Nat.card_multiples N p, ← Finset.sum_boole]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = ∑ n ∈ Finset.range N, ∑ p ∈ N.primesLE,
          if p ∣ n + 1 then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
        exact (sum_log_prime_divisors_le_log (by omega : 0 < n + 1) hnN).trans
          (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log N := by simp
  have hlower : (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / p) -
      Chebyshev.theta N ≤ (N : ℝ) * Real.log N := by
    apply le_trans _ hsum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_right (hcount p hp)
      (Nat.mem_primesLE.mp hp).2.log_pos.le
    calc
      (N : ℝ) * (Real.log p / p) - Real.log p =
        ((N : ℝ) / p - 1) * Real.log p := by ring
      _ ≤ _ := h
  have htheta := Chebyshev.theta_le_log4_mul_x hNr.le
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/- A reusable high-prime cutoff corollary.  It keeps the logarithmic weight until the last
   step, so a tail beginning at `L` pays only the factor `1 / log L` rather than the full
   harmonic loss.  This is the finite estimate needed in the terminal-prime branch of the
   Erdős-878 summatory decomposition. -/
theorem reciprocal_prime_sum_le_log4_of_lower_endpoint
    {L N : ℕ} (hL : 1 < L) (hN : 1 ≤ N)
    {s : Finset ℕ}
    (hsubset : s ⊆ N.primesLE)
    (hge : ∀ p ∈ s, L ≤ p) :
    (∑ p ∈ s, ((p : ℝ)⁻¹)) ≤
      (Real.log (N : ℝ) + Real.log 4) / Real.log (L : ℝ) := by
  classical
  have hLpos : 0 < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have hlogL : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast hL)
  have hterm : ∀ p ∈ s,
      ((p : ℝ)⁻¹) ≤ (Real.log (p : ℝ) / (p : ℝ)) / Real.log (L : ℝ) := by
    intro p hp
    have hpprime : Nat.Prime p := (Nat.mem_primesLE.mp (hsubset hp)).2
    have hppos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hLp : (L : ℝ) ≤ (p : ℝ) := by exact_mod_cast hge p hp
    have hlogmono : Real.log (L : ℝ) ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (L : ℝ) ∈ Set.Ioi 0 by exact hLpos)
        (show (p : ℝ) ∈ Set.Ioi 0 by exact hppos) hLp
    apply (le_div_iff₀ hlogL).2
    calc
      (p : ℝ)⁻¹ * Real.log (L : ℝ) =
          Real.log (L : ℝ) * (p : ℝ)⁻¹ := by ring
      _ ≤ Real.log (p : ℝ) * (p : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hlogmono (inv_nonneg.mpr hppos.le)
      _ = Real.log (p : ℝ) / (p : ℝ) := by ring
  calc
    (∑ p ∈ s, ((p : ℝ)⁻¹)) ≤
        ∑ p ∈ s, (Real.log (p : ℝ) / (p : ℝ)) / Real.log (L : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p hp
    _ ≤ ∑ p ∈ N.primesLE,
        (Real.log (p : ℝ) / (p : ℝ)) / Real.log (L : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp _
      exact div_nonneg (by positivity) hlogL.le
    _ = (∑ p ∈ N.primesLE, Real.log (p : ℝ) / (p : ℝ)) /
          Real.log (L : ℝ) := by
      rw [Finset.sum_div]
    _ ≤ (Real.log (N : ℝ) + Real.log 4) / Real.log (L : ℝ) := by
      exact div_le_div_of_nonneg_right (sum_prime_log_div_le_log4 hN) hlogL.le

theorem primeWindow_log_weight_le_log4
    {T a b : ℝ} (hN : 1 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b,
      Real.log (p : ℝ) / (p : ℝ)) ≤
      Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + Real.log 4 := by
  let N : ℕ := Nat.floor (Real.exp (Real.rpow T b))
  have hsum := sum_prime_log_div_le_log4 (N := N) hN
  have hsubset : primeWindow T a b ⊆ N.primesLE := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hp'.1).2, hp'.2.1⟩
  have hnonneg : ∀ p ∈ N.primesLE, p ∉ primeWindow T a b →
      0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp _
    have hpprime := (Nat.mem_primesLE.mp hp).2
    positivity
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  simpa [N] using hsub.trans hsum

theorem pDependent_main_term_le_log4_mertens
    {T a b rho : ℝ} (M H : ℕ)
    (hT : 0 < T) (hrho : 0 < rho) (hM : 0 < M)
    (hN : 1 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b,
      ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.Icc 1 H,
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) ≤
      (16 / (M : ℝ)) *
        ((4 / rho) *
            (Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + Real.log 4) +
          PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T b))) / Real.rpow T a) *
        (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
  have hprime : ∀ p ∈ primeWindow T a b, 1 < p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.one_lt
  have hmain := pDependent_main_term_le_log_weight
    (primeWindow T a b) rho M H hrho hM hprime
  have hlog4 := primeWindow_log_weight_le_log4 (T := T) (a := a) (b := b) hN
  have hrec := primeWindow_reciprocal_le_mertens (T := T) (a := a) (b := b) hT
  have hcoef : 0 ≤ (4 / rho : ℝ) := by positivity
  have hD :
      (4 / rho) * (∑ p ∈ primeWindow T a b,
        Real.log (p : ℝ) / (p : ℝ)) +
          ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) ≤
        (4 / rho) *
            (Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + Real.log 4) +
          PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T b))) / Real.rpow T a := by
    exact add_le_add (mul_le_mul_of_nonneg_left hlog4 hcoef) hrec
  exact hmain.trans (by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hD (by positivity)
    · positivity)

theorem primeWindow_log_weight_le_mertens
    {T a b : ℝ} (_hT : 0 < T) :
    (∑ p ∈ primeWindow T a b,
      Real.log (p : ℝ) / (p : ℝ)) ≤
      PrimitiveSetsAboveX.mertensPartialSum
        (Nat.floor (Real.exp (Real.rpow T b))) := by
  apply sum_log_prime_div_le_mertens
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpPrime : Nat.Prime p := hp'.2.1
    have hpOne : 1 ≤ p := hpPrime.one_lt.le
    have hpUpper : p ≤ Nat.floor (Real.exp (Real.rpow T b)) :=
      (Finset.mem_Icc.mp hp'.1).2
    exact Finset.mem_Icc.mpr ⟨hpOne, hpUpper⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1

/- The same bridge with the logarithmic prime weight already present in the Mertens sum.  This is
the useful form for the p-dependent cutoff, where the inner r-sum contributes a factor of
`log p` rather than a uniform interval length. -/
theorem primeWindow_log_weight_le_mertens_add_constant
    {T a b C : ℝ} (hT : 0 < T) (_hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b,
      Real.log (p : ℝ) / (p : ℝ)) ≤
      Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C := by
  have hbase := primeWindow_log_weight_le_mertens (T := T) (a := a) (b := b) hT
  have hdiff :
      PrimitiveSetsAboveX.mertensPartialSum (Nat.floor (Real.exp (Real.rpow T b))) -
          Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) ≤ C := by
    exact le_trans (le_abs_self _) (hMertens hN)
  have hupper :
      PrimitiveSetsAboveX.mertensPartialSum (Nat.floor (Real.exp (Real.rpow T b))) ≤
        Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C := by
    linarith
  exact hbase.trans hupper

theorem primeWindow_log_weight_le_mertens_default
    {T a b : ℝ} (hT : 0 < T)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    ∃ C : ℝ, 0 < C ∧
      (∑ p ∈ primeWindow T a b,
        Real.log (p : ℝ) / (p : ℝ)) ≤
        Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) + C := by
  obtain ⟨C, hC, hMertens⟩ := Upstream.vonMangoldt_mertens_bounded_error
  exact ⟨C, hC,
    primeWindow_log_weight_le_mertens_add_constant hT hC hMertens hN⟩

theorem primeWindow_log_weight_le_rpow_add_constant
    {T a b C : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b,
      Real.log (p : ℝ) / (p : ℝ)) ≤
      Real.rpow T b + C := by
  have hbase := primeWindow_log_weight_le_mertens_add_constant
    (T := T) (a := a) (b := b) hT hC hMertens hN
  have hNpos : 0 < (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hN)
  have hlog : Real.log (Nat.floor (Real.exp (Real.rpow T b)) : ℝ) ≤ Real.rpow T b := by
    apply (Real.log_le_iff_le_exp hNpos).2
    exact Nat.floor_le (Real.exp_nonneg _)
  exact hbase.trans (by simpa [add_comm] using add_le_add_right hlog C)

/- Specialization to a prime window.  The only arithmetic input is the one-sided prime-term
bound for the von Mangoldt Mertens sum and the reciprocal-window bridge proved above. -/
theorem pDependent_main_term_le_mertens
    {T a b rho : ℝ} (M H : ℕ)
    (hT : 0 < T) (hrho : 0 < rho) (hM : 0 < M) :
    (∑ p ∈ primeWindow T a b,
      ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.Icc 1 H,
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) ≤
      (16 / (M : ℝ)) *
        ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T b))) +
          PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T b))) / Real.rpow T a) *
        (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
  have hprime : ∀ p ∈ primeWindow T a b, 1 < p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.one_lt
  have hmain := pDependent_main_term_le_log_weight
    (primeWindow T a b) rho M H hrho hM hprime
  have hlog := primeWindow_log_weight_le_mertens (T := T) (a := a) (b := b) hT
  have hrec := primeWindow_reciprocal_le_mertens (T := T) (a := a) (b := b) hT
  have hcoef : 0 ≤ (4 / rho : ℝ) := by positivity
  have hD :
      (4 / rho) * (∑ p ∈ primeWindow T a b,
        Real.log (p : ℝ) / (p : ℝ)) +
          ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) ≤
        (4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T b))) +
          PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T b))) / Real.rpow T a := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hlog hcoef) hrec
  exact hmain.trans (by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hD (by positivity)
    · positivity)

/- Floor-free power form of the preceding estimate.  This is the form used when the eventual
scale bounds for `M` and the harmonic h-sum are supplied separately. -/
theorem pDependent_main_term_le_rpow_mertens
    {T a b rho C : ℝ} (M H : ℕ)
    (hT : 0 < T) (hrho : 0 < rho) (hM : 0 < M) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b,
      ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.Icc 1 H,
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) ≤
      (16 / (M : ℝ)) *
        ((4 / rho) * (Real.rpow T b + C) +
          (Real.rpow T b + C) / Real.rpow T a) *
      (∑ h ∈ Finset.Icc 1 H, ((h : ℝ)⁻¹)) := by
  have hmain := pDependent_main_term_le_log_weight
    (primeWindow T a b) rho M H hrho hM (by
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1.one_lt)
  have hlog := primeWindow_log_weight_le_rpow_add_constant
    (T := T) (a := a) (b := b) hT hC hMertens hN
  have hrec := primeWindow_reciprocal_le_rpow_add_constant
    (T := T) (a := a) (b := b) hT hC hMertens hN
  have hcoef : 0 ≤ (4 / rho : ℝ) := by positivity
  have hD :
      (4 / rho) * (∑ p ∈ primeWindow T a b,
        Real.log (p : ℝ) / (p : ℝ)) +
          ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) ≤
        (4 / rho) * (Real.rpow T b + C) +
          (Real.rpow T b + C) / Real.rpow T a := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hlog hcoef) hrec
  exact hmain.trans (by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hD (by positivity)
    · positivity)

/- The cutoff-weighted prime window itself has the same floor-free power bound as the main
term.  This is the outer factor needed by the exponential-cube gate. -/
theorem primeWindow_cutoff_weight_le_rpow_mertens
    {T a b rho C : ℝ} (hT : 0 < T) (hrho : 0 < rho) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C)
    (hN : 2 ≤ Nat.floor (Real.exp (Real.rpow T b))) :
    (∑ p ∈ primeWindow T a b,
      ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) ≤
      (4 / rho) * (Real.rpow T b + C) +
        (Real.rpow T b + C) / Real.rpow T a := by
  have hprime : ∀ p ∈ primeWindow T a b, 1 < p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.one_lt
  have hden := sum_reciprocal_mul_denominatorCutoff_le_log_weight
    (primeWindow T a b) rho hrho hprime
  have hlog := primeWindow_log_weight_le_rpow_add_constant
    (T := T) (a := a) (b := b) hT hC hMertens hN
  have hrec := primeWindow_reciprocal_le_rpow_add_constant
    (T := T) (a := a) (b := b) hT hC hMertens hN
  have hcoef : 0 ≤ (4 / rho : ℝ) := by positivity
  have hD :
      (4 / rho) * (∑ p ∈ primeWindow T a b,
        Real.log (p : ℝ) / (p : ℝ)) +
          ∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹) ≤
        (4 / rho) * (Real.rpow T b + C) +
          (Real.rpow T b + C) / Real.rpow T a := by
    exact add_le_add (mul_le_mul_of_nonneg_left hlog hcoef) hrec
  exact hden.trans hD

/- Mathlib's exponential-vs-power limit, composed with a positive real-power scale.  The
exponent `s` is arbitrary (in particular it covers the cubic factor in the Brun error term). -/
theorem tendsto_rpow_mul_exp_neg_mul_rpow
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℝ) :
    Tendsto (fun T : ℝ ↦ T ^ (a * s) * Real.exp (-b * T ^ a))
      atTop (𝓝 0) := by
  have hcomp :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).comp
      (tendsto_rpow_atTop ha)
  apply Filter.Tendsto.congr' (f₁ := fun T : ℝ ↦
      (T ^ a) ^ s * Real.exp (-b * T ^ a))
    (f₂ := fun T : ℝ ↦ T ^ (a * s) * Real.exp (-b * T ^ a))
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      rw [Real.rpow_mul hT]) hcomp

/- A direct-exponent form of the preceding kernel, convenient when a finite sum has already been
bounded by `T^c * exp (-b * T^a)`. -/
theorem tendsto_rpow_mul_exp_neg_mul_rpow_of_exponent
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun T : ℝ ↦ T ^ c * Real.exp (-b * T ^ a))
      atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_rpow ha hb (c / a)
  have ha0 : a ≠ 0 := ne_of_gt ha
  apply Filter.Tendsto.congr' (f₁ := fun T : ℝ ↦
      T ^ (a * (c / a)) * Real.exp (-b * T ^ a))
    (f₂ := fun T : ℝ ↦ T ^ c * Real.exp (-b * T ^ a))
    (Filter.Eventually.of_forall (fun T ↦ by
      field_simp [ha0])) h

/- The cubic factor occurring in the Brun error is still dominated by a fixed power of the
underlying scale.  This wrapper makes that domination explicit and keeps the eventual estimate
available for later finite parameter bounds. -/
theorem tendsto_exp_neg_mul_rpow_mul_one_add_rpow_cube
    {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) :
    Tendsto (fun T : ℝ ↦
      Real.exp (-b * T ^ a) * (1 + T ^ s) ^ 3) atTop (𝓝 0) := by
  have hkernel := tendsto_rpow_mul_exp_neg_mul_rpow_of_exponent
    (a := a) (b := b) (c := 3 * s) ha hb
  have hscaled : Tendsto (fun T : ℝ ↦
      8 * (T ^ (3 * s) * Real.exp (-b * T ^ a))) atTop (𝓝 0) := by
    simpa [mul_assoc] using (tendsto_const_nhds.mul hkernel)
  have hupper : ∀ᶠ T : ℝ in atTop,
      Real.exp (-b * T ^ a) * (1 + T ^ s) ^ 3 ≤
        8 * (T ^ (3 * s) * Real.exp (-b * T ^ a)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hTs : 1 ≤ T ^ s := Real.one_le_rpow hT hs
    have hsum : 1 + T ^ s ≤ 2 * T ^ s := by linarith
    have hpow3 : (T ^ s) ^ 3 = T ^ (3 * s) := by
      calc
        (T ^ s) ^ 3 = T ^ (s * (3 : ℝ)) :=
          (Real.rpow_mul_natCast (by linarith : 0 ≤ T) s 3).symm
        _ = T ^ (3 * s) := by
          congr 1
          ring
    have hpoly : (1 + T ^ s) ^ 3 ≤ 8 * T ^ (3 * s) := by
      calc
        (1 + T ^ s) ^ 3 ≤ (2 * T ^ s) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hsum 3
        _ = 8 * (T ^ s) ^ 3 := by ring
        _ = 8 * T ^ (3 * s) := by rw [hpow3]
    calc
      Real.exp (-b * T ^ a) * (1 + T ^ s) ^ 3 ≤
          Real.exp (-b * T ^ a) * (8 * T ^ (3 * s)) :=
        mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
      _ = 8 * (T ^ (3 * s) * Real.exp (-b * T ^ a)) := by ring
  have hnonneg : ∀ᶠ T : ℝ in atTop,
      0 ≤ Real.exp (-b * T ^ a) * (1 + T ^ s) ^ 3 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    positivity
  exact squeeze_zero' hnonneg hupper hscaled

/- A reusable final analytic gate.  It says that a weighted finite box is negligible whenever its
outer weight `W` and h-scale `H` have polynomial bounds; the exponential factor then dominates
the resulting fixed power.  The report-specific work is reduced to proving the two eventual
polynomial hypotheses. -/
theorem tendsto_weight_mul_exp_neg_mul_cube_of_polynomial_bounds
    {a b c s t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (W H : ℝ → ℝ)
    (hW : ∀ᶠ T : ℝ in atTop, 0 ≤ W T ∧ W T ≤ T ^ c)
    (hH : ∀ᶠ T : ℝ in atTop, 0 ≤ H T ∧ H T * T ^ t ≤ T ^ s) :
    Tendsto (fun T : ℝ ↦
      W T * H T * (6 * Real.exp (-b * T ^ a) *
        (1 + (H T * T ^ t) / 2) ^ 3)) atTop (𝓝 0) := by
  have hkernel := tendsto_rpow_mul_exp_neg_mul_rpow_of_exponent
    (a := a) (b := b) (c := c + 4 * s) ha hb
  have hscaled : Tendsto (fun T : ℝ ↦
      48 * (T ^ (c + 4 * s) * Real.exp (-b * T ^ a))) atTop (𝓝 0) := by
    simpa [mul_assoc] using (tendsto_const_nhds.mul hkernel)
  have hnonneg : ∀ᶠ T : ℝ in atTop,
      0 ≤ W T * H T * (6 * Real.exp (-b * T ^ a) *
        (1 + (H T * T ^ t) / 2) ^ 3) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hW, hH] with T hT hWT hHT
    have hTnonneg : 0 ≤ T := le_trans (by norm_num) hT
    have hHt0 : 0 ≤ H T * T ^ t :=
      mul_nonneg hHT.1 (Real.rpow_nonneg hTnonneg _)
    have hpoly : 0 ≤ 1 + (H T * T ^ t) / 2 := by linarith
    exact mul_nonneg (mul_nonneg hWT.1 hHT.1)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (pow_nonneg hpoly 3))
  have hupper : ∀ᶠ T : ℝ in atTop,
      W T * H T * (6 * Real.exp (-b * T ^ a) *
        (1 + (H T * T ^ t) / 2) ^ 3) ≤
      48 * (T ^ (c + 4 * s) * Real.exp (-b * T ^ a)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hW, hH] with T hT hWT hHT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hTnonneg : 0 ≤ T := hTpos.le
    have hTt : 1 ≤ T ^ t := Real.one_le_rpow hT ht
    have hHle : H T ≤ H T * T ^ t := by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hTt hHT.1)
    have hHpow : H T ≤ T ^ s := hHle.trans hHT.2
    have hWH : W T * H T ≤ T ^ c * T ^ s := by
      exact (mul_le_mul hWT.2 hHpow hHT.1 (by positivity))
    have hWH0 : 0 ≤ W T * H T := mul_nonneg hWT.1 hHT.1
    have hsum : 1 + (H T * T ^ t) / 2 ≤ 2 * T ^ s := by
      have hTs : 1 ≤ T ^ s := Real.one_le_rpow hT hs
      linarith [hHT.2]
    have hpoly : (1 + (H T * T ^ t) / 2) ^ 3 ≤ 8 * T ^ (3 * s) := by
      calc
        (1 + (H T * T ^ t) / 2) ^ 3 ≤ (2 * T ^ s) ^ 3 :=
          pow_le_pow_left₀ (by linarith) hsum 3
        _ = 8 * (T ^ s) ^ 3 := by ring
        _ = 8 * T ^ (3 * s) := by
          have hpow3 : (T ^ s) ^ 3 = T ^ (s * (3 : ℝ)) :=
            (Real.rpow_mul_natCast hTnonneg s 3).symm
          rw [hpow3]
          congr 1
          ring_nf
    have hexp0 : 0 ≤ Real.exp (-b * T ^ a) := (Real.exp_pos _).le
    have hleft : W T * H T *
          (6 * Real.exp (-b * T ^ a) *
            (1 + (H T * T ^ t) / 2) ^ 3) ≤
        (T ^ c * T ^ s) * (6 * Real.exp (-b * T ^ a) *
          (8 * T ^ (3 * s))) := by
      calc
        W T * H T * (6 * Real.exp (-b * T ^ a) *
            (1 + (H T * T ^ t) / 2) ^ 3) =
            (W T * H T) * (6 * Real.exp (-b * T ^ a)) *
              (1 + (H T * T ^ t) / 2) ^ 3 := by ring
        _ ≤ (T ^ c * T ^ s) * (6 * Real.exp (-b * T ^ a)) *
              (1 + (H T * T ^ t) / 2) ^ 3 := by
          have hHt0 : 0 ≤ H T * T ^ t :=
            mul_nonneg hHT.1 (Real.rpow_nonneg hTnonneg _)
          have hbase0 : 0 ≤ 1 + (H T * T ^ t) / 2 := by linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hWH (by positivity))
            (pow_nonneg hbase0 3)
        _ ≤ (T ^ c * T ^ s) * (6 * Real.exp (-b * T ^ a)) *
              (8 * T ^ (3 * s)) := by
          exact mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ = (T ^ c * T ^ s) * (6 * Real.exp (-b * T ^ a) *
              (8 * T ^ (3 * s))) := by ring
    calc
      W T * H T * (6 * Real.exp (-b * T ^ a) *
          (1 + (H T * T ^ t) / 2) ^ 3) ≤
        (T ^ c * T ^ s) * (6 * Real.exp (-b * T ^ a) *
          (8 * T ^ (3 * s))) := hleft
      _ = 48 * ((T ^ c * T ^ s) * T ^ (3 * s) *
          Real.exp (-b * T ^ a)) := by ring
      _ = 48 * (T ^ (c + s) * T ^ (3 * s) *
          Real.exp (-b * T ^ a)) := by
        rw [Real.rpow_add hTpos c s]
      _ = 48 * (T ^ ((c + s) + (3 * s)) *
          Real.exp (-b * T ^ a)) := by
        rw [Real.rpow_add hTpos (c + s) (3 * s)]
      _ = 48 * (T ^ (c + 4 * s) * Real.exp (-b * T ^ a)) := by
        congr 2
        ring_nf
  exact squeeze_zero' hnonneg hupper hscaled

/- The part of the Brun majorant carrying the exponential sieve error, separated from the
reciprocal-width main term.  The same zero convention as the full majorant keeps all finite sums
well-defined at `r=0` and `h=0`. -/
def badPairQWindowBrunDecayError (_M r h p : ℕ) : ℝ :=
  if r = 0 ∨ h = 0 then 0 else
    6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
      (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3

/- If the logarithmic centre `x=(h/r) log p` is trapped between explicit nonnegative bounds,
the error term is bounded by the corresponding exponential at the lower endpoint and cubic
polynomial at the upper endpoint.  This is the pointwise analytic interface used by the final
parameter-sum estimate. -/
theorem badPairQWindowBrunDecayError_le_of_bounds
    {M r h p : ℕ} {L U : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hL0 : 0 ≤ L) (hU0 : 0 ≤ U)
    (hL : L ≤ ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ))
    (hU : ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) ≤ U) :
    badPairQWindowBrunDecayError M r h p ≤
      6 * Real.exp (-L / 4) * (1 + U / 2) ^ 3 := by
  have hbaseL : 0 ≤ 1 +
      (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2 := by
    linarith
  have hbaseU : 0 ≤ 1 + U / 2 := by linarith
  have hpoly :
      (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3 ≤
        (1 + U / 2) ^ 3 := by
    apply pow_le_pow_left₀ hbaseL
    linarith
  have hexp :
      Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) ≤
        Real.exp (-L / 4) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hleft :
      6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) ≤
        6 * Real.exp (-L / 4) := by
    exact mul_le_mul_of_nonneg_left hexp (by norm_num)
  simp [badPairQWindowBrunDecayError, Nat.ne_of_gt hr, Nat.ne_of_gt hh]
  calc
    6 * Real.exp (-(((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 4) *
        (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3 ≤
      6 * Real.exp (-L / 4) *
        (1 + (((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ)) / 2) ^ 3 :=
      mul_le_mul_of_nonneg_right hleft (by positivity)
    _ ≤ 6 * Real.exp (-L / 4) * (1 + U / 2) ^ 3 :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)

/- The abstract bounds above can be obtained directly on a prime window.  This theorem keeps
the scale hypotheses explicit: the lower h-cutoff supplies the exponential scale, while the
finite h-range and the upper p-window endpoint supply the cubic scale. -/
theorem badPairQWindowBrunDecayError_le_of_prime_window_bounds
    {T α β γ : ℝ} {M r h p H : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M)
    (hp : p ∈ primeWindow T α β) (hr : 0 < r) (hh : 0 < h)
    (hhH : h < H)
    (hlow : primeWindowHLower T β γ M r ≤ h)
    (hwidth : 2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ))
    (hpower : 1 ≤ Real.rpow T (α + γ - β)) :
    badPairQWindowBrunDecayError M r h p ≤
      6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
        (1 + ((H : ℝ) * Real.rpow T β) / 2) ^ 3 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hlogpos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hloglower : Real.rpow T α < Real.log (p : ℝ) :=
    (primeWindow_log_bounds hp hpPrime.pos).1
  have hlogupper : Real.log (p : ℝ) ≤ Real.rpow T β :=
    (primeWindow_log_bounds hp hpPrime.pos).2
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hdenpos : 0 < (r : ℝ) * (M : ℝ) := mul_pos hrreal hMreal
  have hceil :
      (r : ℝ) * (Real.rpow T γ / Real.rpow T β) - 1 / (M : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast (Nat.ceil_le.mp hlow)
  have hdiv :
      Real.rpow T γ / Real.rpow T β - 1 / ((r : ℝ) * (M : ℝ)) ≤
        (h : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrreal).2
    calc
      (Real.rpow T γ / Real.rpow T β -
          1 / ((r : ℝ) * (M : ℝ))) * (r : ℝ) =
          (r : ℝ) * (Real.rpow T γ / Real.rpow T β) - 1 / (M : ℝ) := by
            field_simp [hrreal.ne', hMreal.ne']
      _ ≤ (h : ℝ) := hceil
  have hmul := mul_le_mul_of_nonneg_right hdiv hlogpos.le
  have hmul' :
      (Real.rpow T γ / Real.rpow T β) * Real.log (p : ℝ) -
          Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) ≤
        ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
    calc
      (Real.rpow T γ / Real.rpow T β) * Real.log (p : ℝ) -
          Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) =
        (Real.rpow T γ / Real.rpow T β -
          1 / ((r : ℝ) * (M : ℝ))) * Real.log (p : ℝ) := by ring
      _ ≤ ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := hmul
  have hhalf :
      Real.log (p : ℝ) / ((r : ℝ) * (M : ℝ)) ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith [hwidth]
  have hxlower :
      (Real.rpow T γ / Real.rpow T β) * Real.log (p : ℝ) - 1 / 2 ≤
        ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
    linarith
  have hratio_nonneg : 0 ≤ Real.rpow T γ / Real.rpow T β := by
    exact div_nonneg
      (Real.rpow_nonneg (le_of_lt hTpos) γ)
      (Real.rpow_nonneg (le_of_lt hTpos) β)
  have hprod_lower :
      Real.rpow T α * (Real.rpow T γ / Real.rpow T β) ≤
        Real.log (p : ℝ) * (Real.rpow T γ / Real.rpow T β) := by
    exact mul_le_mul_of_nonneg_right (le_of_lt hloglower) hratio_nonneg
  have hpow_id :
      (Real.rpow T γ / Real.rpow T β) * Real.rpow T α =
        Real.rpow T (α + γ - β) := by
    have hratio : Real.rpow T γ / Real.rpow T β = Real.rpow T (γ - β) :=
      (Real.rpow_sub hTpos γ β).symm
    calc
      (Real.rpow T γ / Real.rpow T β) * Real.rpow T α =
          Real.rpow T (γ - β) * Real.rpow T α := by rw [hratio]
      _ = Real.rpow T ((γ - β) + α) :=
        (Real.rpow_add hTpos (γ - β) α).symm
      _ = Real.rpow T (α + γ - β) := by
        congr 1
        ring
  have hxlower' :
      Real.rpow T (α + γ - β) - 1 / 2 ≤
        ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
    rw [← hpow_id]
    have hprod_lower' :
        (Real.rpow T γ / Real.rpow T β) * Real.rpow T α ≤
          (Real.rpow T γ / Real.rpow T β) * Real.log (p : ℝ) := by
      calc
        (Real.rpow T γ / Real.rpow T β) * Real.rpow T α =
            Real.rpow T α * (Real.rpow T γ / Real.rpow T β) := by ring
        _ ≤ Real.log (p : ℝ) * (Real.rpow T γ / Real.rpow T β) := hprod_lower
        _ = (Real.rpow T γ / Real.rpow T β) * Real.log (p : ℝ) := by ring
    exact (sub_le_sub_right hprod_lower' _).trans hxlower
  have hL :
      Real.rpow T (α + γ - β) / 2 ≤
        ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) := by
    linarith
  have hhr : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast (Nat.le_of_lt hhH)
  have hrone : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (show 1 ≤ r by omega)
  have hdiv_le : (h : ℝ) / (r : ℝ) ≤ (h : ℝ) := by
    apply (div_le_iff₀ hrreal).2
    nlinarith [hrone]
  have hupper' :
      ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) ≤
        (H : ℝ) * Real.rpow T β := by
    calc
      ((h : ℝ) / (r : ℝ)) * Real.log (p : ℝ) ≤
          (h : ℝ) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right hdiv_le hlogpos.le
      _ ≤ (H : ℝ) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right hhr hlogpos.le
      _ ≤ (H : ℝ) * Real.rpow T β :=
        mul_le_mul_of_nonneg_left hlogupper (by positivity)
  apply badPairQWindowBrunDecayError_le_of_bounds
    (L := Real.rpow T (α + γ - β) / 2)
    (U := (H : ℝ) * Real.rpow T β) hr hh
  · positivity
  · nlinarith [hpower]
  · exact hL
  · exact hupper'

theorem badPairQWindowBrunDecayMajorant_le_main_add_error
    {M r h p : ℕ} :
    badPairQWindowBrunDecayMajorant M r h p ≤
      16 / ((h : ℝ) * (M : ℝ)) + badPairQWindowBrunDecayError M r h p := by
  by_cases hz : r = 0 ∨ h = 0
  · simp [badPairQWindowBrunDecayMajorant, badPairQWindowBrunDecayError, hz]
    positivity
  · simp [badPairQWindowBrunDecayMajorant, badPairQWindowBrunDecayError, hz]

/- Purely finite splitting of the p-dependent decay sum.  The lower-h condition is retained on
the error part, while the main term is enlarged to the unrestricted range; this is the exact
shape needed before applying the logarithmic p-weight estimate. -/
theorem pDependent_decay_sum_le_main_range_add_error
    (s : Finset ℕ) (rho : ℝ) (M H : ℕ)
    (lower : ℕ → ℕ → ℕ) :
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        if lower p _r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M _r h p
        else 0) ≤
      (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.range H,
          ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) +
      (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.range H,
          if lower p _r ≤ h then
            ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M _r h p
          else 0) := by
  calc
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ h ∈ Finset.range H,
          if lower p _r ≤ h then
            ((p : ℝ)⁻¹) * badPairQWindowBrunDecayMajorant M _r h p
          else 0) ≤
        ∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range H,
            (((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ))) +
              if lower p _r ≤ h then
                ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M _r h p
              else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro h hh
      by_cases hlow : lower p r ≤ h
      · simp [hlow]
        have hpoint := badPairQWindowBrunDecayMajorant_le_main_add_error
          (M := M) (r := r) (h := h) (p := p)
        have hmul := mul_le_mul_of_nonneg_left hpoint
          (show 0 ≤ (p : ℝ)⁻¹ by positivity)
        simpa [mul_add] using hmul
      · simp [hlow]
        positivity
    _ =
        (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range H,
            ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) +
        (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range H,
            if lower p _r ≤ h then
              ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M _r h p
            else 0) := by
      simp_rw [Finset.sum_add_distrib]

/- Report-scale specialization of the finite split.  The first summand is the unrestricted
reciprocal-width main term; the second keeps the genuine lower-h indicator and therefore carries
all exponential sieve decay. -/
theorem badPairWeight_le_primeDependent_main_plus_error_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM4 : 4 ≤ M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α)
    (hwidth : ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      (∑ p ∈ primeWindow T α β,
        ∑ _r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
            ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) +
      (∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
            if primeWindowHLower T β γ M r ≤ h then
              ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
            else 0) := by
  exact (badPairWeight_le_primeDependent_decay_of_report_bounds
      T α β γ δ rho M hT hβγ hrho hM4 hL hpositive hwidth).trans
    (pDependent_decay_sum_le_main_range_add_error
      (s := primeWindow T α β) (rho := rho) (M := M)
      (H := reportHBound T α β δ rho M)
      (lower := fun _p r ↦ primeWindowHLower T β γ M r))

/- The preceding split now feeds the available logarithmic prime-weight estimate.  The error
summand is intentionally left explicit: this theorem isolates the only remaining analytic task
for the report's first question, namely proving that this exponentially decaying finite sum tends
to zero under the selected scales. -/
theorem badPairWeight_le_primeDependent_main_plus_error_log_weight_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM4 : 4 ≤ M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α)
    (hwidth : ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      (16 / (M : ℝ)) *
        ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T β))) +
          PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
        (∑ h ∈ Finset.Icc 1 (reportHBound T α β δ rho M), ((h : ℝ)⁻¹)) +
      (∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
            if primeWindowHLower T β γ M r ≤ h then
              ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
            else 0) := by
  have hMpos : 0 < M := by omega
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hsplit := badPairWeight_le_primeDependent_main_plus_error_of_report_bounds
    T α β γ δ rho M hT hβγ hrho hM4 hL hpositive hwidth
  have hmainRange := pDependent_main_range_le_Icc
    (s := primeWindow T α β) (rho := rho) (M := M)
      (H := reportHBound T α β δ rho M)
  have hmainRangeAnalytic :
      (∑ p ∈ primeWindow T α β,
        ∑ r ∈ Finset.range (denominatorCutoff p rho),
          ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
            ((p : ℝ)⁻¹) * (16 / ((h : ℝ) * (M : ℝ)))) ≤
        (16 / (M : ℝ)) *
          ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
              (Nat.floor (Real.exp (Real.rpow T β))) +
            PrimitiveSetsAboveX.mertensPartialSum
              (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
          (∑ h ∈ Finset.Icc 1 (reportHBound T α β δ rho M), ((h : ℝ)⁻¹)) := by
    exact hmainRange.trans (pDependent_main_term_le_mertens
      (M := M) (H := reportHBound T α β δ rho M)
      hTpos hrho hMpos)
  exact hsplit.trans (add_le_add_left hmainRangeAnalytic _)

/- A bookkeeping interface for the last analytic step.  Any uniform pointwise majorant `B` for
the filtered error summands immediately gives a finite cardinality bound; no estimate on `B` is
assumed here. -/
theorem pDependent_decay_error_sum_le_of_pointwise
    (s : Finset ℕ) (rho : ℝ) (M H : ℕ)
    (lower : ℕ → ℕ → ℕ) (B : ℝ)
    (hpoint : ∀ p ∈ s, ∀ r < denominatorCutoff p rho, ∀ h < H,
      (if lower p r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
        else 0) ≤ B) :
    (∑ p ∈ s, ∑ r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        if lower p r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
        else 0) ≤
      (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ _h ∈ Finset.range H, B) := by
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro h hh
  exact hpoint p hp r (Finset.mem_range.mp hr) h (Finset.mem_range.mp hh)

/- A weighted version of the finite bookkeeping interface.  Retaining the factor `1/p` is
important here: after the `r`-sum it produces the logarithmic prime weight rather than the much
larger unweighted prime count. -/
theorem pDependent_decay_error_sum_le_of_pointwise_weighted
    (s : Finset ℕ) (rho : ℝ) (M H : ℕ)
    (lower : ℕ → ℕ → ℕ) (B : ℕ → ℝ)
    (hpoint : ∀ p ∈ s, ∀ r < denominatorCutoff p rho, ∀ h < H,
      (if lower p r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
        else 0) ≤ ((p : ℝ)⁻¹) * B p) :
    (∑ p ∈ s, ∑ r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        if lower p r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
        else 0) ≤
      (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ _h ∈ Finset.range H, ((p : ℝ)⁻¹) * B p) := by
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro h hh
  exact hpoint p hp r (Finset.mem_range.mp hr) h (Finset.mem_range.mp hh)

/- The direct prime-window decay estimate can now be inserted into the weighted bookkeeping
interface.  The remaining analytic task is to show that this explicit `B` times the logarithmic
prime-weight and finite `h` range tends to zero. -/
theorem pDependent_decay_error_sum_le_of_prime_window_bounds
    (s : Finset ℕ) (T α β γ rho : ℝ) (M H : ℕ)
    (hs : s ⊆ primeWindow T α β)
    (hT : 1 ≤ T) (hM : 0 < M)
    (hpower : 1 ≤ Real.rpow T (α + γ - β))
    (hwidth : ∀ p ∈ s, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    (∑ p ∈ s, ∑ r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        if primeWindowHLower T β γ M r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
        else 0) ≤
      (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ _h ∈ Finset.range H,
          ((p : ℝ)⁻¹) * (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
            (1 + ((H : ℝ) * Real.rpow T β) / 2) ^ 3)) := by
  let B : ℝ :=
    6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
      (1 + ((H : ℝ) * Real.rpow T β) / 2) ^ 3
  have hU0 : 0 ≤ (H : ℝ) * Real.rpow T β :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hT)) _)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hpoly : 0 ≤ 1 + ((H : ℝ) * Real.rpow T β) / 2 := by linarith
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (pow_nonneg hpoly 3)
  apply pDependent_decay_error_sum_le_of_pointwise_weighted s rho M H
    (fun _p r ↦ primeWindowHLower T β γ M r) (fun _p ↦ B)
  intro p hp r hr h hh
  have hpw : p ∈ primeWindow T α β := hs hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpw).2.1
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hpReal)
  by_cases hlow : primeWindowHLower T β γ M r ≤ h
  · simp only [hlow, ↓reduceIte]
    by_cases hzero : r = 0 ∨ h = 0
    · simp [badPairQWindowBrunDecayError, hzero]
      exact mul_nonneg hinv0 hB0
    · have hrpos : 0 < r := Nat.pos_of_ne_zero (by
        intro hr0
        apply hzero
        exact Or.inl hr0)
      have hhpos : 0 < h := Nat.pos_of_ne_zero (by
        intro hh0
        apply hzero
        exact Or.inr hh0)
      have herr := badPairQWindowBrunDecayError_le_of_prime_window_bounds
        hT hM hpw hrpos hhpos hh hlow (hwidth p hp r hrpos) hpower
      calc
        (p : ℝ)⁻¹ * badPairQWindowBrunDecayError M r h p ≤
            (p : ℝ)⁻¹ * B := by
          exact mul_le_mul_of_nonneg_left herr hinv0
        _ = (p : ℝ)⁻¹ * B := rfl
  · simp [hlow]
    exact mul_nonneg hinv0 hB0

theorem pDependent_constant_sum_eq
    (s : Finset ℕ) (rho : ℝ) (H : ℕ) (B : ℝ) :
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
      ∑ _h ∈ Finset.range H, B) =
      (∑ p ∈ s, (denominatorCutoff p rho : ℝ)) * (H : ℝ) * B := by
  calc
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ _h ∈ Finset.range H, B) =
        ∑ p ∈ s, (denominatorCutoff p rho : ℝ) * ((H : ℝ) * B) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ = (∑ p ∈ s, (denominatorCutoff p rho : ℝ)) * ((H : ℝ) * B) := by
      rw [Finset.sum_mul]
    _ = (∑ p ∈ s, (denominatorCutoff p rho : ℝ)) * (H : ℝ) * B := by
      ring

/- The corresponding weighted cardinality identity retains the reciprocal-prime factor needed for
the logarithmic prime-weight estimate. -/
theorem pDependent_weighted_constant_sum_eq
    (s : Finset ℕ) (rho : ℝ) (H : ℕ) (B : ℝ) :
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
      ∑ _h ∈ Finset.range H, ((p : ℝ)⁻¹) * B) =
      (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) * (H : ℝ) * B := by
  calc
    (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ _h ∈ Finset.range H, ((p : ℝ)⁻¹) * B) =
        ∑ p ∈ s, (denominatorCutoff p rho : ℝ) *
          ((H : ℝ) * (((p : ℝ)⁻¹) * B)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ = ∑ p ∈ s, (((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
          ((H : ℝ) * B) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
          ((H : ℝ) * B) := by
      rw [Finset.sum_mul]
    _ = (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) * (H : ℝ) * B := by
      ring

/- The preceding pointwise prime-window estimate and the weighted finite-box identity combine
into the exact shape of the remaining exponential error.  This is still a finite inequality: no
asymptotic claim is hidden here. -/
theorem pDependent_decay_error_sum_le_weighted_cube
    (s : Finset ℕ) (T α β γ rho : ℝ) (M H : ℕ)
    (hs : s ⊆ primeWindow T α β)
    (hT : 1 ≤ T) (hM : 0 < M)
    (hpower : 1 ≤ Real.rpow T (α + γ - β))
    (hwidth : ∀ p ∈ s, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    (∑ p ∈ s, ∑ r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        if primeWindowHLower T β γ M r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
        else 0) ≤
      (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) * (H : ℝ) *
        (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
      (1 + ((H : ℝ) * Real.rpow T β) / 2) ^ 3) := by
  let B : ℝ :=
    6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
      (1 + ((H : ℝ) * Real.rpow T β) / 2) ^ 3
  have hpoint := pDependent_decay_error_sum_le_of_prime_window_bounds
    (s := s) (T := T) (α := α) (β := β) (γ := γ) (rho := rho)
    (M := M) (H := H) hs hT hM hpower hwidth
  calc
    (∑ p ∈ s, ∑ r ∈ Finset.range (denominatorCutoff p rho),
      ∑ h ∈ Finset.range H,
        if primeWindowHLower T β γ M r ≤ h then
          ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
        else 0) ≤
      (∑ p ∈ s, ∑ _r ∈ Finset.range (denominatorCutoff p rho),
        ∑ _h ∈ Finset.range H, ((p : ℝ)⁻¹) * B) := by
      simpa [B] using hpoint
    _ = (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) * (H : ℝ) * B :=
      pDependent_weighted_constant_sum_eq s rho H B
    _ = (∑ p ∈ s, ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) * (H : ℝ) *
        (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
          (1 + ((H : ℝ) * Real.rpow T β) / 2) ^ 3) := by
      rfl

/- Report-scale packaging: the explicit main term and the exact weighted exponential cube are
now presented together.  This is the smallest theorem that still exposes every analytic input
needed for the final `T → ∞` argument. -/
theorem badPairWeight_le_main_plus_weighted_cube_of_report_bounds
    (T α β γ δ rho : ℝ) (M : ℕ)
    (hT : 1 ≤ T) (hβγ : β ≤ γ) (hrho : 0 < rho) (hM4 : 4 ≤ M)
    (hL : 0 < Real.rpow T α)
    (hpositive : 0 < Real.rpow T δ / Real.rpow T α)
    (hpower : 1 ≤ Real.rpow T (α + γ - β))
    (hwidth : ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
      2 * Real.log (p : ℝ) ≤ (r : ℝ) * (M : ℝ)) :
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
      (16 / (M : ℝ)) *
        ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T β))) +
          PrimitiveSetsAboveX.mertensPartialSum
            (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
        (∑ h ∈ Finset.Icc 1 (reportHBound T α β δ rho M), ((h : ℝ)⁻¹)) +
      (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
        (reportHBound T α β δ rho M : ℝ) *
        (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
          (1 + ((reportHBound T α β δ rho M : ℝ) * Real.rpow T β) / 2) ^ 3) := by
  have hM : 0 < M := by omega
  have hmain := badPairWeight_le_primeDependent_main_plus_error_log_weight_of_report_bounds
    T α β γ δ rho M hT hβγ hrho hM4 hL hpositive hwidth
  have herr := pDependent_decay_error_sum_le_weighted_cube
    (s := primeWindow T α β) (T := T) (α := α) (β := β) (γ := γ) (rho := rho)
    (M := M) (H := reportHBound T α β δ rho M)
    (hs := by intro p hp; exact hp) hT hM hpower hwidth
  calc
    pairReciprocalWeight (badPairs T α β γ δ rho M) ≤
        (16 / (M : ℝ)) *
            ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) +
              PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
            (∑ h ∈ Finset.Icc 1 (reportHBound T α β δ rho M), ((h : ℝ)⁻¹)) +
          (∑ p ∈ primeWindow T α β,
            ∑ r ∈ Finset.range (denominatorCutoff p rho),
              ∑ h ∈ Finset.range (reportHBound T α β δ rho M),
                if primeWindowHLower T β γ M r ≤ h then
                  ((p : ℝ)⁻¹) * badPairQWindowBrunDecayError M r h p
                else 0) := hmain
    _ ≤
        (16 / (M : ℝ)) *
            ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) +
              PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
            (∑ h ∈ Finset.Icc 1 (reportHBound T α β δ rho M), ((h : ℝ)⁻¹)) +
          (∑ p ∈ primeWindow T α β,
            ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
            (reportHBound T α β δ rho M : ℝ) *
            (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
              (1 + ((reportHBound T α β δ rho M : ℝ) * Real.rpow T β) / 2) ^ 3) := by
      gcongr

/- The exponent in the compact error factor is positive under the source ordering.  This small
arithmetic lemma lets the report-scale packaging discharge the remaining `1 ≤ T^e` side condition
eventually, without baking an unproved analytic estimate into the finite theorem above. -/
theorem eventually_report_decay_exponent_ge_one
    {α β γ : ℝ} (hα : 0 < α) (hβγ : β ≤ γ) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ Real.rpow T (α + γ - β) := by
  have hexp : 0 < α + γ - β := by linarith
  have hpow : Tendsto (fun T : ℝ ↦ Real.rpow T (α + γ - β)) atTop atTop :=
    tendsto_rpow_atTop hexp
  filter_upwards [hpow.eventually (eventually_ge_atTop (1 : ℝ))] with T hT
  exact hT

/- Moving endpoint floors are eventually at least two whenever the exponent is positive.  This is
the small natural-number gate needed before invoking either the Mertens or Chebyshev-window bounds
at `N = floor (exp (T^β))`. -/
theorem eventually_exp_rpow_floor_ge_two
    {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ T : ℝ in atTop,
      2 ≤ Nat.floor (Real.exp (Real.rpow T β)) := by
  have hpow : Tendsto (fun T : ℝ ↦ Real.rpow T β) atTop atTop :=
    tendsto_rpow_atTop hβ
  have hexp : Tendsto (fun T : ℝ ↦ Real.exp (Real.rpow T β)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hpow
  filter_upwards [hexp.eventually (eventually_ge_atTop (2 : ℝ))] with T hT
  apply Nat.le_floor
  exact hT

/- The bounded-error Mertens input can be evaluated at the report's moving endpoint without
leaving a floor or a logarithm in the eventual statement. -/
theorem eventually_mertens_exp_rpow_le_add_constant
    {β C : ℝ} (hβ : 0 < β)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C) :
    ∀ᶠ T : ℝ in atTop,
      PrimitiveSetsAboveX.mertensPartialSum
          (Nat.floor (Real.exp (Real.rpow T β))) ≤
        Real.rpow T β + C := by
  filter_upwards [eventually_exp_rpow_floor_ge_two hβ] with T hN
  have hdiff :
      PrimitiveSetsAboveX.mertensPartialSum
          (Nat.floor (Real.exp (Real.rpow T β))) -
        Real.log (Nat.floor (Real.exp (Real.rpow T β)) : ℝ) ≤ C := by
    exact le_trans (le_abs_self _) (hMertens hN)
  have hNpos : 0 < (Nat.floor (Real.exp (Real.rpow T β)) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hN)
  have hlog : Real.log (Nat.floor (Real.exp (Real.rpow T β)) : ℝ) ≤
      Real.rpow T β := by
    apply (Real.log_le_iff_le_exp hNpos).2
    exact Nat.floor_le (Real.exp_nonneg _)
  linarith

/- Eventual version at the moving endpoint.  The first conjunct is kept explicit because the
generic exponential-vs-polynomial lemma needs nonnegativity of the outer weight. -/
theorem eventually_report_cutoff_weight_le_rpow_mertens
    {α β rho C : ℝ} (hβ : 0 < β) (hrho : 0 < rho) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C) :
    ∀ᶠ T : ℝ in atTop,
      0 ≤ (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) ∧
      (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) ≤
        (4 / rho) * (Real.rpow T β + C) +
          (Real.rpow T β + C) / Real.rpow T α := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_exp_rpow_floor_ge_two hβ] with T hT hN
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    positivity
  · exact primeWindow_cutoff_weight_le_rpow_mertens hT hrho hC hMertens hN

/- A concrete polynomial envelope for the outer cutoff weight.  The exponent `β+1` is deliberately
generous; its only role is to feed the exponential-vs-polynomial lemma, while preserving the
source parameter dependence and avoiding any hidden prime-counting assumption. -/
theorem eventually_report_cutoff_weight_le_polynomial
    {α β rho C : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hrho : 0 < rho) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C) :
    ∀ᶠ T : ℝ in atTop,
      0 ≤ (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) ∧
      (∑ p ∈ primeWindow T α β,
        ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) ≤
        Real.rpow T (β + 1) := by
  let K : ℝ := 8 / rho + 2
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hTpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hN : ∀ᶠ T : ℝ in atTop,
      2 ≤ Nat.floor (Real.exp (Real.rpow T β)) :=
    eventually_exp_rpow_floor_ge_two hβ
  have hCbound : ∀ᶠ T : ℝ in atTop, C ≤ Real.rpow T β := by
    exact (tendsto_rpow_atTop hβ).eventually (eventually_ge_atTop C)
  have hTbound : ∀ᶠ T : ℝ in atTop, K ≤ T := eventually_ge_atTop K
  filter_upwards [hT, hTpos, hN, hCbound, hTbound] with T hT1 hTposT hNT hCT hKT
  have hbase := primeWindow_cutoff_weight_le_rpow_mertens
    (T := T) (a := α) (b := β) (rho := rho) (C := C)
    hTposT hrho hC hMertens hNT
  have hTa : 1 ≤ Real.rpow T α := Real.one_le_rpow hT1 hα.le
  have hTb0 : 0 ≤ Real.rpow T β := (Real.rpow_pos_of_pos hTposT _).le
  have hsum : Real.rpow T β + C ≤ 2 * Real.rpow T β := by linarith
  have hnum0 : 0 ≤ Real.rpow T β + C := by positivity
  have hfrac : (Real.rpow T β + C) / Real.rpow T α ≤
      Real.rpow T β + C := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hTposT α)).2
    calc
      Real.rpow T β + C = (Real.rpow T β + C) * 1 := by ring
      _ ≤ (Real.rpow T β + C) * Real.rpow T α :=
        mul_le_mul_of_nonneg_left hTa hnum0
  have houter :
      (4 / rho) * (Real.rpow T β + C) +
        (Real.rpow T β + C) / Real.rpow T α ≤ K * Real.rpow T β := by
    have hfirst := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (4 / rho : ℝ))
    have hsecond := hfrac.trans hsum
    calc
      (4 / rho) * (Real.rpow T β + C) +
          (Real.rpow T β + C) / Real.rpow T α ≤
          (4 / rho) * (2 * Real.rpow T β) + 2 * Real.rpow T β :=
        add_le_add hfirst hsecond
      _ = K * Real.rpow T β := by
        dsimp [K]
        ring
  have hKT : K * Real.rpow T β ≤ Real.rpow T (β + 1) := by
    have hmul := mul_le_mul_of_nonneg_left hKT hTb0
    calc
      K * Real.rpow T β = Real.rpow T β * K := by ring
      _ ≤ Real.rpow T β * T := hmul
      _ = Real.rpow T (β + 1) := by
        calc
          Real.rpow T β * T = Real.rpow T β * Real.rpow T 1 := by simp
          _ = Real.rpow T (β + 1) :=
            (Real.rpow_add hTposT β 1).symm
  exact ⟨by
    apply Finset.sum_nonneg
    intro p hp
    positivity,
    hbase.trans (houter.trans hKT)⟩

/- The report numerator range has a completely explicit polynomial-sized envelope.  This is still
an elementary ceiling estimate; it is recorded separately so the final exponential gate can use it
without unfolding the nested `ceil` definition. -/
theorem eventually_reportHBound_le_explicit
    {α β δ rho : ℝ}
    (hα : 0 < α) (hδ1 : δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) <
        (4 * Real.rpow T β / rho + 1) * Real.rpow T δ + 3 := by
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hTpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hM : ∀ᶠ T : ℝ in atTop, 1 < reportApproximationScale T δ :=
    eventually_reportApproximationScale_gt_one hδ1
  filter_upwards [hT, hTpos, hM] with T hT1 hTposT hMT
  have hMpos : 0 < (reportApproximationScale T δ : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hMT)
  have hMinv0 : 0 ≤ 1 / (reportApproximationScale T δ : ℝ) :=
    (one_div_pos.mpr hMpos).le
  have hR0 : 0 ≤ (reportRBound T β rho : ℝ) := by positivity
  have hTd0 : 0 ≤ Real.rpow T δ := (Real.rpow_pos_of_pos hTposT _).le
  have hratio0 : 0 ≤ Real.rpow T δ / Real.rpow T α :=
    div_nonneg hTd0 (Real.rpow_pos_of_pos hTposT α).le
  have harg : 0 ≤ (reportRBound T β rho : ℝ) *
      (Real.rpow T δ / Real.rpow T α) +
        1 / (reportApproximationScale T δ : ℝ) :=
    add_nonneg (mul_nonneg hR0 hratio0) hMinv0
  have hH := reportHBound_cast_lt harg
  have hR : (reportRBound T β rho : ℝ) < 4 * Real.rpow T β / rho + 1 := by
    apply reportRBound_cast_lt
    have hTb : 0 ≤ Real.rpow T β := (Real.rpow_pos_of_pos hTposT β).le
    positivity
  have hTa : 1 ≤ Real.rpow T α := Real.one_le_rpow hT1 hα.le
  have hratio : Real.rpow T δ / Real.rpow T α ≤ Real.rpow T δ := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hTposT α)).2
    calc
      Real.rpow T δ = Real.rpow T δ * 1 := by ring
      _ ≤ Real.rpow T δ * Real.rpow T α :=
        mul_le_mul_of_nonneg_left hTa hTd0
  have hMinv : 1 / (reportApproximationScale T δ : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hMpos).2
    norm_num
    exact_mod_cast (show 1 ≤ reportApproximationScale T δ by omega)
  calc
    (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) <
        (reportRBound T β rho : ℝ) *
            (Real.rpow T δ / Real.rpow T α) +
          1 / (reportApproximationScale T δ : ℝ) + 2 := hH
    _ ≤ (4 * Real.rpow T β / rho + 1) * Real.rpow T δ + 3 := by
      have hRrhs0 : 0 ≤ 4 * Real.rpow T β / rho + 1 := by
        have hTb : 0 ≤ Real.rpow T β := (Real.rpow_pos_of_pos hTposT β).le
        positivity
      have hmul := mul_le_mul (le_of_lt hR) hratio hratio0 hRrhs0
      nlinarith

/- Multiplying the report numerator range by the extra `T^β` appearing in the cubic factor still
leaves a fixed polynomial power.  This is the concrete `hH` input for the generic exponential gate.
The exponent is intentionally loose by four powers so all ceiling constants are absorbed by
`T^4` eventually. -/
theorem eventually_reportHBound_mul_beta_le_polynomial
    {α β δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      0 ≤ (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) ∧
      (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
          Real.rpow T β ≤ Real.rpow T (2 * β + δ + 4) := by
  let K : ℝ := 4 / rho + 5
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hTpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hH := eventually_reportHBound_le_explicit (β := β) hα hδ1 hrho
  have hKpow : ∀ᶠ T : ℝ in atTop, K ≤ Real.rpow T 4 := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4)).eventually
      (eventually_ge_atTop K)
  filter_upwards [hT, hTpos, hH, hKpow] with T hT1 hTposT hHT hKT
  have hTb1 : 1 ≤ Real.rpow T β := Real.one_le_rpow hT1 hβ.le
  have hTd1 : 1 ≤ Real.rpow T δ := Real.one_le_rpow hT1 hδ0
  have hTbd1 : 1 ≤ Real.rpow T (β + δ) :=
    Real.one_le_rpow hT1 (by linarith)
  have hTb0 : 0 ≤ Real.rpow T β := (Real.rpow_pos_of_pos hTposT _).le
  have hTd0 : 0 ≤ Real.rpow T δ := (Real.rpow_pos_of_pos hTposT _).le
  have hTbd0 : 0 ≤ Real.rpow T (β + δ) :=
    (Real.rpow_pos_of_pos hTposT _).le
  have hR : (reportRBound T β rho : ℝ) <
      4 * Real.rpow T β / rho + 1 := by
    apply reportRBound_cast_lt
    have hTb : 0 ≤ Real.rpow T β := (Real.rpow_pos_of_pos hTposT β).le
    positivity
  have hHpoly :
      (4 * Real.rpow T β / rho + 1) * Real.rpow T δ + 3 ≤
        K * Real.rpow T (β + δ) := by
    have hterm1 :
        (4 / rho) * (Real.rpow T β * Real.rpow T δ) ≤
          (4 / rho) * Real.rpow T (β + δ) := by
      have hpowbd : Real.rpow T β * Real.rpow T δ =
          Real.rpow T (β + δ) := (Real.rpow_add hTposT β δ).symm
      rw [hpowbd]
    have hterm2 : Real.rpow T δ ≤ Real.rpow T (β + δ) := by
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have hterm3 : (3 : ℝ) ≤ 3 * Real.rpow T (β + δ) := by
      nlinarith
    calc
      (4 * Real.rpow T β / rho + 1) * Real.rpow T δ + 3 =
          (4 / rho) * (Real.rpow T β * Real.rpow T δ) +
            Real.rpow T δ + 3 := by ring
      _ ≤ (4 / rho) * Real.rpow T (β + δ) +
            Real.rpow T (β + δ) + 3 * Real.rpow T (β + δ) := by
        exact add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = (4 / rho + 4) * Real.rpow T (β + δ) := by ring
      _ ≤ (4 / rho + 5) * Real.rpow T (β + δ) := by
        apply mul_le_mul_of_nonneg_right (by norm_num) hTbd0
      _ = K * Real.rpow T (β + δ) := by simp [K]
  have hHle :
      (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) ≤
        K * Real.rpow T (β + δ) := by
    exact (le_of_lt hHT).trans hHpoly
  have hHbeta :
      (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
          Real.rpow T β ≤ K * Real.rpow T (2 * β + δ) := by
    have hmul := mul_le_mul_of_nonneg_right hHle hTb0
    calc
      (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
          Real.rpow T β ≤ (K * Real.rpow T (β + δ)) * Real.rpow T β := hmul
      _ = K * Real.rpow T (2 * β + δ) := by
        have hpow : Real.rpow T (β + δ) * Real.rpow T β =
            Real.rpow T ((β + δ) + β) :=
          (Real.rpow_add hTposT (β + δ) β).symm
        rw [show (K * Real.rpow T (β + δ)) * Real.rpow T β =
            K * (Real.rpow T (β + δ) * Real.rpow T β) by ring, hpow]
        rw [show (β + δ) + β = 2 * β + δ by ring]
  have hKmul : K * Real.rpow T (2 * β + δ) ≤
      Real.rpow T 4 * Real.rpow T (2 * β + δ) := by
    exact mul_le_mul_of_nonneg_right hKT
      (Real.rpow_pos_of_pos hTposT _).le
  have hfinal : Real.rpow T 4 * Real.rpow T (2 * β + δ) ≤
      Real.rpow T (2 * β + δ + 4) := by
    have hpow : Real.rpow T 4 * Real.rpow T (2 * β + δ) =
        Real.rpow T (4 + (2 * β + δ)) :=
      (Real.rpow_add hTposT 4 (2 * β + δ)).symm
    rw [hpow]
    rw [show 4 + (2 * β + δ) = 2 * β + δ + 4 by ring]
  exact ⟨by positivity, hHbeta.trans (hKmul.trans hfinal)⟩

/- The floor in the report scale loses at most one unit.  Once the underlying power is at least
16, this gives the convenient reciprocal lower bound `T^(1-δ)/16 ≤ M(T)` used in the main-term
estimate. -/
theorem eventually_rpow_div_sixteen_le_reportApproximationScale
    {δ : ℝ} (hδ1 : δ < 1) :
    ∀ᶠ T : ℝ in atTop,
      Real.rpow T (1 - δ) / 16 ≤ (reportApproximationScale T δ : ℝ) := by
  have hpow : Tendsto (fun T : ℝ => T ^ (1 - δ)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hδ1)
  filter_upwards [hpow.eventually (eventually_ge_atTop (16 : ℝ))] with T hT
  have hfloor : Real.rpow T (1 - δ) / 8 - 1 <
      (reportApproximationScale T δ : ℝ) := by
    unfold reportApproximationScale
    exact Nat.sub_one_lt_floor _
  have hdiff : Real.rpow T (1 - δ) / 16 ≤
      Real.rpow T (1 - δ) / 8 - 1 := by
    norm_num at hT ⊢
    linarith
  exact le_of_lt (lt_of_le_of_lt hdiff hfloor)

/- A small logarithmic-growth lemma used for the reciprocal-width main term.  It is deliberately
stated for an arbitrary eventually polynomially bounded nonnegative function, so later report
variants can reuse it without unfolding their ceiling definitions. -/
theorem eventually_log_le_two_rpow_of_polynomial_bound
    {q e : ℝ} (hq : 0 < q) (he : 0 < e) (H : ℝ → ℝ)
    (hH : ∀ᶠ T : ℝ in atTop, 0 ≤ H T ∧ H T ≤ Real.rpow T q) :
    ∀ᶠ T : ℝ in atTop,
      Real.log (H T) ≤ Real.rpow T (2 * e) := by
  let r : ℝ := e / q
  have hr : 0 < r := div_pos he hq
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hInv : ∀ᶠ T : ℝ in atTop,
      1 / (e / q) ≤ Real.rpow T e := by
    exact (tendsto_rpow_atTop he).eventually
      (eventually_ge_atTop (1 / (e / q)))
  filter_upwards [hH, hT, hInv] with T hHT hT1 hInvT
  have hT0 : 0 ≤ T := by linarith
  have hpowH : (H T) ^ r ≤ (Real.rpow T q) ^ r :=
    Real.rpow_le_rpow hHT.1 hHT.2 hr.le
  have hTpow : (Real.rpow T q) ^ r = Real.rpow T e := by
    calc
      (Real.rpow T q) ^ r = Real.rpow T (q * r) :=
        (Real.rpow_mul hT0 q r).symm
      _ = Real.rpow T e := by
        congr 1
        dsimp [r]
        field_simp
  have hpow : (H T) ^ r ≤ Real.rpow T e := hpowH.trans_eq hTpow
  have hlog := Real.log_le_rpow_div hHT.1 hr
  have hlog' : Real.log (H T) ≤ (H T) ^ r * (1 / r) := by
    simpa [div_eq_mul_inv] using hlog
  have hmul := mul_le_mul_of_nonneg_right hpow (one_div_pos.mpr hr).le
  have hlog'' : Real.log (H T) ≤ Real.rpow T e * (1 / r) :=
    hlog'.trans (by simpa [mul_comm] using hmul)
  have hInv' : 1 / r ≤ Real.rpow T e := by
    simpa [r] using hInvT
  have hprod : (1 / r) * Real.rpow T e ≤
      Real.rpow T e * Real.rpow T e :=
    mul_le_mul_of_nonneg_right hInv' (Real.rpow_nonneg hT0 _)
  calc
    Real.log (H T) ≤ Real.rpow T e * (1 / r) := hlog''
    _ = (1 / r) * Real.rpow T e := by ring
    _ ≤ Real.rpow T e * Real.rpow T e := hprod
    _ = Real.rpow T (2 * e) := by
      calc
        Real.rpow T e * Real.rpow T e = Real.rpow T (e + e) :=
          (Real.rpow_add (lt_of_lt_of_le zero_lt_one hT1) e e).symm
        _ = Real.rpow T (2 * e) := by congr 1; ring

/- The von Mangoldt Mertens partial sum is a finite sum of nonnegative terms.  This elementary
fact lets the report main term be handled by a squeeze rather than an absolute-value estimate. -/
theorem mertensPartialSum_nonneg (N : ℕ) :
    0 ≤ PrimitiveSetsAboveX.mertensPartialSum N := by
  unfold PrimitiveSetsAboveX.mertensPartialSum
  apply Finset.sum_nonneg
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  exact div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) hnpos.le

/- The report numerator range is polynomially bounded before taking a logarithm.  The gap
`β+δ<1` is exactly what makes a positive spare exponent available for the logarithmic factor. -/
theorem eventually_report_harmonic_le_two_rpow
    {α β δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      (∑ h ∈ Finset.Icc 1
          (reportHBound T α β δ rho (reportApproximationScale T δ)), ((h : ℝ)⁻¹)) ≤
        2 * Real.rpow T (2 * ((1 - β - δ) / 3)) := by
  let q : ℝ := 2 * β + δ + 4
  let e : ℝ := (1 - β - δ) / 3
  have hgap : 0 < 1 - β - δ := by linarith [hβδ]
  have he : 0 < e := by
    dsimp [e]
    linarith
  have hq : 0 < q := by
    dsimp [q]
    linarith
  have hHpoly := eventually_reportHBound_mul_beta_le_polynomial
    (α := α) (β := β) (δ := δ) (rho := rho)
    hα hβ hδ0 hδ1 hrho
  have hHbound : ∀ᶠ T : ℝ in atTop,
      0 ≤ (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) ∧
      (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) ≤
        Real.rpow T q := by
    filter_upwards [hHpoly, eventually_ge_atTop (1 : ℝ)] with T hHT hT
    have hTβ : 1 ≤ Real.rpow T β := Real.one_le_rpow hT hβ.le
    have hH0 : 0 ≤
        (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) := hHT.1
    have hHle :
        (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) ≤
          (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
            Real.rpow T β := by
      have hmul := mul_le_mul_of_nonneg_left hTβ hH0
      simpa only [mul_one] using hmul
    exact ⟨hH0, hHle.trans (by simpa [q] using hHT.2)⟩
  have hlog := eventually_log_le_two_rpow_of_polynomial_bound hq he _ hHbound
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  filter_upwards [hlog, hT] with T hlogT hT1
  have he0 : 0 ≤ 2 * e := by linarith
  have hpow1 : 1 ≤ Real.rpow T (2 * e) := Real.one_le_rpow hT1 he0
  have hsum := reciprocal_harmonic_sum_le_one_add_log
    (reportHBound T α β δ rho (reportApproximationScale T δ))
  have hbound :
      (∑ h ∈ Finset.Icc 1
          (reportHBound T α β δ rho (reportApproximationScale T δ)), ((h : ℝ)⁻¹)) ≤
        1 + Real.rpow T (2 * e) := by
    exact hsum.trans (by simpa [add_comm] using add_le_add_left hlogT 1)
  calc
    (∑ h ∈ Finset.Icc 1
        (reportHBound T α β δ rho (reportApproximationScale T δ)), ((h : ℝ)⁻¹)) ≤
      1 + Real.rpow T (2 * e) := hbound
    _ ≤ 2 * Real.rpow T (2 * e) := by linarith
    _ = 2 * Real.rpow T (2 * ((1 - β - δ) / 3)) := by simp [e]

/- Pure power bookkeeping for the main-term envelope.  Keeping this equality separate makes the
order-theoretic proof below readable and avoids hiding any exponent arithmetic in `ring`. -/
theorem report_main_power_identity {T β δ rho e gap : ℝ} (hT : 0 < T)
    (hgap : gap = 1 - β - δ)
    (heq : e = (1 - β - δ) / 3) :
    (256 / Real.rpow T (1 - δ)) *
        ((8 / rho + 2) * Real.rpow T β) *
        (2 * Real.rpow T (2 * e)) =
      (512 * (8 / rho + 2)) * Real.rpow T (-(gap / 3)) := by
  have hInvEq : 256 / Real.rpow T (1 - δ) =
      256 * Real.rpow T (-(1 - δ)) := by
    have hneg : (Real.rpow T (1 - δ))⁻¹ =
        Real.rpow T (-(1 - δ)) :=
      (Real.rpow_neg hT.le (1 - δ)).symm
    calc
      256 / Real.rpow T (1 - δ) =
          256 * (Real.rpow T (1 - δ))⁻¹ := by ring
      _ = 256 * Real.rpow T (-(1 - δ)) := by rw [hneg]
  rw [hInvEq]
  have hp1 : Real.rpow T (-(1 - δ)) * Real.rpow T β =
      Real.rpow T (-(1 - δ) + β) :=
    (Real.rpow_add hT (-(1 - δ)) β).symm
  have hp2 : Real.rpow T (-(1 - δ) + β) * Real.rpow T (2 * e) =
      Real.rpow T (-(1 - δ) + β + 2 * e) :=
    (Real.rpow_add hT (-(1 - δ) + β) (2 * e)).symm
  have hpowers :
      Real.rpow T (-(1 - δ)) * Real.rpow T β *
          Real.rpow T (2 * e) =
        Real.rpow T (-(1 - δ) + β + 2 * e) := by
    calc
      Real.rpow T (-(1 - δ)) * Real.rpow T β *
          Real.rpow T (2 * e) =
          (Real.rpow T (-(1 - δ)) * Real.rpow T β) *
            Real.rpow T (2 * e) := by ring
      _ = Real.rpow T (-(1 - δ) + β) *
            Real.rpow T (2 * e) := by rw [hp1]
      _ = Real.rpow T (-(1 - δ) + β + 2 * e) := hp2
  calc
    (256 * Real.rpow T (-(1 - δ))) *
          ((8 / rho + 2) * Real.rpow T β) *
          (2 * Real.rpow T (2 * e)) =
        (512 * (8 / rho + 2)) *
          (Real.rpow T (-(1 - δ)) * Real.rpow T β *
            Real.rpow T (2 * e)) := by ring
    _ = (512 * (8 / rho + 2)) *
          Real.rpow T (-(1 - δ) + β + 2 * e) := by
      exact congrArg (fun z : ℝ => (512 * (8 / rho + 2)) * z) hpowers
    _ = (512 * (8 / rho + 2)) * Real.rpow T (-(gap / 3)) := by
      rw [hgap, heq]
      congr 2
      ring

/- The explicit reciprocal-width Mertens main term tends to zero under the report's parameter
gap `β+δ<1`.  This is the last analytic factor in the report-scale bad-pair estimate. -/
def reportMainTerm (T α β δ rho : ℝ) : ℝ :=
  (16 / (reportApproximationScale T δ : ℝ)) *
      ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
          (Nat.floor (Real.exp (Real.rpow T β))) +
        PrimitiveSetsAboveX.mertensPartialSum
          (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
      (∑ h ∈ Finset.Icc 1
          (reportHBound T α β δ rho (reportApproximationScale T δ)), ((h : ℝ)⁻¹))

theorem tendsto_report_main_term_zero
    {α β δ rho C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho)
    (_hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C) :
    Tendsto (fun T : ℝ ↦ reportMainTerm T α β δ rho) atTop (𝓝 0) := by
  let gap : ℝ := 1 - β - δ
  let e : ℝ := gap / 3
  let A : ℝ := 8 / rho + 2
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [hβδ]
  have he : 0 < e := by
    dsimp [e]
    linarith
  have hq : 0 < (2 * β + δ + 4 : ℝ) := by
    linarith
  have hMlow := eventually_rpow_div_sixteen_le_reportApproximationScale hδ1
  have hS := eventually_mertens_exp_rpow_le_add_constant hβ hMertens
  have hCpow : ∀ᶠ T : ℝ in atTop, C ≤ Real.rpow T β :=
    (tendsto_rpow_atTop hβ).eventually (eventually_ge_atTop C)
  have hHarm := eventually_report_harmonic_le_two_rpow
    hα hβ hδ0 hδ1 hβδ hrho
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hTpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hKernel : Tendsto (fun T : ℝ ↦
      (512 * A) * Real.rpow T (-(gap / 3))) atTop (𝓝 0) := by
    have hk := tendsto_rpow_neg_atTop (by linarith : 0 < gap / 3)
    have hc : Tendsto (fun _ : ℝ ↦ (512 * A)) atTop (𝓝 (512 * A)) :=
      tendsto_const_nhds
    change Tendsto (fun T : ℝ ↦ (512 * A) * T ^ (-(gap / 3))) atTop (𝓝 0)
    simpa using hc.mul hk
  have hpoint : ∀ᶠ T : ℝ in atTop,
      0 ≤ reportMainTerm T α β δ rho ∧
        reportMainTerm T α β δ rho ≤
          (512 * A) * Real.rpow T (-(gap / 3)) := by
    filter_upwards [hMlow, hS, hCpow, hHarm, hT, hTpos] with
      T hMlowT hST hCT hHT hT1 hTposT
    let N : ℕ := Nat.floor (Real.exp (Real.rpow T β))
    let S : ℝ := PrimitiveSetsAboveX.mertensPartialSum N
    let Hn : ℕ := reportHBound T α β δ rho (reportApproximationScale T δ)
    let Hsum : ℝ := ∑ h ∈ Finset.Icc 1 Hn, ((h : ℝ)⁻¹)
    let X : ℝ := Real.rpow T (1 - δ)
    have hS0 : 0 ≤ S := by
      dsimp [S, N]
      exact mertensPartialSum_nonneg _
    have hSle : S ≤ 2 * Real.rpow T β := by
      calc
        S ≤ Real.rpow T β + C := by simpa [S, N] using hST
        _ ≤ 2 * Real.rpow T β := by linarith [hCT]
    have hTa : 1 ≤ Real.rpow T α := Real.one_le_rpow hT1 hα.le
    have hTapos : 0 < Real.rpow T α := Real.rpow_pos_of_pos hTposT _
    have hSdiv : S / Real.rpow T α ≤ S := by
      apply (div_le_iff₀ hTapos).2
      calc
        S = S * 1 := by ring
        _ ≤ S * Real.rpow T α := mul_le_mul_of_nonneg_left hTa hS0
    have hB0 : 0 ≤ (4 / rho) * S + S / Real.rpow T α :=
      add_nonneg (mul_nonneg (by positivity) hS0) (div_nonneg hS0 hTapos.le)
    have hB : (4 / rho) * S + S / Real.rpow T α ≤
        A * Real.rpow T β := by
      have hfirst := mul_le_mul_of_nonneg_left hSle
        (by positivity : 0 ≤ (4 / rho : ℝ))
      have hsecond := hSdiv.trans hSle
      calc
        (4 / rho) * S + S / Real.rpow T α ≤
            (4 / rho) * (2 * Real.rpow T β) + 2 * Real.rpow T β :=
          add_le_add hfirst hsecond
        _ = A * Real.rpow T β := by dsimp [A]; ring
    have hXpos : 0 < X := by dsimp [X]; positivity
    have hMpos : 0 < (reportApproximationScale T δ : ℝ) := by
      exact lt_of_lt_of_le (by positivity : 0 < Real.rpow T (1 - δ) / 16) hMlowT
    have hInv : 1 / (reportApproximationScale T δ : ℝ) ≤ 1 / (X / 16) :=
      one_div_le_one_div_of_le (div_pos hXpos (by norm_num)) hMlowT
    have hMmain : 16 / (reportApproximationScale T δ : ℝ) ≤ 256 / X := by
      calc
        16 / (reportApproximationScale T δ : ℝ) =
            16 * (1 / (reportApproximationScale T δ : ℝ)) := by ring
        _ ≤ 16 * (1 / (X / 16)) :=
          mul_le_mul_of_nonneg_left hInv (by norm_num)
        _ = 256 / X := by
          field_simp [ne_of_gt hXpos]
          norm_num
    have hHsum0 : 0 ≤ Hsum := by
      dsimp [Hsum, Hn]
      apply Finset.sum_nonneg
      intro h hh
      have hhpos : 0 < (h : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hh).1
      positivity
    have hHarmT : Hsum ≤ 2 * Real.rpow T (2 * e) := by
      simpa [Hsum, Hn, e] using hHT
    have hA0 : 0 ≤ A := by
      dsimp [A]
      positivity
    have hAd0 : 0 ≤ A * Real.rpow T β :=
      mul_nonneg hA0 (Real.rpow_nonneg (by linarith) _)
    have hprod1 : (16 / (reportApproximationScale T δ : ℝ)) *
        ((4 / rho) * S + S / Real.rpow T α) ≤
      (256 / X) * (A * Real.rpow T β) := by
      have h256X0 : 0 ≤ 256 / X := div_nonneg (by norm_num) hXpos.le
      exact mul_le_mul hMmain hB hB0 h256X0
    have hprod2 : ((16 / (reportApproximationScale T δ : ℝ)) *
        ((4 / rho) * S + S / Real.rpow T α)) * Hsum ≤
      ((256 / X) * (A * Real.rpow T β)) *
        (2 * Real.rpow T (2 * e)) := by
      have h256X0 : 0 ≤ 256 / X := div_nonneg (by norm_num) hXpos.le
      have hR0 : 0 ≤ (256 / X) * (A * Real.rpow T β) :=
        mul_nonneg h256X0 hAd0
      exact mul_le_mul hprod1 hHarmT hHsum0 hR0
    have hEq : (256 / X) * (A * Real.rpow T β) *
        (2 * Real.rpow T (2 * e)) =
      (512 * A) * Real.rpow T (-(gap / 3)) := by
      dsimp [X]
      exact report_main_power_identity hTposT
        (by dsimp [gap]) (by dsimp [e, gap])
    have hupper : reportMainTerm T α β δ rho ≤
        (512 * A) * Real.rpow T (-(gap / 3)) := by
      dsimp [reportMainTerm, N, S, Hn, Hsum, X]
      exact hprod2.trans_eq hEq
    have hmain0 : 0 ≤ reportMainTerm T α β δ rho := by
      dsimp [reportMainTerm, N, S, Hn, Hsum]
      have hMfac0 : 0 ≤ 16 / (reportApproximationScale T δ : ℝ) :=
        div_nonneg (by norm_num) hMpos.le
      exact mul_nonneg (mul_nonneg hMfac0 hB0) hHsum0
    exact ⟨hmain0, hupper⟩
  exact squeeze_zero'
    (hpoint.mono fun T h => h.1)
    (hpoint.mono fun T h => h.2)
    hKernel

/- The report-specific exponential error is now discharged completely.  The only analytic input
left in this theorem is the bounded-error Mertens estimate used to control the reciprocal prime
weight; the rest is the generic exponential-vs-polynomial gate above. -/
theorem tendsto_report_weighted_cube_error_zero
    {α β γ δ rho C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hrho : 0 < rho) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C) :
    Tendsto
      (fun T : ℝ ↦
        (∑ p ∈ primeWindow T α β,
          ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
          (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
          (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
            (1 + ((reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
              Real.rpow T β) / 2) ^ 3)) atTop (𝓝 0) := by
  let W : ℝ → ℝ := fun T ↦
    ∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)
  let H : ℝ → ℝ := fun T ↦
    (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ)
  have hW := eventually_report_cutoff_weight_le_polynomial
    (α := α) (β := β) (rho := rho) (C := C)
    hα hβ hrho hC hMertens
  have hH := eventually_reportHBound_mul_beta_le_polynomial
    (α := α) (β := β) (δ := δ) (rho := rho)
    hα hβ hδ0 hδ1 hrho
  have ha : 0 < α + γ - β := by linarith
  have hs : 0 ≤ 2 * β + δ + 4 := by linarith
  have hgen := tendsto_weight_mul_exp_neg_mul_cube_of_polynomial_bounds
    (a := α + γ - β) (b := (1 / 8 : ℝ)) (c := β + 1)
    (s := 2 * β + δ + 4) (t := β)
    ha (by norm_num) hs hβ.le W H hW hH
  change Tendsto (fun T : ℝ ↦
      W T * H T * (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
        (1 + (H T * Real.rpow T β) / 2) ^ 3)) atTop (𝓝 0)
  have heq : (fun T : ℝ ↦
      W T * H T * (6 * Real.exp (-(1 / 8 : ℝ) * Real.rpow T (α + γ - β)) *
        (1 + (H T * Real.rpow T β) / 2) ^ 3)) =
      (fun T : ℝ ↦
        W T * H T * (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
          (1 + (H T * Real.rpow T β) / 2) ^ 3)) := by
    funext T
    have hexp : -(1 / 8 : ℝ) * Real.rpow T (α + γ - β) =
        -(Real.rpow T (α + γ - β) / 2) / 4 := by ring
    rw [hexp]
  rw [← heq]
  exact hgen

/- All elementary report-scale side conditions can now be assembled in one eventual statement.
The right-hand side is intentionally left in the explicit finite form: the next milestone is to
prove that its Mertens main term and weighted exponential cube tend to zero. -/
theorem eventually_badPairWeight_le_main_plus_weighted_cube_of_report_scale
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hδ : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      pairReciprocalWeight (badPairsAtReportScale T α β γ δ rho) ≤
        (16 / (reportApproximationScale T δ : ℝ)) *
            ((4 / rho) * PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) +
              PrimitiveSetsAboveX.mertensPartialSum
                (Nat.floor (Real.exp (Real.rpow T β))) / Real.rpow T α) *
            (∑ h ∈ Finset.Icc 1
                (reportHBound T α β δ rho (reportApproximationScale T δ)), ((h : ℝ)⁻¹)) +
          (∑ p ∈ primeWindow T α β,
            ((p : ℝ)⁻¹) *
              (denominatorCutoff p rho : ℝ)) *
            (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
            (6 * Real.exp
                (-(Real.rpow T (α + γ - β) / 2) / 4) *
              (1 + ((reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
                Real.rpow T β) / 2) ^ 3) := by
  have hTpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hTone : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hM4 : ∀ᶠ T : ℝ in atTop,
      4 ≤ (reportApproximationScale T δ : ℝ) :=
    eventually_reportApproximationScale_ge_four hδ
  have hwidth : ∀ᶠ T : ℝ in atTop,
      ∀ p ∈ primeWindow T α β, ∀ r : ℕ, 0 < r →
        2 * Real.log (p : ℝ) ≤ (r : ℝ) *
          (reportApproximationScale T δ : ℝ) :=
    eventually_primeWindow_width_of_reportApproximationScale hβ hβδ
  have hpower := eventually_report_decay_exponent_ge_one hα hβγ
  filter_upwards [hTpos, hTone, hM4, hwidth, hpower] with T hT hT1 hM4T hwidthT hpowerT
  have hM4nat : 4 ≤ reportApproximationScale T δ := by
    exact_mod_cast hM4T
  have hL : 0 < Real.rpow T α := Real.rpow_pos_of_pos hT _
  have hpositive : 0 < Real.rpow T δ / Real.rpow T α := by
    exact div_pos (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hT _)
  have hbound := badPairWeight_le_main_plus_weighted_cube_of_report_bounds
    T α β γ δ rho (reportApproximationScale T δ)
    hT1 hβγ hrho hM4nat hL hpositive hpowerT hwidthT
  simpa [badPairsAtReportScale, badPairsWithScale] using hbound

/- Final analytic contract for Track A.  The finite report-scale inequality above is deliberately
separated from this order-theoretic endpoint: once the explicit Mertens main term and weighted
exponential cube have each been dominated by functions tending to zero, no further number theory
is hidden in the passage to the bad-pair weight limit. -/
theorem tendsto_badPairWeight_zero_of_report_main_error_bounds
    {alpha beta gamma delta rho : ℝ}
    (main error : ℝ → ℝ)
    (hupper : ∀ᶠ T : ℝ in atTop,
      pairReciprocalWeight (badPairsAtReportScale T alpha beta gamma delta rho) ≤
        main T + error T)
    (hmain : Tendsto main atTop (𝓝 0))
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto
      (fun T : ℝ ↦ pairReciprocalWeight
        (badPairsAtReportScale T alpha beta gamma delta rho))
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun T : ℝ ↦ main T + error T) atTop (𝓝 0) := by
    simpa using hmain.add herror
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun T ↦
      pairReciprocalWeight_nonneg
        (badPairsAtReportScale T alpha beta gamma delta rho))
  · exact hupper
  · exact hsum

/- The explicit report-scale error term, named so that the preceding finite inequality can be
packaged without repeating its long expression at every Track-A call site. -/
def reportWeightedCubeError (T α β γ δ rho : ℝ) : ℝ :=
  (∑ p ∈ primeWindow T α β,
      ((p : ℝ)⁻¹) * (denominatorCutoff p rho : ℝ)) *
    (reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
    (6 * Real.exp (-(Real.rpow T (α + γ - β) / 2) / 4) *
      (1 + ((reportHBound T α β δ rho (reportApproximationScale T δ) : ℝ) *
        Real.rpow T β) / 2) ^ 3)

/- The report-scale bad-pair reciprocal weight now has a complete analytic `o(1)` proof, once the
audited bounded-error von Mangoldt Mertens estimate is supplied.  This theorem is deliberately
below the density-one construction: it closes the central bad-prime-pair estimate itself, while
leaving the normal-order and lower-packing inputs explicit in the higher-level Track-A file. -/
theorem tendsto_badPairWeight_zero_of_report_scale
    {α β γ δ rho C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) (hC : 0 < C)
    (hMertens : ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |PrimitiveSetsAboveX.mertensPartialSum t - Real.log (t : ℝ)| ≤ C) :
    Tendsto
      (fun T : ℝ ↦ pairReciprocalWeight
        (badPairsAtReportScale T α β γ δ rho))
      atTop (𝓝 0) := by
  apply tendsto_badPairWeight_zero_of_report_main_error_bounds
    (main := fun T : ℝ ↦ reportMainTerm T α β δ rho)
    (error := fun T : ℝ ↦ reportWeightedCubeError T α β γ δ rho)
  · filter_upwards [eventually_badPairWeight_le_main_plus_weighted_cube_of_report_scale
      hα hβ.le hβγ hδ1 hβδ hrho] with T hT
    simpa [reportMainTerm, reportWeightedCubeError] using hT
  · exact tendsto_report_main_term_zero hα hβ hδ0 hδ1 hβδ hrho hC hMertens
  · simpa [reportWeightedCubeError] using
      (tendsto_report_weighted_cube_error_zero
        (α := α) (β := β) (γ := γ) (δ := δ) (rho := rho) (C := C)
        hα hβ hβγ hδ0 hδ1 hrho hC hMertens)

/- The previous theorem can consume the exact existential interface exported by LeanPool, so
callers need not manually thread its error constant through the report-scale calculation. -/
theorem tendsto_badPairWeight_zero_of_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    Tendsto
      (fun T : ℝ ↦ pairReciprocalWeight
        (badPairsAtReportScale T α β γ δ rho))
      atTop (𝓝 0) := by
  rcases Upstream.vonMangoldt_mertens_bounded_error with ⟨C, hC, hMertens⟩
  exact tendsto_badPairWeight_zero_of_report_scale
    hα hβ hβγ hδ0 hδ1 hβδ hrho hC hMertens

/- The integer-indexed version is the form consumed by the union-bound theorem: the real report
parameter is simply evaluated at the cast `T = X`. -/
theorem tendsto_badPairExceptionalRatio_zero_of_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    Tendsto (fun X : ℕ ↦
      ((divisibleBySomePairUpTo X
        (badPairsAtReportScale (X : ℝ) α β γ δ rho)).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  let pairs : ℕ → Finset (ℕ × ℕ) := fun X ↦
    badPairsAtReportScale (X : ℝ) α β γ δ rho
  have hweightR : Tendsto (fun T : ℝ ↦
      pairReciprocalWeight (badPairsAtReportScale T α β γ δ rho)) atTop (𝓝 0) :=
    tendsto_badPairWeight_zero_of_report_scale_default
      hα hβ hβγ hδ0 hδ1 hβδ hrho
  have hweightN : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (pairs X))
      atTop (𝓝 0) := by
    have hcomp := hweightR.comp tendsto_natCast_atTop_atTop
    change Tendsto
      ((fun T : ℝ ↦ pairReciprocalWeight
        (badPairsAtReportScale T α β γ δ rho)) ∘ Nat.cast)
      atTop (𝓝 0)
    exact hcomp
  simpa [pairs] using
    (tendsto_exceptionalRatio_zero_of_reciprocalWeight pairs hweightN)

/- The report chooses its analytic parameter as `T = log X`.  The preceding theorem evaluates at
   `T = X` for the finite endpoint version; this companion records the actual logarithmic scaling
   before any variable-family bookkeeping is applied. -/
theorem tendsto_badPairWeight_zero_of_log_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    Tendsto (fun X : ℕ ↦ pairReciprocalWeight
      (badPairsAtReportScale (Real.log (X : ℝ)) α β γ δ rho)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (tendsto_badPairWeight_zero_of_report_scale_default
    hα hβ hβγ hδ0 hδ1 hβδ hrho).comp hlog

theorem tendsto_badPairExceptionalRatio_zero_of_log_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho) :
    Tendsto (fun X : ℕ ↦
      ((divisibleBySomePairUpTo X
        (badPairsAtReportScale (Real.log (X : ℝ)) α β γ δ rho)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let pairs : ℕ → Finset (ℕ × ℕ) := fun X ↦
    badPairsAtReportScale (Real.log (X : ℝ)) α β γ δ rho
  have hweightN : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (pairs X))
      atTop (𝓝 0) := by
    simpa [pairs] using
      (tendsto_badPairWeight_zero_of_log_report_scale_default
        hα hβ hβγ hδ0 hδ1 hβδ hrho)
  simpa [pairs] using
    (tendsto_exceptionalRatio_zero_of_reciprocalWeight pairs hweightN)

/- If the report-scale bad-pair families are monotone in the integer endpoint, the variable-family
   union-bound interface gives the corresponding exceptional ratio directly.  The monotonicity
   premise is kept explicit: the floor/ceiling changes in the report parameters must be checked by
   the eventual good-window construction before this can be discharged. -/
theorem tendsto_variableReportExceptionalRatio_zero_of_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho)
    (hmono : ∀ ⦃n m : ℕ⦄, n ≤ m →
      badPairsAtReportScale (n : ℝ) α β γ δ rho ⊆
        badPairsAtReportScale (m : ℝ) α β γ δ rho) :
    Tendsto (fun X : ℕ ↦
      ((divisibleBySomeVariablePairUpTo X
        (fun N : ℕ ↦ badPairsAtReportScale (N : ℝ) α β γ δ rho)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let pairs : ℕ → Finset (ℕ × ℕ) := fun X ↦
    badPairsAtReportScale (X : ℝ) α β γ δ rho
  have hweightR : Tendsto (fun T : ℝ ↦
      pairReciprocalWeight (badPairsAtReportScale T α β γ δ rho)) atTop (𝓝 0) :=
    tendsto_badPairWeight_zero_of_report_scale_default
      hα hβ hβγ hδ0 hδ1 hβδ hrho
  have hweightN : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (pairs X))
      atTop (𝓝 0) := by
    have hcomp := hweightR.comp tendsto_natCast_atTop_atTop
    change Tendsto
      ((fun T : ℝ ↦ pairReciprocalWeight
        (badPairsAtReportScale T α β γ δ rho)) ∘ Nat.cast)
      atTop (𝓝 0)
    exact hcomp
  have hmono' : ∀ ⦃n m : ℕ⦄, n ≤ m → pairs n ⊆ pairs m := by
    intro n m hnm
    exact hmono hnm
  simpa [pairs] using
    (tendsto_variableExceptionalRatio_zero_of_reciprocalWeight pairs hmono' hweightN)

/- The variable-family report-scale version with the source's `T = log X` choice. -/
theorem tendsto_variableLogReportExceptionalRatio_zero_of_report_scale_default
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hβδ : β + δ < 1)
    (hrho : 0 < rho)
    (hmono : ∀ ⦃n m : ℕ⦄, n ≤ m →
      badPairsAtReportScale (Real.log (n : ℝ)) α β γ δ rho ⊆
        badPairsAtReportScale (Real.log (m : ℝ)) α β γ δ rho) :
    Tendsto (fun X : ℕ ↦
      ((divisibleBySomeVariablePairUpTo X
        (fun N : ℕ ↦ badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let pairs : ℕ → Finset (ℕ × ℕ) := fun X ↦
    badPairsAtReportScale (Real.log (X : ℝ)) α β γ δ rho
  have hweightN : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (pairs X))
      atTop (𝓝 0) := by
    simpa [pairs] using
      (tendsto_badPairWeight_zero_of_log_report_scale_default
        hα hβ hβγ hδ0 hδ1 hβδ hrho)
  have hmono' : ∀ ⦃n m : ℕ⦄, n ≤ m → pairs n ⊆ pairs m := by
    intro n m hnm
    exact hmono hnm
  simpa [pairs] using
    (tendsto_variableExceptionalRatio_zero_of_reciprocalWeight pairs hmono' hweightN)

/- The block-cover form is the honest interface for the raw moving report windows.  A future
   geometric/dyadic decomposition may provide a block family whose reciprocal weight tends to
   zero even though the pointwise report families are not monotone. -/
theorem tendsto_variableLogReportExceptionalRatio_zero_of_blockWeight
    {α β γ δ rho : ℝ}
    (block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃X N : ℕ⦄, N ≤ X →
      badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho ⊆ block X)
    (hweight : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (block X)) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((divisibleBySomeVariablePairUpTo X
        (fun N : ℕ ↦ badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let pairs : ℕ → Finset (ℕ × ℕ) := fun N ↦
    badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho
  have hcover' : ∀ ⦃X N : ℕ⦄, N ≤ X → pairs N ⊆ block X := by
    intro X N hNX
    exact hcover hNX
  have hresult := tendsto_variableExceptionalRatio_zero_of_blockWeight
    pairs block hcover' hweight
  simpa [pairs] using hresult

/- The initial-block version allows the cover to start only at `K(X)`.  This is often the natural
   shape of a density argument: the finitely many smaller indices contribute `K(X)/X`, while the
   report-scale block carries the reciprocal-weight estimate. -/
theorem tendsto_variableLogReportExceptionalRatio_zero_of_initial_blockWeight
    {α β γ δ rho : ℝ}
    (K : ℕ → ℕ) (block : ℕ → Finset (ℕ × ℕ))
    (hcover : ∀ ⦃X N : ℕ⦄, K X ≤ N → N ≤ X →
      badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho ⊆ block X)
    (hK : Tendsto (fun X : ℕ ↦ (K X : ℝ) / (X : ℝ)) atTop (𝓝 0))
    (hweight : Tendsto (fun X : ℕ ↦ pairReciprocalWeight (block X)) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ ↦
      ((divisibleBySomeVariablePairUpTo X
        (fun N : ℕ ↦ badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  let pairs : ℕ → Finset (ℕ × ℕ) := fun N ↦
    badPairsAtReportScale (Real.log (N : ℝ)) α β γ δ rho
  have hcover' : ∀ ⦃X N : ℕ⦄, K X ≤ N → N ≤ X → pairs N ⊆ block X := by
    intro X N hKN hNX
    exact hcover hKN hNX
  have hresult := tendsto_variableExceptionalRatio_zero_of_initial_blockWeight
    pairs block K hcover' hK hweight
  simpa [pairs] using hresult

end Erdos878

namespace Erdos878

/- A concrete all-endpoint family.  The index is deliberately halved: the `m`-block family
  ends at `2^(4*(m+1)) = 16^(m+1)`, while `Nat.log 16 X` only guarantees `16^log₁₆ X ≤ X`.
  For the finitely many small endpoints we return the empty family; this keeps the subset
  contract global and makes the eventual branch explicit rather than hiding a partial index. -/
noncomputable def dyadicDisjointPrimeFamilyUpTo (X : ℕ) : Finset ℕ :=
  if 2 ≤ Nat.log 16 X then
    dyadicDisjointPrimeFamily (Nat.log 16 X / 2)
  else ∅

theorem dyadicDisjointPrimeFamilyUpTo_mono {n m : ℕ} (hnm : n ≤ m) :
    dyadicDisjointPrimeFamilyUpTo n ⊆ dyadicDisjointPrimeFamilyUpTo m := by
  classical
  by_cases hn : 2 ≤ Nat.log 16 n
  · have hlog : Nat.log 16 n ≤ Nat.log 16 m := Nat.log_mono_right hnm
    have hm : 2 ≤ Nat.log 16 m := le_trans hn hlog
    simp only [dyadicDisjointPrimeFamilyUpTo, hn, hm, ↓reduceIte]
    apply dyadicDisjointPrimeFamily_mono
    exact Nat.div_le_div_right hlog
  · simp only [dyadicDisjointPrimeFamilyUpTo, hn, ↓reduceIte]
    exact Finset.empty_subset _

theorem tendsto_nat_log_base_atTop {b : ℕ} (hb : 1 < b) :
    Tendsto (fun X : ℕ ↦ Nat.log b X) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (b ^ N)] with X hX
  exact Nat.le_log_of_pow_le hb hX

theorem tendsto_nat_log_div_two_atTop :
    Tendsto (fun X : ℕ ↦ Nat.log 16 X / 2) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  have hlog := tendsto_nat_log_base_atTop (b := 16) (by norm_num)
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 * N))] with X hX
  omega

/- The halved base-16 logarithmic index still controls the double logarithm of the endpoint.
   This elementary comparison is the scale bridge needed to turn the family-mass lower bound
   into the `n log log n` normalization of the Erdős #878 function `F`. -/
theorem eventually_loglog_le_two_log_natLog16_div_two_add_one :
    ∀ᶠ X : ℕ in atTop,
      Real.log (Real.log (X : ℝ)) ≤
        2 * Real.log ((Nat.log 16 X / 2 + 1 : ℕ) : ℝ) := by
  let M : ℕ → ℕ := fun X ↦ Nat.log 16 X / 2
  have hMt : Tendsto M atTop atTop := by
    simpa [M] using tendsto_nat_log_div_two_atTop
  have hMcast : Tendsto (fun X : ℕ ↦ ((M X + 1 : ℕ) : ℝ)) atTop atTop := by
    have hnat : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact hnat.comp hMt
  have hX : ∀ᶠ X : ℕ in atTop, 2 ≤ X := eventually_ge_atTop 2
  have hMlarge : ∀ᶠ X : ℕ in atTop, 0 < M X ∧
      2 * Real.log (16 : ℝ) ≤ ((M X + 1 : ℕ) : ℝ) := by
    filter_upwards [hMt.eventually (eventually_ge_atTop 1),
      hMcast.eventually (eventually_ge_atTop (2 * Real.log (16 : ℝ)))] with X hM hconst
    exact ⟨by omega, hconst⟩
  filter_upwards [hX, hMlarge] with X hX hM
  let L : ℝ := Real.log (X : ℝ)
  let Mreal : ℝ := ((M X + 1 : ℕ) : ℝ)
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpowNat : X < 16 ^ (Nat.log 16 X + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) X
  have hpowR : (X : ℝ) ≤ (16 : ℝ) ^ (Nat.log 16 X + 1) := by
    exact_mod_cast (Nat.le_of_lt hpowNat)
  have hlogpow :
      L ≤ ((Nat.log 16 X + 1 : ℕ) : ℝ) * Real.log (16 : ℝ) := by
    dsimp [L]
    have h := Real.log_le_log hXpos hpowR
    rw [Real.log_pow] at h
    exact h
  have hindex :
      ((Nat.log 16 X + 1 : ℕ) : ℝ) ≤ 2 * Mreal := by
    dsimp [Mreal, M]
    exact_mod_cast (by omega : Nat.log 16 X + 1 ≤ 2 * (Nat.log 16 X / 2 + 1))
  have hlogXupper : L ≤ (2 * Real.log (16 : ℝ)) * Mreal := by
    calc
      L ≤ ((Nat.log 16 X + 1 : ℕ) : ℝ) * Real.log (16 : ℝ) := hlogpow
      _ ≤ (2 * Mreal) * Real.log (16 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hindex (Real.log_pos (by norm_num)).le
      _ = (2 * Real.log (16 : ℝ)) * Mreal := by ring
  have hlogupper :
      Real.log L ≤ Real.log ((2 * Real.log (16 : ℝ)) * Mreal) := by
    apply Real.log_le_log hLpos
    have hconstpos : 0 < 2 * Real.log (16 : ℝ) := by positivity
    have hMpos : 0 < Mreal := by
      dsimp [Mreal]
      positivity
    exact hlogXupper
  have hconstlog :
      Real.log (2 * Real.log (16 : ℝ)) ≤ Real.log Mreal := by
    apply Real.log_le_log
    · positivity
    · exact hM.2
  have hlogmul :
      Real.log ((2 * Real.log (16 : ℝ)) * Mreal) =
        Real.log (2 * Real.log (16 : ℝ)) + Real.log Mreal := by
    rw [Real.log_mul (by positivity) (by positivity)]
  dsimp [L, Mreal] at hlogupper hconstlog hlogmul ⊢
  rw [hlogmul] at hlogupper
  linarith

theorem eventually_nat_log_base_ge_two :
    ∀ᶠ X : ℕ in atTop, 2 ≤ Nat.log 16 X := by
  have hlog := tendsto_nat_log_base_atTop (b := 16) (by norm_num)
  exact hlog.eventually (eventually_ge_atTop 2)

/- The all-endpoint family therefore carries a positive multiple of the required `log log X`
   reciprocal mass.  This is the quantitative lower input for the density-one `F` construction;
   the second-moment theorem below will convert it into a large divisor count on almost all `n`. -/
theorem eventually_dyadicDisjointPrimeFamilyUpTo_mass_ge_loglog :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * Real.log (Real.log (X : ℝ)) ≤
        ∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹) := by
  rcases eventually_dyadicDisjointPrimeFamily_mass_ge_log with ⟨c, hc, hfamily⟩
  let M : ℕ → ℕ := fun X ↦ Nat.log 16 X / 2
  have hMt : Tendsto M atTop atTop := by
    simpa [M] using tendsto_nat_log_div_two_atTop
  have hfamilyX : ∀ᶠ X : ℕ in atTop,
      c * Real.log ((M X + 1 : ℕ) : ℝ) ≤
        ∑ p ∈ dyadicDisjointPrimeFamily (M X), ((p : ℝ)⁻¹) := by
    exact hMt.eventually hfamily
  have hcompare := eventually_loglog_le_two_log_natLog16_div_two_add_one
  have hbranch := eventually_nat_log_base_ge_two
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hfamilyX, hcompare, hbranch] with X hfam hcomp hbr
  have hEq :
      (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) =
        ∑ p ∈ dyadicDisjointPrimeFamily (M X), ((p : ℝ)⁻¹) := by
    simp [dyadicDisjointPrimeFamilyUpTo, M, hbr]
  rw [hEq]
  have hmul := mul_le_mul_of_nonneg_left hcomp hc.le
  dsimp [M] at hmul ⊢
  nlinarith [hmul, hfam]

theorem dyadicDisjointPrimeFamilyUpTo_prime (X : ℕ) {p : ℕ}
    (hp : p ∈ dyadicDisjointPrimeFamilyUpTo X) : p.Prime := by
  classical
  by_cases hbranch : 2 ≤ Nat.log 16 X
  · have hp' : p ∈ dyadicDisjointPrimeFamily (Nat.log 16 X / 2) := by
      simpa [dyadicDisjointPrimeFamilyUpTo, hbranch] using hp
    exact dyadicDisjointPrimeFamily_prime (Nat.log 16 X / 2) hp'
  · simp [dyadicDisjointPrimeFamilyUpTo, hbranch] at hp

theorem dyadicDisjointPrimeFamilyUpTo_subset_Icc (X : ℕ) :
    dyadicDisjointPrimeFamilyUpTo X ⊆ Finset.Icc 1 X := by
  classical
  by_cases hX : X = 0
  · subst X
    by_cases hbranch : 2 ≤ Nat.log 16 0
    · have hlog : Nat.log 16 0 = 0 := Nat.log_zero_right 16
      omega
    · simp [dyadicDisjointPrimeFamilyUpTo]
  by_cases hbranch : 2 ≤ Nat.log 16 X
  · intro p hp
    have hp' : p ∈ dyadicDisjointPrimeFamily (Nat.log 16 X / 2) := by
      simpa [dyadicDisjointPrimeFamilyUpTo, hbranch] using hp
    have hfamily : p ∈ Finset.Icc 1
        (dyadicDisjointUpperEndpoint (Nat.log 16 X / 2)) :=
      dyadicDisjointPrimeFamily_subset_Icc (Nat.log 16 X / 2) hp'
    have hfamily' := Finset.mem_Icc.mp hfamily
    have hlogpow : 16 ^ Nat.log 16 X ≤ X := Nat.pow_log_le_self 16 hX
    have hidx : Nat.log 16 X / 2 + 1 ≤ Nat.log 16 X := by omega
    have hpow : 16 ^ (Nat.log 16 X / 2 + 1) ≤ 16 ^ Nat.log 16 X :=
      Nat.pow_le_pow_right (by norm_num) hidx
    have hupper : dyadicDisjointUpperEndpoint (Nat.log 16 X / 2) ≤ X := by
      unfold dyadicDisjointUpperEndpoint
      calc
        2 ^ (4 * (Nat.log 16 X / 2 + 1)) =
            (2 ^ 4) ^ (Nat.log 16 X / 2 + 1) := by rw [pow_mul]
        _ = 16 ^ (Nat.log 16 X / 2 + 1) := by norm_num
        _ ≤ 16 ^ Nat.log 16 X := hpow
        _ ≤ X := hlogpow
    exact Finset.mem_Icc.mpr ⟨hfamily'.1, hfamily'.2.trans hupper⟩
  · intro p hp
    simp [dyadicDisjointPrimeFamilyUpTo, hbranch] at hp

theorem tendsto_dyadicDisjointPrimeFamilyUpTo_mass_atTop :
    Tendsto (fun X : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) atTop atTop := by
  let m : ℕ → ℕ := fun X ↦ Nat.log 16 X / 2
  have hm : Tendsto m atTop atTop := by
    simpa [m] using tendsto_nat_log_div_two_atTop
  have hmass : Tendsto (fun X : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeFamily (m X), ((p : ℝ)⁻¹)) atTop atTop :=
    tendsto_dyadicDisjointPrimeFamily_mass_atTop.comp hm
  apply hmass.congr'
  filter_upwards [eventually_nat_log_base_ge_two] with X hX
  simp [dyadicDisjointPrimeFamilyUpTo, m, hX]

theorem tendsto_dyadicDisjointPrimeFamilyUpTo_mass_inv_zero :
    Tendsto (fun X : ℕ ↦
      (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹))⁻¹) atTop (𝓝 0) := by
  exact tendsto_dyadicDisjointPrimeFamilyUpTo_mass_atTop.inv_tendsto_atTop

/- The all-endpoint family also inherits the explicit finite Brun upper bound eventually.  The
   halved index keeps the family inside `[1,X]`; `tendsto_nat_log_div_two_atTop` supplies the
   threshold needed by the block estimate. -/
theorem eventually_dyadicDisjointPrimeFamilyUpTo_mass_le_harmonic_brun :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) ≤
        (∑ i ∈ Finset.range 10,
          ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
        (15 / Real.log 2) * (harmonic (Nat.log 16 X / 2) : ℝ) + 324 := by
  have hm := tendsto_nat_log_div_two_atTop
  filter_upwards [hm.eventually (eventually_ge_atTop 10), eventually_nat_log_base_ge_two]
    with X hX hbranch
  simp [dyadicDisjointPrimeFamilyUpTo, hbranch]
  exact dyadicDisjointPrimeFamily_mass_le_harmonic_brun (Nat.log 16 X / 2) hX

/- The harmonic number can be compressed once more, exposing the iterated-log index that appears
   in the summatory estimates. -/
theorem eventually_dyadicDisjointPrimeFamilyUpTo_mass_le_log :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) ≤
        (∑ i ∈ Finset.range 10,
          ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) +
        (15 / Real.log 2) *
          (1 + Real.log ((Nat.log 16 X / 2 : ℕ) : ℝ)) + 324 := by
  have hbase := eventually_dyadicDisjointPrimeFamilyUpTo_mass_le_harmonic_brun
  filter_upwards [hbase] with X hX
  have hharm : (harmonic (Nat.log 16 X / 2) : ℝ) ≤
      1 + Real.log ((Nat.log 16 X / 2 : ℕ) : ℝ) := by
    simpa only [Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
      (harmonic_le_one_add_log (Nat.log 16 X / 2))
  have hcoef : 0 ≤ 15 / Real.log (2 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hharm hcoef
  have hadd := add_le_add_right hmul
    ((∑ i ∈ Finset.range 10,
        ∑ p ∈ dyadicDisjointPrimeBlock i, ((p : ℝ)⁻¹)) + 324)
  linarith

/- Combining the all-endpoint family with the sharp finite second-moment theorem gives a genuine
   all-`X` density-zero statement (not merely a subsequence at dyadic endpoints).  This is still a
   divisor-count theorem; the remaining Track-A work is to turn these divisors into matched
   prime-power products near `n`. -/
theorem tendsto_dyadicDisjointPrimeFamilyUpTo_exceptionalRatio_zero :
    Tendsto (fun X : ℕ ↦
      ((((Finset.Icc 1 X).filter
        (fun n ↦ divisorCount (dyadicDisjointPrimeFamilyUpTo X) n <
          (∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹)) / 2)).card : ℕ) : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hμ : ∀ᶠ X : ℕ in atTop,
      0 < ∑ p ∈ dyadicDisjointPrimeFamilyUpTo X, ((p : ℝ)⁻¹) := by
    have h := tendsto_dyadicDisjointPrimeFamilyUpTo_mass_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))
    filter_upwards [h] with X hX
    exact hX
  exact tendsto_divisorCount_exceptionalRatio_zero_of_primeReciprocal_sharp_of_subset_Icc
    dyadicDisjointPrimeFamilyUpTo
    (fun X p hp ↦ dyadicDisjointPrimeFamilyUpTo_prime X hp)
    (fun X ↦ dyadicDisjointPrimeFamilyUpTo_subset_Icc X)
    hμ tendsto_dyadicDisjointPrimeFamilyUpTo_mass_inv_zero

end Erdos878

namespace Erdos878

/- Every prime in a real `primeWindow` lies in the initial interval ending at its floor upper
   endpoint.  This is the subset hypothesis needed when the divisor-count scale is chosen to be
   that upper endpoint. -/
theorem primeWindow_subset_Icc_floor_upper
    {T a b : ℝ} :
    primeWindow T a b ⊆
      Finset.Icc 1 (Nat.floor (Real.exp (Real.rpow T b))) := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpPrime : Nat.Prime p := hp'.2.1
  have hpIcc := Finset.mem_Icc.mp hp'.1
  exact Finset.mem_Icc.mpr ⟨hpPrime.one_lt.le, hpIcc.2⟩

end Erdos878

namespace Erdos878

/- A blockwise lower bound with a common positive contribution.  This is the finite interface
   consumed by the order-theoretic reciprocal-mass divergence lemma in `UnionBound`. -/
theorem reciprocalPrimesNat_sum_ge_mul_of_block_lower
    (m : ℕ) (A : ℕ → ℕ)
    (hmono : ∀ i < m, A i ≤ A (i + 1))
    (hpos : ∀ i < m, 0 < A (i + 1))
    {c : ℝ} (hblock : ∀ i < m,
      c ≤ ((Nat.primeCounting (A (i + 1)) - Nat.primeCounting (A i) : ℕ) : ℝ) /
        (A (i + 1) : ℝ)) :
    c * (m : ℝ) ≤
      ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hsum := reciprocalPrimesNat_sum_ge_primeCounting_sub_div_sum m A hmono hpos
  calc
    c * (m : ℝ) = ∑ i ∈ Finset.range m, c := by simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ i ∈ Finset.range m,
        ((Nat.primeCounting (A (i + 1)) - Nat.primeCounting (A i) : ℕ) : ℝ) /
          (A (i + 1) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hblock i (Finset.mem_range.mp hi)
    _ ≤ ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := hsum

end Erdos878

namespace Erdos878

/- The theta version of the common-contribution interface.  Once a future geometric partition
   proves a uniform lower bound `c` for the explicit theta block expression, this theorem turns it
   into a reciprocal prime-mass bound without reopening any finite-set bookkeeping. -/
theorem reciprocalPrimesNat_sum_ge_mul_of_theta_block_lower
    (m : ℕ) (A : ℕ → ℕ)
    (hA : ∀ i < m, 1 ≤ A i)
    (hmono : ∀ i < m, A i ≤ A (i + 1))
    (hB : ∀ i < m, 2 ≤ A (i + 1))
    {c : ℝ} (hblock : ∀ i < m,
      c ≤ ((A (i + 1) : ℝ) * Real.log 2 -
          Real.log ((A (i + 1) : ℝ) + 1) -
          2 * Real.sqrt (A (i + 1) : ℝ) * Real.log (A (i + 1) : ℝ) -
          Real.log 4 * (A i : ℝ)) /
        ((A (i + 1) : ℝ) * Real.log (A (i + 1) : ℝ))) :
    c * (m : ℝ) ≤
      ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hsum := reciprocalPrimesNat_sum_ge_theta_chebyshev m A hA hmono hB
  calc
    c * (m : ℝ) = ∑ i ∈ Finset.range m, c := by simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ i ∈ Finset.range m,
        ((A (i + 1) : ℝ) * Real.log 2 -
          Real.log ((A (i + 1) : ℝ) + 1) -
          2 * Real.sqrt (A (i + 1) : ℝ) * Real.log (A (i + 1) : ℝ) -
          Real.log 4 * (A i : ℝ)) /
        ((A (i + 1) : ℝ) * Real.log (A (i + 1) : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hblock i (Finset.mem_range.mp hi)
    _ ≤ ∑ i ∈ Finset.range m,
        ∑ p ∈ (Finset.Icc (A i + 1) (A (i + 1))).filter Nat.Prime, ((p : ℝ)⁻¹) := hsum

end Erdos878
