/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license; see LICENSE at the publication package root.

Modified for Erdős 878: standalone imports, exact sum identities and product-cutoff intervals.
Source of the first three lemmas: gersh/ternary-goldbach-lean,
commit 27df23af6a712895f22204d0d81102baa74f0ebe,
MathExtras/NumberTheory/Vinogradov/HardCutoffTypeIIQSensitive.lean.
-/
import Erdos878.TrackBCoefficients
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Track B: finite dyadic decomposition and exact product cutoffs

Every block retains its original upper endpoint. Product conditions in a correlation
are identified with a single interval; no terms are dropped from an oscillatory sum.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

/-- **Box-count log factor.**  The number of dyadic blocks needed to cover
`(0, n]` is `Nat.log 2 n + 1 ≤ 3·log n` for `n ≥ 2`
(constant `2/log 2 + ε ≤ 3`). -/
theorem dyadicBoxCount_le_three_log (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log n := by
  have hn0 : n ≠ 0 := by omega
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hpowR : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hcpos : (0 : ℝ) < Real.log 2 := by linarith
  have hlogpow : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) hpowR
    rwa [Real.log_pow] at h
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hX_pos : (0 : ℝ) < Real.log n := lt_of_lt_of_le hcpos hlogn
  have key : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log n := by
    have : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 =
        (Nat.log 2 n : ℝ) * Real.log 2 + Real.log 2 := by ring
    rw [this]
    linarith
  have key2 : 2 * Real.log n ≤ 3 * Real.log n * Real.log 2 := by nlinarith
  have h1 : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤
      3 * Real.log n * Real.log 2 := key.trans key2
  have h2 : ((Nat.log 2 n : ℝ) + 1) ≤ 3 * Real.log n :=
    le_of_mul_le_mul_right h1 hcpos
  push_cast
  exact h2

/-! ## Layer 1: dyadic partition of `(0, N]` -/

/-- **Dyadic partition.**  `(0, N] = {1} ∪ ⋃_{j ≤ log₂ N} (2^j, min(2^{j+1}, N)]`
(for `N ≥ 1`); each block is of the exact `Ioc K (2K)`-after-truncation
shape consumed by `AnalyticNT.Bilinear.TypeII.typeIISum`. -/
theorem Ioc_zero_eq_dyadic_biUnion (N : ℕ) (hN : 1 ≤ N) :
    Finset.Ioc 0 N =
      insert 1 ((Finset.range (Nat.log 2 N + 1)).biUnion
        (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N))) := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range,
    le_min_iff]
  constructor
  · rintro ⟨hm0, hmN⟩
    by_cases hm1 : m = 1
    · exact Or.inl hm1
    · refine Or.inr ⟨Nat.log 2 (m - 1), ?_, ?_, ?_, hmN⟩
      · have hle : m - 1 ≤ N := by omega
        exact Nat.lt_succ_of_le (Nat.log_mono_right hle)
      · have h := Nat.pow_log_le_self 2 (x := m - 1) (by omega)
        omega
      · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (m - 1)
        omega
  · rintro (rfl | ⟨j, _, hjm, hm2, hmN⟩)
    · exact ⟨one_pos, hN⟩
    · exact ⟨lt_of_le_of_lt (Nat.zero_le _) hjm, hmN⟩

/-- Pairwise disjointness of the dyadic blocks. -/
theorem dyadic_blocks_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint ↑(Finset.range (Nat.log 2 N + 1))
      (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
  have key : ∀ i j : ℕ, i < j →
      Disjoint (Finset.Ioc (2 ^ i) (min (2 ^ (i + 1)) N))
        (Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
    intro i j hij
    refine Finset.disjoint_left.mpr ?_
    intro m hm hm'
    obtain ⟨_, hm2⟩ := Finset.mem_Ioc.mp hm
    obtain ⟨hm3, _⟩ := Finset.mem_Ioc.mp hm'
    have hpow : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij
    have := le_min_iff.mp hm2
    omega
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm


/-- Exact sum decomposition, with the singleton endpoint accounted for. -/
theorem sum_Ioc_eq_one_add_dyadic {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Ioc 0 N, f n) = f 1 +
      ∑ j ∈ range (Nat.log 2 N + 1),
        ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
  classical
  have hnot : 1 ∉ (range (Nat.log 2 N + 1)).biUnion
      (fun j ↦ Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
    intro h
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp h
    have := (mem_Ioc.mp hj).1
    have := Nat.one_le_two_pow (n := j)
    omega
  rw [Ioc_zero_eq_dyadic_biUnion N hN, sum_insert hnot,
    sum_biUnion (dyadic_blocks_pairwiseDisjoint N)]

/-- Zero at one removes the singleton, even for endpoint zero. -/
theorem sum_Ioc_eq_dyadic_of_one_eq_zero {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) (hf : f 1 = 0) :
    (∑ n ∈ Ioc 0 N, f n) =
      ∑ j ∈ range (Nat.log 2 N + 1),
        ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [sum_Ioc_eq_one_add_dyadic f N hN, hf, zero_add]

/-- Two-dimensional exact decomposition for coefficients supported away from one. -/
theorem sum_sum_Ioc_eq_dyadic (f : ℕ → ℕ → ℂ) (X Y : ℕ)
    (hleft : ∀ n, f 1 n = 0) (hright : ∀ m, f m 1 = 0) :
    (∑ m ∈ Ioc 0 X, ∑ n ∈ Ioc 0 Y, f m n) =
      ∑ i ∈ range (Nat.log 2 X + 1), ∑ j ∈ range (Nat.log 2 Y + 1),
        ∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) X),
          ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y), f m n := by
  rw [sum_Ioc_eq_dyadic_of_one_eq_zero (fun m ↦ ∑ n ∈ Ioc 0 Y, f m n)
    X (by simp [hleft])]
  apply sum_congr rfl
  intro i _
  simp_rw [sum_Ioc_eq_dyadic_of_one_eq_zero (f _) Y (hright _)]
  rw [sum_comm]

/-- The triangle inequality is applied after exact decomposition into boxes. -/
theorem norm_sum_sum_Ioc_le_dyadic (f : ℕ → ℕ → ℂ) (X Y : ℕ)
    (hleft : ∀ n, f 1 n = 0) (hright : ∀ m, f m 1 = 0) :
    ‖∑ m ∈ Ioc 0 X, ∑ n ∈ Ioc 0 Y, f m n‖ ≤
      ∑ i ∈ range (Nat.log 2 X + 1), ∑ j ∈ range (Nat.log 2 Y + 1),
        ‖∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) X),
          ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y), f m n‖ := by
  rw [sum_sum_Ioc_eq_dyadic f X Y hleft hright]
  exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_sum_le _ _)

/-- The simultaneous product cutoffs in a Type-II correlation form a single integer interval. -/
theorem correlation_product_filter_eq_Ioc (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    {m ∈ Ioc M B | P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y} =
      Ioc (max M (max (P / n₁) (P / n₂)))
        (min B (min (Y / n₁) (Y / n₂))) := by
  ext m
  simp only [mem_filter, mem_Ioc, max_lt_iff, le_min_iff,
    Nat.div_lt_iff_lt_mul hn₁, Nat.div_lt_iff_lt_mul hn₂,
    Nat.le_div_iff_mul_le hn₁, Nat.le_div_iff_mul_le hn₂]
  tauto

/-- The corresponding exact identity for any summand, including complex phases. -/
theorem sum_correlation_product_filter_eq_Ioc (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (f : ℕ → ℂ) :
    (∑ m ∈ Ioc M B,
      if P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y then f m else 0) =
      ∑ m ∈ Ioc (max M (max (P / n₁) (P / n₂)))
        (min B (min (Y / n₁) (Y / n₂))), f m := by
  rw [← sum_filter, correlation_product_filter_eq_Ioc M B P Y n₁ n₂ hn₁ hn₂]

end
end Erdos878.TrackB
