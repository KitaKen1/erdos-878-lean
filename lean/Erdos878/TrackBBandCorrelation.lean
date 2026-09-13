import Erdos878.TrackBPhaseSums

/-!
# Track B: the exact cutoff correlation satisfies the second-derivative bound

This is the first direct bridge from the actual cutoff weight used in the Vaughan
Type-II term to the proved exponential-sum estimate. Natural-number division at
the endpoints is retained exactly.
-/

namespace Erdos878.TrackB
open Finset Set
open scoped ComplexConjugate
noncomputable section

theorem sum_Ioc_eq_sum_Icc_succ {R : Type*} [AddCommMonoid R]
    (u : ℕ → R) (A B : ℕ) :
    (∑ k ∈ Finset.Ioc A B, u k) = ∑ k ∈ Finset.Icc (A + 1) B, u k := by
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  · intro k hk
    rfl

/-- Correlation bound on the exact interval surviving both product cutoffs.
The length in the result is the real hull length between its first and last integers. -/
theorem norm_sum_bandPhase_correlation_le
    (a C : ℝ) (M B P Y N n₁ n₂ : ℕ)
    (ha : 0 < a) (hC : 0 < C) (hP : 0 < P) (hPlog : 1 ≤ Real.log (P : ℝ))
    (hCP : C ≤ (P : ℝ)) (hY : (Y : ℝ) ≤ C * P)
    (hM : 0 < M) (hB : B ≤ 2 * M) (hN : 0 < N)
    (hnlo : N ≤ n₁) (hnord : n₁ < n₂) (hnhi : n₂ ≤ 2 * N)
    (hlam : a * ((n₂ : ℝ) - n₁) /
      (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3) ≤ 1) :
    let lo := max M (max (P / n₁) (P / n₂))
    let hi := min B (min (Y / n₁) (Y / n₂))
    let lam := a * ((n₂ : ℝ) - n₁) /
      (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
    ‖∑ m ∈ Finset.Ioc M B,
        bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)‖ ≤
      10 * (256 * (hi - (lo + 1) : ℕ) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  dsimp only
  let lo := max M (max (P / n₁) (P / n₂))
  let hi := min B (min (Y / n₁) (Y / n₂))
  let lam := a * ((n₂ : ℝ) - n₁) /
    (32 * (N : ℝ) * (M : ℝ) ^ 2 * (Real.log (P : ℝ)) ^ 3)
  have hn₁ : 0 < n₁ := hN.trans_le hnlo
  have hn₂ : 0 < n₂ := hn₁.trans hnord
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hPreal : (0 : ℝ) < P := by exact_mod_cast hP
  have hnordreal : (n₁ : ℝ) < n₂ := by exact_mod_cast hnord
  have hlogPpos : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hPlog
  have hlampos : 0 < lam := by
    dsimp [lam]
    exact div_pos (mul_pos ha (sub_pos.mpr hnordreal)) (by positivity)
  rw [sum_bandPhase_correlation a M B P Y n₁ n₂ hn₁ hn₂]
  change ‖∑ m ∈ Finset.Ioc lo hi,
    phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ))‖ ≤ _
  by_cases hli : lo < hi
  · rw [sum_Ioc_eq_sum_Icc_succ]
    apply norm_sum_reciprocalLogCorrelation_Icc_le a (Real.log (P : ℝ))
      (M : ℝ) (N : ℝ) (n₁ : ℝ) (n₂ : ℝ) (lo + 1) hi
      ha hPlog hMreal hNreal
      (by exact_mod_cast hnlo) (by exact_mod_cast hnord) (by exact_mod_cast hnhi)
      (by omega) hlam
    · intro x hx
      have hxlo : ((max M (max (P / n₁) (P / n₂)) + 1 : ℕ) : ℝ) ≤ x := by
        simpa only [lo] using hx.1
      have hxhi : x ≤ ((min B (min (Y / n₁) (Y / n₂)) : ℕ) : ℝ) := by
        simpa only [hi] using hx.2
      rcases correlation_real_hull_bounds M B P Y n₁ n₂ hn₁ hn₂ x hxlo hxhi with
        ⟨hxM, hxB, hp₁lo, hp₁hi, hp₂lo, hp₂hi⟩
      refine ⟨hxM.le, hxB.trans ?_⟩
      exact_mod_cast hB
    · intro x hx
      have hxlo : ((max M (max (P / n₁) (P / n₂)) + 1 : ℕ) : ℝ) ≤ x := by
        simpa only [lo] using hx.1
      have hxhi : x ≤ ((min B (min (Y / n₁) (Y / n₂)) : ℕ) : ℝ) := by
        simpa only [hi] using hx.2
      rcases correlation_real_hull_bounds M B P Y n₁ n₂ hn₁ hn₂ x hxlo hxhi with
        ⟨hxM, hxB, hp₁lo, hp₁hi, hp₂lo, hp₂hi⟩
      constructor
      · exact Real.log_le_log hPreal hp₁lo.le
      · calc
          Real.log ((n₂ : ℝ) * x) ≤ Real.log (C * P) :=
            Real.log_le_log (mul_pos (by exact_mod_cast hn₂) (hMreal.trans hxM))
              (hp₂hi.trans hY)
          _ = Real.log C + Real.log (P : ℝ) := Real.log_mul hC.ne' hPreal.ne'
          _ ≤ 2 * Real.log (P : ℝ) := by
            linarith [Real.log_le_log hC hCP]
  · rw [Finset.Ioc_eq_empty hli, Finset.sum_empty, norm_zero]
    positivity

end
end Erdos878.TrackB
