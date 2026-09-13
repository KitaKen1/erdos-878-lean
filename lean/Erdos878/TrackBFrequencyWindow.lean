import Erdos878.TrackBLogSaving

/-!
# Track B: signed frequencies and the finite harmonic range

This is the concrete exponential-sum interface used by the planned finite
Fourier argument. It does not yet construct a prime in the desired phase window.
-/

namespace Erdos878.TrackB
open Filter Finset
open scoped ComplexConjugate
noncomputable section

/-- The eventual harmonic range is inhabited: its middle scale and frequency 1 qualify. -/
theorem trackBHarmonicWindow_nonempty (P : ℕ) (h : trackBScaleCondition P) :
    0 < (P : ℝ)/Real.log (P : ℝ)^128 ∧
    (P : ℝ)/Real.log (P : ℝ)^130 ≤ (P : ℝ)/Real.log (P : ℝ)^128 ∧
    (P : ℝ)/Real.log (P : ℝ)^128 ≤ (P : ℝ)/Real.log (P : ℝ)^126 ∧
    (1 : ℝ) ≤ Real.log (P : ℝ)^6 := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by
    have := trackBScaleCondition_sixteen_le P h; omega)
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le h.1
  exact ⟨div_pos hP (pow_pos hL _),
    div_le_div_of_nonneg_left hP.le (pow_pos hL _) (pow_le_pow_right₀ h.1 (by decide)),
    div_le_div_of_nonneg_left hP.le (pow_pos hL _) (pow_le_pow_right₀ h.1 (by decide)),
    one_le_pow₀ h.1⟩

theorem phaseCharacter_neg_eq_conj (a : ℝ) : phaseCharacter (-a) = conj (phaseCharacter a) := by
  have h := (phaseCharacter_mul_conj 0 a).symm
  simpa only [show phaseCharacter 0 = 1 by simp [phaseCharacter], one_mul, zero_sub] using h

/-- Negating the frequency conjugates the sum because the arithmetic coefficients are real. -/
theorem weightedArithmeticSum_neg_frequency (A : ArithmeticFunction ℝ) (a : ℝ) (I : Finset ℕ) :
    weightedArithmeticSum I (reciprocalLogWeight (-a)) A =
      conj (weightedArithmeticSum I (reciprocalLogWeight a) A) := by
  unfold weightedArithmeticSum
  simp only [map_sum, map_mul, Complex.conj_ofReal, reciprocalLogWeight, neg_div,
    phaseCharacter_neg_eq_conj]

theorem norm_weightedArithmeticSum_abs_frequency (A : ArithmeticFunction ℝ) (a : ℝ) (I : Finset ℕ) :
    ‖weightedArithmeticSum I (reciprocalLogWeight |a|) A‖ =
      ‖weightedArithmeticSum I (reciprocalLogWeight a) A‖ := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha), weightedArithmeticSum_neg_frequency, Complex.norm_conj]

theorem eventually_vonMangoldt_signed_logSaving (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ a : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ |a| → |a| ≤ (P : ℝ)/Real.log (P : ℝ)^120 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a) ArithmeticFunction.vonMangoldt‖ ≤
        1000000*C^2*P/Real.log (P : ℝ)^25 := by
  filter_upwards [eventually_vonMangoldt_logSaving C hC] with P hp
  intro a hlo hhi Y X hPX hX hYX
  simpa only [norm_weightedArithmeticSum_abs_frequency] using hp |a| hlo hhi Y X hPX hX hYX

/-- The paper's frequency window: `P/L^130 ≤ t ≤ P/L^126`, `0 < |k| ≤ L^6`.
The bound holds simultaneously for all these integers and all partial endpoints. -/
theorem eventually_vonMangoldt_harmonics_logSaving (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t → t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ k : ℤ, k ≠ 0 → |(k : ℝ)| ≤ Real.log (P : ℝ)^6 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight ((k : ℝ)*t))
        ArithmeticFunction.vonMangoldt‖ ≤ 1000000*C^2*P/Real.log (P : ℝ)^25 := by
  filter_upwards [eventually_vonMangoldt_signed_logSaving C hC,
    eventually_trackBScaleCondition] with P hp hs
  intro t htlo hthi k hk hkhi Y X hPX hX hYX
  have hP : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by
    have := trackBScaleCondition_sixteen_le P hs; omega)
  have hL : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hs.1
  have ht : 0 < t := (div_pos hP (pow_pos hL _)).trans_le htlo
  have hklo : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hprodlo : (P : ℝ)/Real.log (P : ℝ)^130 ≤ |(k : ℝ)*t| := by
    rw [abs_mul, abs_of_pos ht]
    exact htlo.trans (by nlinarith)
  have hprodhi : |(k : ℝ)*t| ≤ (P : ℝ)/Real.log (P : ℝ)^120 := by
    rw [abs_mul, abs_of_pos ht]
    calc
      _ ≤ Real.log (P : ℝ)^6 * ((P : ℝ)/Real.log (P : ℝ)^126) :=
        mul_le_mul hkhi hthi ht.le (by positivity)
      _ = _ := by field_simp
  exact hp ((k : ℝ)*t) hprodlo hprodhi Y X hPX hX hYX

end
end Erdos878.TrackB
