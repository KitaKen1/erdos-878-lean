import Erdos878.TrackBCurvature
import Erdos878.TrackBBilinear
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Track B: the nonlinear phase in the finite correlation sums

This connects the derivative calculation to the complex weight in the exact Vaughan
decomposition. Product cutoffs remain in place when conjugate phases are multiplied.
-/

namespace Erdos878.TrackB
open Finset
open scoped ComplexConjugate
noncomputable section

def phaseCharacter (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

def reciprocalLogWeight (a : ℝ) (n : ℕ) : ℂ := phaseCharacter (a / Real.log (n : ℝ))

@[simp] theorem norm_phaseCharacter (t : ℝ) : ‖phaseCharacter t‖ = 1 := by
  simp [phaseCharacter, Complex.norm_exp]

@[simp] theorem norm_reciprocalLogWeight (a : ℝ) (n : ℕ) : ‖reciprocalLogWeight a n‖ = 1 :=
  norm_phaseCharacter _

theorem phaseCharacter_mul_conj (s t : ℝ) :
    phaseCharacter s * conj (phaseCharacter t) = phaseCharacter (s - t) := by
  unfold phaseCharacter
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub,
    Complex.ofReal_mul]
  ring

theorem reciprocalLogWeight_mul_conj (a : ℝ) (m n₁ n₂ : ℕ) :
    reciprocalLogWeight a (m * n₁) * conj (reciprocalLogWeight a (m * n₂)) =
      phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ)) := by
  unfold reciprocalLogWeight reciprocalLogCorrelation reciprocalLogPhase
  rw [phaseCharacter_mul_conj]
  simp only [Nat.cast_mul, mul_comm (m : ℝ)]

def bandPhase (a : ℝ) (P Y m n : ℕ) : ℂ :=
  if P < m * n ∧ m * n ≤ Y then reciprocalLogWeight a (m * n) else 0

/-- The phase products occurring when the squared inner sum is expanded. -/
theorem bandPhase_mul_conj (a : ℝ) (P Y m n₁ n₂ : ℕ) :
    bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂) =
      if P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y then
        phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ)) else 0 := by
  have hcond : (P < m * n₁ ∧ m * n₁ ≤ Y ∧ P < m * n₂ ∧ m * n₂ ≤ Y) =
      ((P < m * n₁ ∧ m * n₁ ≤ Y) ∧ (P < m * n₂ ∧ m * n₂ ≤ Y)) :=
    propext and_assoc.symm
  simp only [hcond]
  by_cases h₁ : P < m * n₁ ∧ m * n₁ ≤ Y <;>
    by_cases h₂ : P < m * n₂ ∧ m * n₂ ≤ Y <;>
    simp [bandPhase, h₁, h₂, reciprocalLogWeight_mul_conj]

/-- A correlation of the actual cutoff weights is an exponential sum of the
difference phase on the exact interval needed for the second-derivative test. -/
theorem sum_bandPhase_correlation (a : ℝ) (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (∑ m ∈ Ioc M B, bandPhase a P Y m n₁ * conj (bandPhase a P Y m n₂)) =
      ∑ m ∈ Ioc (max M (max (P / n₁) (P / n₂)))
        (min B (min (Y / n₁) (Y / n₂))),
          phaseCharacter (reciprocalLogCorrelation a (n₁ : ℝ) (n₂ : ℝ) (m : ℝ)) := by
  simp_rw [bandPhase_mul_conj]
  exact sum_correlation_product_filter_eq_Ioc M B P Y n₁ n₂ hn₁ hn₂ _

/-- Every real point between the first and last allowed integers stays in the
original product band. The `+1` at the lower endpoint is essential. -/
theorem real_product_bounds_of_div_hull (P Y n : ℕ) (hn : 0 < n) (x : ℝ)
    (hlo : ((P / n + 1 : ℕ) : ℝ) ≤ x) (hhi : x ≤ ((Y / n : ℕ) : ℝ)) :
    (P : ℝ) < (n : ℝ) * x ∧ (n : ℝ) * x ≤ (Y : ℝ) := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · have hnat : P < n * (P / n + 1) := Nat.lt_mul_div_succ P hn
    have hreal : (P : ℝ) < (n : ℝ) * ((P / n + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    exact hreal.trans_le (mul_le_mul_of_nonneg_left hlo hnR)
  · have hnat : n * (Y / n) ≤ Y := Nat.mul_div_le Y n
    have hreal : (n : ℝ) * ((Y / n : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hnat
    exact (mul_le_mul_of_nonneg_left hhi hnR).trans hreal

/-- Continuous hull of the exact correlation interval; valid also when the hull is empty. -/
theorem correlation_real_hull_bounds (M B P Y n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (x : ℝ)
    (hlo : ((max M (max (P / n₁) (P / n₂)) + 1 : ℕ) : ℝ) ≤ x)
    (hhi : x ≤ ((min B (min (Y / n₁) (Y / n₂)) : ℕ) : ℝ)) :
    (M : ℝ) < x ∧ x ≤ (B : ℝ) ∧
      (P : ℝ) < (n₁ : ℝ) * x ∧ (n₁ : ℝ) * x ≤ (Y : ℝ) ∧
      (P : ℝ) < (n₂ : ℝ) * x ∧ (n₂ : ℝ) * x ≤ (Y : ℝ) := by
  have hlo₁ : ((P / n₁ + 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.add_le_add_right ((le_max_left _ _).trans (le_max_right _ _)) 1)).trans hlo
  have hlo₂ : ((P / n₂ + 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.add_le_add_right ((le_max_right _ _).trans (le_max_right _ _)) 1)).trans hlo
  have hhi₁ : x ≤ ((Y / n₁ : ℕ) : ℝ) :=
    hhi.trans (Nat.cast_le.mpr ((min_le_right _ _).trans (min_le_left _ _)))
  have hhi₂ : x ≤ ((Y / n₂ : ℕ) : ℝ) :=
    hhi.trans (Nat.cast_le.mpr ((min_le_right _ _).trans (min_le_right _ _)))
  have hb₁ := real_product_bounds_of_div_hull P Y n₁ hn₁ x hlo₁ hhi₁
  have hb₂ := real_product_bounds_of_div_hull P Y n₂ hn₂ x hlo₂ hhi₂
  refine ⟨?_, hhi.trans (Nat.cast_le.mpr (min_le_left _ _)), hb₁.1, hb₁.2, hb₂.1, hb₂.2⟩
  have hnat : M < max M (max (P / n₁) (P / n₂)) + 1 :=
    Nat.lt_succ_of_le (le_max_left _ _)
  exact (Nat.cast_lt.mpr hnat).trans_le hlo

end
end Erdos878.TrackB
