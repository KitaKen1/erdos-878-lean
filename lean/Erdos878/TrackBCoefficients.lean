import Erdos878.TrackBVaughan
import Erdos878.TrackBDivisorMoment

/-!
# Track B: bounds and support for the actual Vaughan coefficients

The Type-I cross coefficient is bounded by `log n`; the Type-II coefficients have
dyadic square sums of size `M log² M` and `M log³ M`. All bounds are uniform in
the cutoff parameters. No cancellation estimate or hypothesis about primes is used.
-/

namespace Erdos878.TrackB
open scoped ArithmeticFunction BigOperators

/-- The coefficient after grouping the two short factors in the Type-I cross term. -/
noncomputable def typeICoeff (U V : ℕ) : ArithmeticFunction ℝ :=
  muLE U * lambdaLE V

/-- The divisor-sum coefficient of the Type-II term. -/
noncomputable def typeIICoeff (U : ℕ) : ArithmeticFunction ℝ :=
  muGT U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

theorem abs_muLE_le_one (U n : ℕ) : |muLE U n| ≤ 1 := by
  by_cases h : n ≤ U
  · simp only [muLE_apply, ite_eq_left h]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp [h]

theorem abs_muGT_le_one (U n : ℕ) : |muGT U n| ≤ 1 := by
  by_cases h : U < n
  · simp only [muGT_apply, ite_eq_left h]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp [h]

theorem lambdaLE_nonneg (V n : ℕ) : 0 ≤ lambdaLE V n := by
  simp only [lambdaLE_apply]
  split_ifs <;> positivity

theorem lambdaGT_nonneg (V n : ℕ) : 0 ≤ lambdaGT V n := by
  simp only [lambdaGT_apply]
  split_ifs <;> positivity

theorem lambdaLE_le_vonMangoldt (V n : ℕ) :
    lambdaLE V n ≤ ArithmeticFunction.vonMangoldt n := by
  simp only [lambdaLE_apply]
  split_ifs <;> first | exact le_rfl | exact ArithmeticFunction.vonMangoldt_nonneg

theorem lambdaGT_le_log (V n : ℕ) : lambdaGT V n ≤ Real.log n := by
  simp only [lambdaGT_apply]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_le_log
  · exact Real.log_natCast_nonneg n

theorem vaughanTypeILambda_eq (U V : ℕ) :
    vaughanTypeILambda U V =
      typeICoeff U V * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  unfold vaughanTypeILambda typeICoeff
  ring

/-- Grouping the short factors introduces no divisor-function loss: the coefficient
is bounded by the exact divisor sum of von Mangoldt, namely `log n`. -/
theorem abs_typeICoeff_le_log (U V n : ℕ) : |typeICoeff U V n| ≤ Real.log n := by
  rw [typeICoeff, ArithmeticFunction.mul_apply]
  calc
    |∑ ab ∈ n.divisorsAntidiagonal, muLE U ab.1 * lambdaLE V ab.2|
        ≤ ∑ ab ∈ n.divisorsAntidiagonal, |muLE U ab.1 * lambdaLE V ab.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt ab.2 := by
      apply Finset.sum_le_sum
      intro ab _
      rw [abs_mul, abs_of_nonneg (lambdaLE_nonneg V ab.2)]
      exact (mul_le_mul_of_nonneg_right (abs_muLE_le_one U ab.1)
        (lambdaLE_nonneg V ab.2)).trans (by simpa using lambdaLE_le_vonMangoldt V ab.2)
    _ = Real.log n := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b ↦ ArithmeticFunction.vonMangoldt b)]
      exact ArithmeticFunction.vonMangoldt_sum

theorem typeICoeff_eq_zero_of_mul_lt (U V n : ℕ) (hn : U * V < n) :
    typeICoeff U V n = 0 := by
  rw [typeICoeff, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have heq := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases ha : ab.1 ≤ U
  · have hb : ¬ ab.2 ≤ V := by
      intro hb
      have := Nat.mul_le_mul ha hb
      omega
    simp [hb]
  · simp [ha]

theorem abs_typeIICoeff_le_card_divisors (U n : ℕ) :
    |typeIICoeff U n| ≤ (n.divisors.card : ℝ) := by
  rw [typeIICoeff, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    |∑ d ∈ n.divisors, muGT U d| ≤ ∑ d ∈ n.divisors, |muGT U d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) :=
      Finset.sum_le_sum fun d _ ↦ abs_muGT_le_one U d
    _ = _ := by simp

theorem typeIICoeff_eq_zero_of_le (U n : ℕ) (hn : n ≤ U) :
    typeIICoeff U n = 0 := by
  rw [typeIICoeff, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdu : d ≤ U := (Nat.divisor_le hd).trans hn
  simp [not_lt.mpr hdu]

/-- The low von Mangoldt term disappears on every interval strictly above its cutoff. -/
theorem weightedArithmeticSum_lambdaLE_eq_zero
    (V : ℕ) (I : Finset ℕ) (w : ℕ → ℂ) (hI : ∀ n ∈ I, V < n) :
    weightedArithmeticSum I w (lambdaLE V) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  simp [not_le.mpr (hI n hn)]

/-- A uniform second-moment bound for the actual Möbius divisor coefficient. -/
theorem sum_typeIICoeff_sq_le (U N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, typeIICoeff U n ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  apply le_trans _ (sum_Ioc_card_divisors_sq_le N)
  apply Finset.sum_le_sum
  intro n _
  simpa only [sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) (abs_typeIICoeff_le_card_divisors U n) 2

/-- The same estimate survives arbitrary restrictions inside a dyadic block. -/
theorem sum_typeIICoeff_sq_le_on_dyadic
    (U M : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.Ioc M (2 * M)) :
    (∑ n ∈ I, typeIICoeff U n ^ 2) ≤
      2 * (M : ℝ) * (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
  have hsub : I ⊆ Finset.Ioc 0 (2 * M) :=
    hI.trans (Finset.Ioc_subset_Ioc (Nat.zero_le M) le_rfl)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ sq_nonneg _)).trans ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using sum_typeIICoeff_sq_le U (2 * M)

/-- Square-sum control for the von Mangoldt coefficient on a dyadic block, including
any additional support restriction imposed by the product cutoff. -/
theorem sum_lambdaGT_sq_le_on_dyadic
    (V M : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.Ioc M (2 * M)) :
    (∑ n ∈ I, lambdaGT V n ^ 2) ≤
      (M : ℝ) * Real.log (2 * (M : ℝ) + 1) ^ 2 := by
  calc
    (∑ n ∈ I, lambdaGT V n ^ 2) ≤
        ∑ n ∈ Finset.Ioc M (2 * M), lambdaGT V n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ ↦ sq_nonneg _)
    _ ≤ ∑ _n ∈ Finset.Ioc M (2 * M), Real.log (2 * (M : ℝ) + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnM⟩ := Finset.mem_Ioc.mp hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le M).trans_lt hn0
      apply pow_le_pow_left₀ (lambdaGT_nonneg V n) _ 2
      refine (lambdaGT_le_log V n).trans (Real.log_le_log hnpos ?_)
      exact_mod_cast (show n ≤ 2 * M + 1 by omega)
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      congr 2
      omega

end Erdos878.TrackB
