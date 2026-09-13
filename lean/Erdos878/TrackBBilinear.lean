/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license; see LICENSE at the publication package root.

The first lemma is adapted from gersh/ternary-goldbach-lean, commit
27df23af6a712895f22204d0d81102baa74f0ebe,
MathExtras/NumberTheory/Vinogradov/HardCutoffTypeIIQSensitive.lean.
Modified: standalone namespace and imports. The later arbitrary-weight interfaces are local.
-/
import Erdos878.TrackBDyadic

/-!
# Track B: exact weighted convolution and Type-II box decomposition

This connects the arithmetic-function identity to finite rectangular sums with the original
product cutoff retained. The input weight remains arbitrary; no linear-phase assumption occurs.
-/

namespace Erdos878.TrackB
open Finset
open scoped ArithmeticFunction
noncomputable section

/-- **Hyperbola swap.**  `Σ_{m ≤ M} Σ_{e ∣ m} F(e, m) = Σ_{e ≤ M} Σ_{f ≤ M/e} F(e, ef)`. -/
theorem sum_Ioc_divisors_swap (M : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ m ∈ Finset.Ioc 0 M, ∑ e ∈ m.divisors, F e m =
      ∑ e ∈ Finset.Ioc 0 M, ∑ f ∈ Finset.Ioc 0 (M / e), F e (e * f) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.2, p.1 / p.2⟩)
    (j := fun p => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hm0, hmM⟩, hdvd, hne⟩ := hp
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hdvd hm0
    refine ⟨⟨he0, le_trans (Nat.le_of_dvd hm0 hdvd) hmM⟩, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hm0 hdvd) he0
    · exact Nat.div_le_div_right hmM
  · rintro ⟨e, f⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨he0, heM⟩, hf0, hfM⟩ := hp
    have hefM : e * f ≤ M := by
      have hfe := (Nat.le_div_iff_mul_le he0).mp hfM
      calc e * f = f * e := Nat.mul_comm e f
        _ ≤ M := hfe
    exact ⟨⟨by positivity, hefM⟩, Dvd.intro f rfl, by positivity⟩
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp
    obtain ⟨_, hdvd, _⟩ := hp
    simp [Nat.mul_div_cancel' hdvd]
  · rintro ⟨e, f⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc] at hp
    obtain ⟨⟨he0, _⟩, _, _⟩ := hp
    simp [Nat.mul_div_cancel_left f he0]
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp
    obtain ⟨_, hdvd, _⟩ := hp
    simp [Nat.mul_div_cancel' hdvd]


/-- Convolution summed on a finite prefix, with an arbitrary complex weight. -/
theorem weightedArithmeticSum_convolution_Ioc
    (a b : ArithmeticFunction ℝ) (Y : ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc 0 Y) w (a * b) =
      ∑ m ∈ Ioc 0 Y, ∑ n ∈ Ioc 0 (Y / m),
        (a m : ℂ) * (b n : ℂ) * w (m * n) := by
  unfold weightedArithmeticSum
  have hexpand :
      (∑ r ∈ Ioc 0 Y, ((a * b) r : ℂ) * w r) =
        ∑ r ∈ Ioc 0 Y, ∑ m ∈ r.divisors,
          (a m : ℂ) * (b (r / m) : ℂ) * w r := by
    apply sum_congr rfl
    intro r _
    simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.sum_mul]
    exact Nat.sum_divisorsAntidiagonal (fun m n ↦ (a m : ℂ) * (b n : ℂ) * w r)
  rw [hexpand]
  rw [sum_Ioc_divisors_swap]
  apply sum_congr rfl
  intro m hm
  have hmpos := (mem_Ioc.mp hm).1
  apply sum_congr rfl
  intro n _
  rw [Nat.mul_div_cancel_left n hmpos]

/-- The hyperbolic upper bound is exactly a filter in the full finite rectangle. -/
theorem Ioc_div_eq_product_filter (Y m : ℕ) (hm : 0 < m) :
    Ioc 0 (Y / m) = {n ∈ Ioc 0 Y | m * n ≤ Y} := by
  ext n
  simp only [mem_Ioc, mem_filter]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨⟨hn, h.trans (Nat.div_le_self Y m)⟩, ?_⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp h
  · rintro ⟨⟨hn, _⟩, h⟩
    exact ⟨hn, (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using h)⟩

/-- The weight on the product-cutoff rectangle. -/
def productBandTerm (a b : ArithmeticFunction ℝ) (P Y : ℕ) (w : ℕ → ℂ)
    (m n : ℕ) : ℂ :=
  if P < m * n ∧ m * n ≤ Y then (a m : ℂ) * (b n : ℂ) * w (m * n) else 0

/-- Swapping the variables also swaps the coefficient sequences, with no change to the phase. -/
theorem productBandTerm_swap (a b : ArithmeticFunction ℝ) (P Y : ℕ)
    (w : ℕ → ℂ) (m n : ℕ) :
    productBandTerm a b P Y w m n = productBandTerm b a P Y w n m := by
  unfold productBandTerm
  rw [Nat.mul_comm n m]
  split_ifs <;> ring

/-- A box may be oriented with the longer variable outside the inner sum. -/
theorem sum_productBandTerm_swap (a b : ArithmeticFunction ℝ) (P Y : ℕ)
    (w : ℕ → ℂ) (I J : Finset ℕ) :
    (∑ m ∈ I, ∑ n ∈ J, productBandTerm a b P Y w m n) =
      ∑ n ∈ J, ∑ m ∈ I, productBandTerm b a P Y w n m := by
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro m _
  exact productBandTerm_swap a b P Y w m n

/-- Exact band-to-rectangle conversion; valid even when the band is empty. -/
theorem weightedArithmeticSum_convolution_band
    (a b : ArithmeticFunction ℝ) (P Y : ℕ) (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc P Y) w (a * b) =
      ∑ m ∈ Ioc 0 Y, ∑ n ∈ Ioc 0 Y, productBandTerm a b P Y w m n := by
  have hband : {n ∈ Ioc 0 Y | P < n} = Ioc P Y := by
    ext n
    simp only [mem_filter, mem_Ioc]
    omega
  have hweight :
      weightedArithmeticSum (Ioc P Y) w (a * b) =
        weightedArithmeticSum (Ioc 0 Y) (fun n ↦ if P < n then w n else 0) (a * b) := by
    unfold weightedArithmeticSum
    rw [← hband, sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : P < n <;> simp only [hn, ite_true, ite_false, mul_zero]
  rw [hweight, weightedArithmeticSum_convolution_Ioc]
  apply sum_congr rfl
  intro m hm
  rw [Ioc_div_eq_product_filter Y m (mem_Ioc.mp hm).1, sum_filter]
  apply sum_congr rfl
  intro n _
  unfold productBandTerm
  by_cases hlo : P < m * n <;> by_cases hhi : m * n ≤ Y <;> simp [hlo, hhi]

/-- The actual Vaughan tail written as dyadic boxes with its sharp product cutoff. -/
theorem weightedArithmeticSum_typeII_eq_dyadic (U V P Y : ℕ) (hU : 1 ≤ U)
    (w : ℕ → ℂ) :
    weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V) =
      ∑ i ∈ range (Nat.log 2 Y + 1), ∑ j ∈ range (Nat.log 2 Y + 1),
        ∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) Y),
          ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y),
            productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n := by
  change weightedArithmeticSum (Ioc P Y) w (lambdaGT V * typeIICoeff U) = _
  rw [weightedArithmeticSum_convolution_band]
  apply sum_sum_Ioc_eq_dyadic
  · intro n
    simp [productBandTerm, lambdaGT_apply]
  · intro m
    simp [productBandTerm, typeIICoeff_eq_zero_of_le U 1 hU]

/-- Box norms control the full Type-II tail with no dropped product restrictions. -/
theorem norm_weightedArithmeticSum_typeII_le_dyadic (U V P Y : ℕ) (hU : 1 ≤ U)
    (w : ℕ → ℂ) :
    ‖weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V)‖ ≤
      ∑ i ∈ range (Nat.log 2 Y + 1), ∑ j ∈ range (Nat.log 2 Y + 1),
        ‖∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) Y),
          ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y),
            productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n‖ := by
  rw [weightedArithmeticSum_typeII_eq_dyadic U V P Y hU w]
  exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_sum_le _ _)

/-- Uniform box estimates lose at most the explicitly accounted-for `9 log² Y` factor.
The hypothesis concerns the actual finite boxes with their product restrictions. -/
theorem norm_weightedArithmeticSum_typeII_le_of_box_bound
    (U V P Y : ℕ) (hU : 1 ≤ U) (hY : 2 ≤ Y) (w : ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbox : ∀ i ∈ range (Nat.log 2 Y + 1), ∀ j ∈ range (Nat.log 2 Y + 1),
      ‖∑ m ∈ Ioc (2 ^ i) (min (2 ^ (i + 1)) Y),
        ∑ n ∈ Ioc (2 ^ j) (min (2 ^ (j + 1)) Y),
          productBandTerm (lambdaGT V) (typeIICoeff U) P Y w m n‖ ≤ B) :
    ‖weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V)‖ ≤
      9 * Real.log (Y : ℝ) ^ 2 * B := by
  calc
    ‖weightedArithmeticSum (Ioc P Y) w (vaughanTypeII U V)‖ ≤
        ∑ _i ∈ range (Nat.log 2 Y + 1), ∑ _j ∈ range (Nat.log 2 Y + 1), B :=
      (norm_weightedArithmeticSum_typeII_le_dyadic U V P Y hU w).trans
        (sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ hbox i hi j hj)
    _ = ((Nat.log 2 Y + 1 : ℕ) : ℝ) ^ 2 * B := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring
    _ ≤ (3 * Real.log (Y : ℝ)) ^ 2 * B :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (dyadicBoxCount_le_three_log Y hY) 2) hB
    _ = _ := by ring

end
end Erdos878.TrackB
