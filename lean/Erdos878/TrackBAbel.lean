import Erdos878.TrackBBandCorrelation
import Mathlib.Algebra.BigOperators.Module

/-!
# Track B: a finite Abel bound for logarithmic Type-I weights

The Type-I inner sums contain the increasing weight `log k`.  This file packages
summation by parts so that a uniform bound for every unweighted prefix loses only
the expected endpoint logarithm.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

/-- Abel summation for a nonnegative increasing real weight.  If every prefix of
`g` has norm at most `B`, multiplying by `f` costs at most twice its endpoint value. -/
theorem norm_sum_range_smul_le_two_mul_endpoint
    (f : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hf0 : 0 ≤ f 0) (hf : Monotone f) (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, f i • g i‖ ≤ 2 * f n * B := by
  rw [Finset.sum_range_by_parts]
  have hflast : 0 ≤ f (n - 1) := hf0.trans (hf (Nat.zero_le _))
  have hfirst :
      ‖f (n - 1) • ∑ i ∈ Finset.range n, g i‖ ≤ f (n - 1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hflast]
    exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) hflast
  have hsecond :
      ‖∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ ≤
        (f (n - 1) - f 0) * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          ‖(f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hdiff : 0 ≤ f (i + 1) - f i := sub_nonneg.mpr (hf (Nat.le_succ i))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        apply mul_le_mul_of_nonneg_left _ hdiff
        apply hpartial
        have : i < n - 1 := Finset.mem_range.mp hi
        omega
      _ = (f (n - 1) - f 0) * B := by
        rw [← Finset.sum_mul, Finset.sum_range_sub]
  calc
    ‖f (n - 1) • ∑ i ∈ Finset.range n, g i -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ ≤
        ‖f (n - 1) • ∑ i ∈ Finset.range n, g i‖ +
          ‖∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ :=
      norm_sub_le _ _
    _ ≤ f (n - 1) * B + (f (n - 1) - f 0) * B := add_le_add hfirst hsecond
    _ = 2 * f (n - 1) * B - f 0 * B := by ring
    _ ≤ 2 * f (n - 1) * B := sub_le_self _ (mul_nonneg hf0 hB)
    _ ≤ 2 * f n * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hf (Nat.sub_le n 1)) (by norm_num)) hB

/-- The form used for logarithmic Type-I inner sums.  The input is only a
uniform bound for every unweighted prefix of the shifted interval. -/
theorem norm_sum_range_log_mul_le
    (Q n : ℕ) (g : ℕ → ℂ) (B : ℝ) (hQ : 1 ≤ Q) (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, (Real.log (Q + i : ℕ) : ℂ) * g i‖ ≤
      2 * Real.log (Q + n : ℕ) * B := by
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog0 : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQreal
  have hmono : Monotone (fun i : ℕ => Real.log (Q + i : ℕ)) := by
    intro i j hij
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_left hij Q
  have h := norm_sum_range_smul_le_two_mul_endpoint
    (fun i : ℕ => Real.log (Q + i : ℕ)) g n B hlog0 hmono hB hpartial
  simpa only [Complex.real_smul] using h

/-- Closed-interval wrapper.  Prefixes start at `A`; the harmless endpoint is
`log (B+1)`, which also covers a one-point interval without a separate case. -/
theorem norm_sum_Icc_log_mul_le
    (u : ℕ → ℂ) (A B : ℕ) (E : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hE : 0 ≤ E)
    (hpartial : ∀ r ≤ B - A + 1,
      ‖∑ i ∈ Finset.range r, u (A + i)‖ ≤ E) :
    ‖∑ k ∈ Finset.Icc A B, (Real.log (k : ℝ) : ℂ) * u k‖ ≤
      2 * Real.log (B + 1 : ℕ) * E := by
  rw [sum_Icc_eq_sum_range_shift _ A B hAB]
  have h := norm_sum_range_log_mul_le A (B - A + 1) (fun i => u (A + i)) E
    hA hE hpartial
  convert h using 1
  rw [show A + (B - A + 1) = B + 1 by omega]

/-- The logarithmically weighted reciprocal-log phase on one closed integer
interval.  This is the analytic form consumed by the logarithmic Type-I term. -/
theorem norm_sum_log_mul_reciprocalLogPhase_Icc_le
    (a n L M : ℝ) (A B : ℕ) (ha : 0 < a) (hn : 0 < n)
    (hL : 1 ≤ L) (hM : 0 < M) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hlam : a / (16 * M ^ 2 * L ^ 2) ≤ 1)
    (hbox : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ), M ≤ x ∧ x ≤ 2 * M)
    (hlog : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
      L ≤ Real.log (n * x) ∧ Real.log (n * x) ≤ 2 * L) :
    ‖∑ k ∈ Finset.Icc A B, (Real.log (k : ℝ) : ℂ) *
        phaseCharacter (reciprocalLogPhase a n k)‖ ≤
      2 * Real.log (B + 1 : ℕ) *
        (10 * (48 * (B - A : ℕ) * Real.sqrt (a / (16 * M ^ 2 * L ^ 2)) +
          1 / Real.sqrt (a / (16 * M ^ 2 * L ^ 2)))) := by
  let lam := a / (16 * M ^ 2 * L ^ 2)
  let E := 10 * (48 * (B - A : ℕ) * Real.sqrt lam + 1 / Real.sqrt lam)
  have hlampos : 0 < lam := by dsimp [lam]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply norm_sum_Icc_log_mul_le
    (fun k => phaseCharacter (reciprocalLogPhase a n k)) A B E hA hAB hE
  intro r hr
  by_cases hr0 : r = 0
  · simp [hr0, hE]
  · let C := A + r - 1
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hAC : A ≤ C := by dsimp [C]; omega
    have hCB : C ≤ B := by dsimp [C]; omega
    have hlen : C - A + 1 = r := by dsimp [C]; omega
    rw [← hlen]
    change ‖∑ i ∈ Finset.range (C - A + 1),
      (fun k : ℕ => phaseCharacter (reciprocalLogPhase a n (k : ℝ))) (A + i)‖ ≤ E
    have hsum :
        (∑ i ∈ Finset.range (C - A + 1),
          (fun k : ℕ => phaseCharacter (reciprocalLogPhase a n (k : ℝ))) (A + i)) =
          ∑ k ∈ Finset.Icc A C, phaseCharacter (reciprocalLogPhase a n (k : ℝ)) :=
      (sum_Icc_eq_sum_range_shift
        (fun k : ℕ => phaseCharacter (reciprocalLogPhase a n (k : ℝ))) A C hAC).symm
    rw [hsum]
    have ht := norm_sum_reciprocalLogPhase_Icc_le a n L M A C ha hn hL hM hAC hlam
      (fun x hx => hbox x ⟨hx.1, hx.2.trans (by exact_mod_cast hCB)⟩)
      (fun x hx => hlog x ⟨hx.1, hx.2.trans (by exact_mod_cast hCB)⟩)
    refine ht.trans ?_
    dsimp [E, lam]
    gcongr

end
end Erdos878.TrackB
