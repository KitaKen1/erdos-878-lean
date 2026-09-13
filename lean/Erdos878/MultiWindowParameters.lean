import Erdos878.GoodPairPacking
import Erdos878.PrimeMass
import Erdos878.PrimeReciprocalAbel

/-!
# Finite multi-window parameters for the sharp first question

For `k` pairs put `w = 1 / (2k + 5)`.  Pair the window

`((i+1)w, (i+2)w]`

with

`(1-(i+4)w, 1-(i+3)w]`, for `i : Fin k`.

The lemmas below package exactly the side conditions consumed by the report-scale bad-pair,
prime-mass, and positive-power-product theorems.  They also record the global separation of
all left windows from all right windows; this is what permits all selected pairs to be combined
into one admissible family without reusing a prime.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

def multiWindowDenominator (k : ℕ) : ℝ := 2 * (k : ℝ) + 5

def multiWindowWidth (k : ℕ) : ℝ := 1 / multiWindowDenominator k

def multiWindowAlpha (k : ℕ) (i : Fin k) : ℝ :=
  ((i.1 : ℝ) + 1) / multiWindowDenominator k

def multiWindowBeta (k : ℕ) (i : Fin k) : ℝ :=
  ((i.1 : ℝ) + 2) / multiWindowDenominator k

def multiWindowGamma (k : ℕ) (i : Fin k) : ℝ :=
  1 - ((i.1 : ℝ) + 4) / multiWindowDenominator k

def multiWindowDelta (k : ℕ) (i : Fin k) : ℝ :=
  1 - ((i.1 : ℝ) + 3) / multiWindowDenominator k

theorem multiWindowDenominator_pos (k : ℕ) : 0 < multiWindowDenominator k := by
  unfold multiWindowDenominator
  positivity

theorem multiWindowWidth_pos (k : ℕ) : 0 < multiWindowWidth k := by
  exact one_div_pos.mpr (multiWindowDenominator_pos k)

theorem multiWindow_alpha_pos {k : ℕ} (i : Fin k) :
    0 < multiWindowAlpha k i := by
  unfold multiWindowAlpha
  exact div_pos (by positivity) (multiWindowDenominator_pos k)

theorem multiWindow_alpha_lt_beta {k : ℕ} (i : Fin k) :
    multiWindowAlpha k i < multiWindowBeta k i := by
  unfold multiWindowAlpha multiWindowBeta
  exact (div_lt_div_iff_of_pos_right (multiWindowDenominator_pos k)).2 (by norm_num)

theorem multiWindow_beta_pos {k : ℕ} (i : Fin k) :
    0 < multiWindowBeta k i :=
  (multiWindow_alpha_pos i).trans (multiWindow_alpha_lt_beta i)

theorem multiWindow_gamma_lt_delta {k : ℕ} (i : Fin k) :
    multiWindowGamma k i < multiWindowDelta k i := by
  unfold multiWindowGamma multiWindowDelta
  have hdiv :
      ((i.1 : ℝ) + 3) / multiWindowDenominator k <
        ((i.1 : ℝ) + 4) / multiWindowDenominator k :=
    (div_lt_div_iff_of_pos_right (multiWindowDenominator_pos k)).2 (by norm_num)
  linarith

theorem multiWindow_delta_nonneg {k : ℕ} (i : Fin k) :
    0 ≤ multiWindowDelta k i := by
  have hiNat : i.1 + 1 ≤ k := Nat.succ_le_iff.mpr i.2
  have hi : (i.1 : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hiNat
  unfold multiWindowDelta
  rw [sub_nonneg]
  apply (div_le_iff₀ (multiWindowDenominator_pos k)).2
  unfold multiWindowDenominator
  nlinarith

theorem multiWindow_delta_lt_one {k : ℕ} (i : Fin k) :
    multiWindowDelta k i < 1 := by
  unfold multiWindowDelta
  have hquot : 0 < ((i.1 : ℝ) + 3) / multiWindowDenominator k :=
    div_pos (by positivity) (multiWindowDenominator_pos k)
  linarith

theorem multiWindow_beta_le_gamma {k : ℕ} (i : Fin k) :
    multiWindowBeta k i ≤ multiWindowGamma k i := by
  have hiNat : i.1 + 1 ≤ k := Nat.succ_le_iff.mpr i.2
  have hi : (i.1 : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hiNat
  unfold multiWindowBeta multiWindowGamma
  rw [le_sub_iff_add_le, ← add_div]
  apply (div_le_iff₀ (multiWindowDenominator_pos k)).2
  unfold multiWindowDenominator
  nlinarith

theorem multiWindow_beta_add_delta_lt_one {k : ℕ} (i : Fin k) :
    multiWindowBeta k i + multiWindowDelta k i < 1 := by
  have hD := multiWindowDenominator_pos k
  unfold multiWindowBeta multiWindowDelta
  have heq :
      ((i.1 : ℝ) + 2) / multiWindowDenominator k +
          (1 - ((i.1 : ℝ) + 3) / multiWindowDenominator k) =
        1 - 1 / multiWindowDenominator k := by
    field_simp [hD.ne']
    ring
  rw [heq]
  exact sub_lt_self 1 (one_div_pos.mpr hD)

theorem multiWindow_left_width {k : ℕ} (i : Fin k) :
    multiWindowBeta k i - multiWindowAlpha k i = multiWindowWidth k := by
  unfold multiWindowBeta multiWindowAlpha multiWindowWidth
  ring

theorem multiWindow_right_width {k : ℕ} (i : Fin k) :
    multiWindowDelta k i - multiWindowGamma k i = multiWindowWidth k := by
  unfold multiWindowDelta multiWindowGamma multiWindowWidth
  ring

/-- Every left-window upper exponent lies strictly below every right-window lower exponent. -/
theorem multiWindow_beta_lt_gamma_cross {k : ℕ} (i j : Fin k) :
    multiWindowBeta k i < multiWindowGamma k j := by
  have hiNat : i.1 + 1 ≤ k := Nat.succ_le_iff.mpr i.2
  have hjNat : j.1 + 1 ≤ k := Nat.succ_le_iff.mpr j.2
  have hi : (i.1 : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hiNat
  have hj : (j.1 : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjNat
  unfold multiWindowBeta multiWindowGamma
  rw [lt_sub_iff_add_lt, ← add_div]
  apply (div_lt_iff₀ (multiWindowDenominator_pos k)).2
  unfold multiWindowDenominator
  nlinarith

theorem multiWindow_beta_le_alpha_of_lt {k : ℕ} {i j : Fin k} (hij : i.1 < j.1) :
    multiWindowBeta k i ≤ multiWindowAlpha k j := by
  have hij' : i.1 + 1 ≤ j.1 := hij
  have hijR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hij'
  unfold multiWindowBeta multiWindowAlpha
  apply (div_le_div_iff_of_pos_right (multiWindowDenominator_pos k)).2
  linarith

theorem multiWindow_delta_le_gamma_of_lt {k : ℕ} {i j : Fin k} (hij : i.1 < j.1) :
    multiWindowDelta k j ≤ multiWindowGamma k i := by
  have hij' : i.1 + 1 ≤ j.1 := hij
  have hijR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hij'
  unfold multiWindowDelta multiWindowGamma
  have hdiv :
      ((i.1 : ℝ) + 4) / multiWindowDenominator k ≤
        ((j.1 : ℝ) + 3) / multiWindowDenominator k :=
    (div_le_div_iff_of_pos_right (multiWindowDenominator_pos k)).2 (by linarith)
  linarith

/-- A prime belongs to at most one left window of the multi-window family. -/
theorem eq_of_mem_multiWindow_left
    {k : ℕ} {T : ℝ} (hT : 1 ≤ T) {i j : Fin k} {p : ℕ}
    (hi : p ∈ primeWindow T (multiWindowAlpha k i) (multiWindowBeta k i))
    (hj : p ∈ primeWindow T (multiWindowAlpha k j) (multiWindowBeta k j)) :
    i = j := by
  apply Fin.ext
  by_contra hne
  have hp : p.Prime := (Finset.mem_filter.mp hi).2.1
  have hpi := primeWindow_log_bounds hi hp.pos
  have hpj := primeWindow_log_bounds hj hp.pos
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hpow := Real.rpow_le_rpow_of_exponent_le hT
      (multiWindow_beta_le_alpha_of_lt hij)
    change Real.rpow T (multiWindowBeta k i) ≤
      Real.rpow T (multiWindowAlpha k j) at hpow
    linarith
  · have hpow := Real.rpow_le_rpow_of_exponent_le hT
      (multiWindow_beta_le_alpha_of_lt hji)
    change Real.rpow T (multiWindowBeta k j) ≤
      Real.rpow T (multiWindowAlpha k i) at hpow
    linarith

/-- A prime belongs to at most one right window of the multi-window family. -/
theorem eq_of_mem_multiWindow_right
    {k : ℕ} {T : ℝ} (hT : 1 ≤ T) {i j : Fin k} {p : ℕ}
    (hi : p ∈ primeWindow T (multiWindowGamma k i) (multiWindowDelta k i))
    (hj : p ∈ primeWindow T (multiWindowGamma k j) (multiWindowDelta k j)) :
    i = j := by
  apply Fin.ext
  by_contra hne
  have hp : p.Prime := (Finset.mem_filter.mp hi).2.1
  have hpi := primeWindow_log_bounds hi hp.pos
  have hpj := primeWindow_log_bounds hj hp.pos
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hpow := Real.rpow_le_rpow_of_exponent_le hT
      (multiWindow_delta_le_gamma_of_lt hij)
    change Real.rpow T (multiWindowDelta k j) ≤
      Real.rpow T (multiWindowGamma k i) at hpow
    linarith
  · have hpow := Real.rpow_le_rpow_of_exponent_le hT
      (multiWindow_delta_le_gamma_of_lt hji)
    change Real.rpow T (multiWindowDelta k i) ≤
      Real.rpow T (multiWindowGamma k j) at hpow
    linarith

/-- The complete report-scale parameter package for each one of the `k` window pairs. -/
theorem multiWindow_report_parameter_conditions {k : ℕ} (i : Fin k) :
    0 < multiWindowAlpha k i ∧
    multiWindowAlpha k i < multiWindowBeta k i ∧
    0 < multiWindowBeta k i ∧
    multiWindowBeta k i ≤ multiWindowGamma k i ∧
    multiWindowGamma k i < multiWindowDelta k i ∧
    0 ≤ multiWindowDelta k i ∧
    multiWindowDelta k i < 1 ∧
    multiWindowBeta k i + multiWindowDelta k i < 1 := by
  exact ⟨multiWindow_alpha_pos i, multiWindow_alpha_lt_beta i,
    multiWindow_beta_pos i, multiWindow_beta_le_gamma i,
    multiWindow_gamma_lt_delta i, multiWindow_delta_nonneg i,
    multiWindow_delta_lt_one i, multiWindow_beta_add_delta_lt_one i⟩

end

end Erdos878

#print axioms Erdos878.multiWindow_report_parameter_conditions
#print axioms Erdos878.multiWindow_beta_lt_gamma_cross
