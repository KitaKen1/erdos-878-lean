import Erdos878.TrackBPrimeSelection

/-!
# Track B: convert the phase window into prime-power bounds

This is the deterministic bridge after prime selection. It identifies the real
size of `p ^ floor(t / log p)` without an asymptotic approximation.
-/

namespace Erdos878.TrackB
open Filter Finset
noncomputable section

def phaseExponent (t : ℝ) (p : ℕ) : ℕ :=
  ⌊t/Real.log (p : ℝ)⌋₊

theorem phaseExponent_mul_log (t : ℝ) {p : ℕ} (hp : 1 < p) (ht : 0 ≤ t) :
    (phaseExponent t p : ℝ)*Real.log (p : ℝ) =
      t - Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  have hu : 0 ≤ t/Real.log (p : ℝ) := div_nonneg ht hlog.le
  have hfloor : (phaseExponent t p : ℝ) =
      ((⌊t/Real.log (p : ℝ)⌋ : ℤ) : ℝ) := by
    exact natCast_floor_eq_intCast_floor hu
  calc
    (phaseExponent t p : ℝ)*Real.log (p : ℝ) =
        ((⌊t/Real.log (p : ℝ)⌋ : ℤ) : ℝ)*Real.log (p : ℝ) := by rw [hfloor]
    _ = (t/Real.log (p : ℝ) - Int.fract (t/Real.log (p : ℝ)))*
          Real.log (p : ℝ) := by
      rw [show ((⌊t/Real.log (p : ℝ)⌋ : ℤ) : ℝ) =
        t/Real.log (p : ℝ) - Int.fract (t/Real.log (p : ℝ)) by
          linarith [Int.floor_add_fract (t/Real.log (p : ℝ))]]
    _ = _ := by rw [sub_mul, div_mul_cancel₀ t hlog.ne']

theorem phaseExponent_power_eq_exp (t : ℝ) {p : ℕ} (hp : 1 < p) (ht : 0 ≤ t) :
    ((p : ℝ)^phaseExponent t p) =
      Real.exp (t - Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  calc
    ((p : ℝ)^phaseExponent t p) =
        Real.exp (Real.log ((p : ℝ)^phaseExponent t p)) :=
      (Real.exp_log (pow_pos hpR _)).symm
    _ = Real.exp ((phaseExponent t p : ℝ)*Real.log (p : ℝ)) := by
      rw [Real.log_pow]
    _ = _ := congrArg Real.exp (phaseExponent_mul_log t hp ht)

/-- A selected phase-window prime has a prime power in an explicit narrow
multiplicative band. The constants `4` and `1` leave room for `p ≤ 16P`. -/
theorem goodPrime_phaseExponent_power_bounds (P : ℕ) (t : ℝ)
    (hscale : trackBScaleCondition P) (ht : 0 ≤ t) {p : ℕ}
    (hp : p ∈ logSquaredGoodPrimes P t) :
    Real.exp (t - 4/Real.log (P : ℝ)) ≤ ((p : ℝ)^phaseExponent t p) ∧
      ((p : ℝ)^phaseExponent t p) ≤ Real.exp (t - 1/Real.log (P : ℝ)) := by
  let L := Real.log (P : ℝ)
  have hP : 0 < P := by have := trackBScaleCondition_sixteen_le P hscale; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hL : 0 < L := by dsimp [L]; exact zero_lt_one.trans_le hscale.1
  have hpfilter := mem_filter.mp hp
  have hpprime : p.Prime := hpfilter.2
  have hpbase := mem_filter.mp hpfilter.1
  have hpband := mem_Ioc.mp hpbase.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpprime.one_lt)
  have hloglower : L ≤ Real.log (p : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
      (show (P : ℝ) ∈ Set.Ioi 0 by exact hPr)
      (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
    exact_mod_cast hpband.1.le
  have hlogupper : Real.log (p : ℝ) ≤ 2*L := by
    have hp_le : p ≤ 16*P := hpband.2
    have hmono : Real.log (p : ℝ) ≤ Real.log ((16*P : ℕ) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
        (show ((16*P : ℕ) : ℝ) ∈ Set.Ioi 0 by
          change (0 : ℝ) < ((16*P : ℕ) : ℝ)
          exact_mod_cast (show 0 < 16*P by omega))
        (by exact_mod_cast hp_le)
    exact hmono.trans (by
      simpa only [L, Nat.cast_mul, Nat.cast_ofNat] using
        (trackBEndpoint_log_bounds 16 P (16*P) hscale
          (by exact_mod_cast trackBScaleCondition_sixteen_le P hscale)
          (by omega) (by norm_num)).1)
  have hphaseLower : 1/L^2 ≤ Int.fract (t/Real.log (p : ℝ)) := by
    simpa only [L] using hpbase.2.1
  have hphaseUpper : Int.fract (t/Real.log (p : ℝ)) ≤ 2/L^2 := by
    simpa only [L] using hpbase.2.2
  have hproductLower : 1/L ≤
      Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ) := by
    calc
      1/L = (1/L^2)*L := by field_simp
      _ ≤ _ := mul_le_mul hphaseLower hloglower hL.le (Int.fract_nonneg _)
  have hproductUpper :
      Int.fract (t/Real.log (p : ℝ))*Real.log (p : ℝ) ≤ 4/L := by
    calc
      _ ≤ (2/L^2)*(2*L) := mul_le_mul hphaseUpper hlogupper hlogp.le (by positivity)
      _ = 4/L := by field_simp; norm_num
  rw [phaseExponent_power_eq_exp t hpprime.one_lt ht]
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_exp.mpr
    linarith

theorem sum_phaseExponent_power_lower {P : ℕ} {t : ℝ} (hscale : trackBScaleCondition P)
    (ht : 0 ≤ t) {S : Finset ℕ} (hS : S ⊆ logSquaredGoodPrimes P t) :
    (S.card : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) ≤
      ∑ p ∈ S, ((p : ℝ)^phaseExponent t p) := by
  calc
    _ = ∑ _p ∈ S, Real.exp (t - 4/Real.log (P : ℝ)) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      exact (goodPrime_phaseExponent_power_bounds P t hscale ht (hS hp)).1

end
end Erdos878.TrackB
