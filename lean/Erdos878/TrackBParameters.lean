import Erdos878.TrackBVaughanBound

/-!
# Track B: an integer polylogarithmic Vaughan cutoff

The cutoff uses only a natural ceiling and an integer power. A deliberately
generous eventual size condition makes the later finite estimates elementary.
-/

namespace Erdos878.TrackB
open Filter
noncomputable section

def trackBCutoff (P : ℕ) : ℕ := ⌈Real.log (P : ℝ) ^ 64⌉₊

/-- A sufficient large-parameter condition, not an additional number-theoretic hypothesis. -/
def trackBScaleCondition (P : ℕ) : Prop :=
  1 ≤ Real.log (P : ℝ) ∧ 16 * Real.log (P : ℝ) ^ 400 ≤ (P : ℝ)

theorem trackBCutoff_bounds (P : ℕ) (hL : 1 ≤ Real.log (P : ℝ)) :
    Real.log (P : ℝ) ^ 64 ≤ (trackBCutoff P : ℝ) ∧
      (trackBCutoff P : ℝ) ≤ 2 * Real.log (P : ℝ) ^ 64 := by
  have hpow : (1 : ℝ) ≤ Real.log (P : ℝ) ^ 64 := one_le_pow₀ hL
  refine ⟨Nat.le_ceil _, ?_⟩
  have ht := Nat.ceil_lt_add_one (show 0 ≤ Real.log (P : ℝ)^64 by positivity)
  dsimp [trackBCutoff]
  linarith

theorem trackBCutoff_pos (P : ℕ) (hL : 1 ≤ Real.log (P : ℝ)) :
    0 < trackBCutoff P := by
  have h := (one_le_pow₀ hL (n := 64)).trans (trackBCutoff_bounds P hL).1
  have : 1 ≤ trackBCutoff P := by exact_mod_cast h
  omega

theorem trackBScaleCondition_sixteen_le (P : ℕ) (h : trackBScaleCondition P) :
    16 ≤ P := by
  have hpow : (1 : ℝ) ≤ Real.log (P : ℝ)^400 := one_le_pow₀ h.1
  have : (16 : ℝ) ≤ P := by linarith [h.2]
  exact_mod_cast this

theorem trackBCutoff_sq_sq_le (P : ℕ) (h : trackBScaleCondition P) :
    (trackBCutoff P * trackBCutoff P)^2 ≤ P := by
  have hb := (trackBCutoff_bounds P h.1).2
  have he : (trackBCutoff P : ℝ)^4 ≤ (P : ℝ) := by
    calc
      _ ≤ (2*Real.log (P : ℝ)^64)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hb 4
      _ = 16*Real.log (P : ℝ)^256 := by ring
      _ ≤ 16*Real.log (P : ℝ)^400 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h.1 (by decide)) (by norm_num)
      _ ≤ _ := h.2
  have he' : ((trackBCutoff P : ℝ)*trackBCutoff P)^2 ≤ (P : ℝ) := by
    convert he using 1; ring
  exact_mod_cast he'

theorem trackBScaleCondition_sqrt_lower (P : ℕ) (h : trackBScaleCondition P) :
    4 * Real.log (P : ℝ)^200 ≤ Real.sqrt (P : ℝ) := by
  apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg P)).2
  convert h.2 using 1; ring

/-- The size condition holds for all sufficiently large natural numbers. -/
theorem eventually_trackBScaleCondition : ∀ᶠ P : ℕ in atTop, trackBScaleCondition P := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 400)).bound
    (show (0 : ℝ) < 1/16 by norm_num)
  have hn : Tendsto (fun P : ℕ => (P : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp hn).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hn.eventually hsmall, hlog] with P hp hL
  change 1 ≤ Real.log (P : ℝ) at hL
  refine ⟨hL, ?_⟩
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hL0 : 0 ≤ Real.log (P : ℝ) := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL0 _),
    id_eq, abs_of_nonneg hP0] at hp
  linarith

/-- The actual cutoff discharges all short-support conditions in Vaughan's estimate. -/
theorem norm_weightedArithmeticSum_vonMangoldt_le_polylogCutoff
    (a C : ℝ) (P Y X : ℕ) (hscale : trackBScaleCondition P)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C)
    (hCP : C ≤ (P : ℝ)) (hX : (X : ℝ) ≤ C * P) (hYX : Y ≤ X) :
    ‖weightedArithmeticSum (Finset.Ioc P Y) (reciprocalLogWeight a)
      ArithmeticFunction.vonMangoldt‖ ≤
      vaughanReciprocalLogBound a C (trackBCutoff P) (trackBCutoff P) P X := by
  exact norm_weightedArithmeticSum_vonMangoldt_le_uniform_endpoint a C
    (trackBCutoff P) (trackBCutoff P) P Y X ha haP hC
    (by have := trackBScaleCondition_sixteen_le P hscale; omega) hscale.1 hCP hX hYX
    (trackBCutoff_pos P hscale.1) (trackBCutoff_pos P hscale.1)
    (trackBCutoff_sq_sq_le P hscale)

end
end Erdos878.TrackB
