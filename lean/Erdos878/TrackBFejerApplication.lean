import Erdos878.TrackBFejerMean

/-!
# Track B: apply the proved exponential-sum estimate to a concrete phase window

This gives a lower bound for von Mangoldt mass in the window. A lower bound
for the total mass and removal of higher prime powers are subsequent tasks.
-/

namespace Erdos878.TrackB
open Filter Finset
noncomputable section

theorem weightedPhaseSum_reciprocalLog (I : Finset ℕ) (A : ArithmeticFunction ℝ) (t : ℝ) (k : ℤ) :
    weightedPhaseSum I A (fun r => t/Real.log (r : ℝ)) k =
      weightedArithmeticSum I (reciprocalLogWeight ((k : ℝ)*t)) A := by
  simp only [weightedPhaseSum, weightedArithmeticSum, reciprocalLogWeight, mul_div_assoc]

/-- A uniform lower bound for the mass in any sufficiently wide circular phase window. -/
theorem eventually_vonMangoldt_phaseWindow_mass_lower (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t → t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      ∀ K : ℕ, 0 < K → (K : ℝ) ≤ Real.log (P : ℝ)^6 →
      ∀ c b : ℝ, 0 < b → 1 ≤ 2*(K : ℝ)*b^2 →
      (∑ r ∈ Ioc P Y, ArithmeticFunction.vonMangoldt r)/(2*(K : ℝ)) -
          1000000*C^2*P/Real.log (P : ℝ)^25 ≤
        ∑ r ∈ (Ioc P Y).filter (fun r : ℕ => inPhaseWindow c b (t/Real.log (r : ℝ))),
          ArithmeticFunction.vonMangoldt r := by
  filter_upwards [eventually_vonMangoldt_harmonics_logSaving C hC] with P hp
  intro t htlo hthi Y X hPX hX hYX K hK hKL c b hb hwidth
  have hlog := Real.log_natCast_nonneg P
  apply weighted_phaseWindow_mass_lower_half (Ioc P Y) ArithmeticFunction.vonMangoldt
    (fun r => t/Real.log (r : ℝ)) K c b _ hK hb hwidth (by positivity)
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  intro k hk hkK
  rw [weightedPhaseSum_reciprocalLog]
  exact hp t htlo hthi k hk (hkK.le.trans hKL) Y X hPX hX hYX

/-- Fourier order, separate from the Vaughan cutoff of exponent 64. -/
def trackBFejerOrder (P : ℕ) : ℕ := ⌊Real.log (P : ℝ)^6⌋₊

theorem trackBFejerOrder_bounds (P : ℕ) (hL : 2 ≤ Real.log (P : ℝ)) :
    0 < trackBFejerOrder P ∧ (trackBFejerOrder P : ℝ) ≤ Real.log (P : ℝ)^6 ∧
      Real.log (P : ℝ)^6/2 ≤ (trackBFejerOrder P : ℝ) := by
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 6
  norm_num at hpow
  have hfloor := Nat.lt_floor_add_one (Real.log (P : ℝ)^6)
  have hlo : Real.log (P : ℝ)^6/2 ≤ (trackBFejerOrder P : ℝ) := by
    dsimp [trackBFejerOrder]
    linarith
  refine ⟨?_, Nat.floor_le (by positivity), hlo⟩
  have hK : (0 : ℝ) < trackBFejerOrder P := by linarith
  exact_mod_cast hK

theorem trackBFejerOrder_width (P : ℕ) (hL : 2 ≤ Real.log (P : ℝ)) :
    1 ≤ 2*(trackBFejerOrder P : ℝ)*(1/(2*Real.log (P : ℝ)^2))^2 := by
  have hLp : 0 < Real.log (P : ℝ) := by linarith
  have hK := (trackBFejerOrder_bounds P hL).2.2
  calc
    1 ≤ Real.log (P : ℝ)^2/4 := by apply (le_div_iff₀ (by norm_num)).2; nlinarith
    _ = 2*(Real.log (P : ℝ)^6/2)*(1/(2*Real.log (P : ℝ)^2))^2 := by field_simp; ring
    _ ≤ _ := by gcongr

/-- The ordinary fractional-part window `[1/L²,2/L²]` needs no wrap-around convention. -/
theorem inPhaseWindow_log_squared_iff (P : ℕ) (u : ℝ) (hL : 2 ≤ Real.log (P : ℝ)) :
    inPhaseWindow (3/(2*Real.log (P : ℝ)^2)) (1/(2*Real.log (P : ℝ)^2)) u ↔
      1/Real.log (P : ℝ)^2 ≤ Int.fract u ∧ Int.fract u ≤ 2/Real.log (P : ℝ)^2 := by
  have hLp : 0 < Real.log (P : ℝ) := by linarith
  have helo : 3/(2*Real.log (P : ℝ)^2)-1/(2*Real.log (P : ℝ)^2) = 1/Real.log (P : ℝ)^2 := by ring
  have hehi : 3/(2*Real.log (P : ℝ)^2)+1/(2*Real.log (P : ℝ)^2) = 2/Real.log (P : ℝ)^2 := by ring
  have hlo : 0 < 3/(2*Real.log (P : ℝ)^2)-1/(2*Real.log (P : ℝ)^2) := by rw [helo]; positivity
  have hhi : 3/(2*Real.log (P : ℝ)^2)+1/(2*Real.log (P : ℝ)^2) < 1 := by
    rw [hehi]
    apply (div_lt_one (by positivity)).2
    nlinarith
  simpa only [helo, hehi] using inPhaseWindow_iff_fract_mem _ _ u (by positivity) hlo hhi

/-- Concrete window mass bound with the Fejér order and half-width fully substituted.
The remaining main term is the actual total von Mangoldt mass, not a prime-distribution assumption. -/
theorem eventually_vonMangoldt_logSquaredWindow_mass_lower (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ P : ℕ in atTop, ∀ t : ℝ,
      (P : ℝ)/Real.log (P : ℝ)^130 ≤ t → t ≤ (P : ℝ)/Real.log (P : ℝ)^126 →
      ∀ Y X : ℕ, P ≤ X → (X : ℝ) ≤ C*P → Y ≤ X →
      (∑ r ∈ Ioc P Y, ArithmeticFunction.vonMangoldt r)/(2*Real.log (P : ℝ)^6) -
          1000000*C^2*P/Real.log (P : ℝ)^25 ≤
        ∑ r ∈ (Ioc P Y).filter (fun r : ℕ =>
          1/Real.log (P : ℝ)^2 ≤ Int.fract (t/Real.log (r : ℝ)) ∧
          Int.fract (t/Real.log (r : ℝ)) ≤ 2/Real.log (P : ℝ)^2),
            ArithmeticFunction.vonMangoldt r := by
  have hlog : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log (P : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_vonMangoldt_phaseWindow_mass_lower C hC, hlog] with P hp hL
  intro t htlo hthi Y X hPX hX hYX
  obtain ⟨hK, hKhi, _⟩ := trackBFejerOrder_bounds P hL
  have hb : 0 < 1/(2*Real.log (P : ℝ)^2) := by positivity
  have ht := hp t htlo hthi Y X hPX hX hYX (trackBFejerOrder P) hK hKhi
    (3/(2*Real.log (P : ℝ)^2)) (1/(2*Real.log (P : ℝ)^2)) hb (trackBFejerOrder_width P hL)
  simp_rw [inPhaseWindow_log_squared_iff P _ hL] at ht
  refine le_trans ?_ ht
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_left (sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    (by positivity) (by gcongr)

end
end Erdos878.TrackB
