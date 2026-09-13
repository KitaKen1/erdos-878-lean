import Erdos878.MultiWindowLower

/-!
# Letting the finite multi-window coefficient approach one half

Use the single sequence

`k` window pairs and `rho = epsilon = eta = 1 / (k + 1)`.

Its fixed-parameter lower coefficient tends to `1/2`.  Therefore every constant strictly below
`1/2` is an eventual lower bound on some density-one set.  The parameters remain fixed before
the integer variable tends to infinity.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

def sharpFirstLoss (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

def sharpFirstLowerCoefficient (k : ℕ) : ℝ :=
  (1 - sharpFirstLoss k) * (1 - sharpFirstLoss k) * (k : ℝ) *
    multiWindowWidth k / Real.exp (sharpFirstLoss k)

theorem tendsto_sharpFirstLoss_zero :
    Tendsto sharpFirstLoss atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_nat_mul_multiWindowWidth_half :
    Tendsto (fun k : ℕ ↦ (k : ℝ) * multiWindowWidth k) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds
    (0 : ℝ) 5 1 (by norm_num : (2 : ℝ) ≠ 0)
  convert h using 1
  · funext k
    unfold multiWindowWidth multiWindowDenominator
    ring

theorem tendsto_sharpFirstLowerCoefficient_half :
    Tendsto sharpFirstLowerCoefficient atTop (𝓝 (1 / 2 : ℝ)) := by
  have hloss := tendsto_sharpFirstLoss_zero
  have hone : Tendsto (fun k : ℕ ↦ 1 - sharpFirstLoss k) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hloss
  have hratio := tendsto_nat_mul_multiWindowWidth_half
  have hexp : Tendsto (fun k : ℕ ↦ Real.exp (sharpFirstLoss k)) atTop (𝓝 1) := by
    change Tendsto (Real.exp ∘ sharpFirstLoss) atTop (𝓝 1)
    simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hloss
  have h := ((hone.mul hone).mul hratio).div hexp (by norm_num : (1 : ℝ) ≠ 0)
  have h' : Tendsto sharpFirstLowerCoefficient atTop
      (𝓝 (1 * 1 * (1 / 2 : ℝ) / 1)) := by
    apply h.congr'
    exact Filter.Eventually.of_forall (fun k ↦ by
      unfold sharpFirstLowerCoefficient
      change
        (1 - sharpFirstLoss k) * (1 - sharpFirstLoss k) *
            ((k : ℝ) * multiWindowWidth k) / Real.exp (sharpFirstLoss k) =
          (1 - sharpFirstLoss k) * (1 - sharpFirstLoss k) * (k : ℝ) *
            multiWindowWidth k / Real.exp (sharpFirstLoss k)
      ring)
  simpa using h'

/-- Every coefficient below `1/2` is attained as a density-one eventual lower bound. -/
theorem exists_density_one_F_div_scale_ge_of_lt_half
    {c : ℝ} (hc : c < 1 / 2) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop, c ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
  have hcoeff : ∀ᶠ k : ℕ in atTop, c < sharpFirstLowerCoefficient k :=
    ((tendsto_order.1 tendsto_sharpFirstLowerCoefficient_half).1 c hc)
  have hlate : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
  obtain ⟨k, hck, hk⟩ := (hcoeff.and hlate).exists
  have hloss0 : 0 < sharpFirstLoss k := by
    unfold sharpFirstLoss
    positivity
  have hloss1 : sharpFirstLoss k < 1 := by
    unfold sharpFirstLoss
    rw [div_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rcases exists_density_one_F_div_scale_ge_multiWindow k
      hloss0 hloss0 hloss1 hloss0 hloss1 with ⟨A, hA, hAcoeff⟩
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAcoeff] with n hn
  exact hck.le.trans (by simpa [sharpFirstLowerCoefficient] using hn)

end

end Erdos878

#print axioms Erdos878.tendsto_sharpFirstLowerCoefficient_half
#print axioms Erdos878.exists_density_one_F_div_scale_ge_of_lt_half
