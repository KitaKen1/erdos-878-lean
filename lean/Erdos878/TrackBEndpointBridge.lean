import Erdos878.TrackBPacking

/-!
# Track B: endpoint-parameter interface

The analytic and finite packing work is combined here. The only remaining
lower-bound input is a scalar choice of `P(X)`, `t(X)`, and `N(X)` satisfying
explicit inequalities.
-/

namespace Erdos878.TrackB
open Filter Finset
noncomputable section

def endpointConditions (ε : ℝ) (X P N : ℕ) (t : ℝ) : Prop :=
  0 ≤ t ∧
  (P : ℝ)/Real.log (P : ℝ)^130 ≤ t ∧
  t ≤ (P : ℝ)/Real.log (P : ℝ)^126 ∧
  (N : ℝ) ≤ (P : ℝ)/(2*Real.log (P : ℝ)^7) ∧
  Real.exp (t - 1/Real.log (P : ℝ)) + (((16*P)^N : ℕ) : ℝ) ≤ (X : ℝ) ∧
  0 < Erdos878.maximalOrderScale X ∧
  1-ε ≤ (N : ℝ)*Real.exp (t - 4/Real.log (P : ℝ)) /
    Erdos878.maximalOrderScale X

/-- All analytic estimates and finite arithmetic are discharged: an eventual
family of scalar endpoint conditions implies the required eventual lower bound. -/
theorem eventually_maxUpTo_ratio_ge_one_sub_of_endpointConditions
    (ε : ℝ) (P N : ℕ → ℕ) (t : ℕ → ℝ)
    (hP : Tendsto P atTop atTop)
    (hcond : ∀ᶠ X : ℕ in atTop, endpointConditions ε X (P X) (N X) (t X)) :
    ∀ᶠ X : ℕ in atTop,
      1-ε ≤ (Erdos878.maxUpTo Erdos878.f X : ℝ) / Erdos878.maximalOrderScale X := by
  have hselect := hP.eventually eventually_exists_logSquaredGoodPrime_family
  have hscale := hP.eventually eventually_trackBScaleCondition
  filter_upwards [hselect, hscale, hcond] with X hselectX hscaleX hX
  rcases hX with ⟨ht0, htlo, hthi, hN, hbudget, hscalePos, hnormalized⟩
  obtain ⟨S, hsubset, hcard, _⟩ := hselectX (t X) htlo hthi (N X) hN
  have hbudgetS : Real.exp (t X - 1/Real.log (P X : ℝ)) +
      (((16*(P X))^S.card : ℕ) : ℝ) ≤ (X : ℝ) := by
    simpa only [hcard] using hbudget
  have hpacked := card_mul_exp_le_maxUpTo_f_of_goodPrime_family_of_additive_budget
    hscaleX ht0 hsubset hbudgetS
  have hpacked' : (N X : ℝ)*Real.exp (t X - 4/Real.log (P X : ℝ)) ≤
      (Erdos878.maxUpTo Erdos878.f X : ℝ) := by
    simpa only [hcard] using hpacked
  have hquot : (N X : ℝ)*Real.exp (t X - 4/Real.log (P X : ℝ)) /
      Erdos878.maximalOrderScale X ≤
      (Erdos878.maxUpTo Erdos878.f X : ℝ) / Erdos878.maximalOrderScale X :=
    div_le_div_of_nonneg_right hpacked' hscalePos.le
  exact hnormalized.trans hquot

/-- Public reduction of the ordinary maximal-order statement to scalar
endpoint parameters. No exponential-sum or prime-distribution hypothesis
remains in this interface. -/
theorem second_question_of_endpointParameters
    (hparams : ∀ ε : ℝ, 0 < ε →
      ∃ (P N : ℕ → ℕ) (t : ℕ → ℝ),
        Tendsto P atTop atTop ∧
        ∀ᶠ X : ℕ in atTop, endpointConditions ε X (P X) (N X) (t X)) :
    erdos_878.parts.ii := by
  apply Erdos878.second_question_iff.mpr
  apply Erdos878.tendsto_maximalOrder_of_eventually_one_sub_le
  intro ε hε
  obtain ⟨P, N, t, hP, hcond⟩ := hparams ε hε
  exact eventually_maxUpTo_ratio_ge_one_sub_of_endpointConditions ε P N t hP hcond

end
end Erdos878.TrackB
