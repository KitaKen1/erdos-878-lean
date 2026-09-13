import Erdos878.PrimeReciprocalAbel
import Erdos878.GeometricBlockDensity
import Erdos878.DensityDiagonal

/-!
# Density-one normal order of the number of distinct prime factors

This file derives the Hardy--Ramanujan normal-order input needed by the sharp first-question
variant from two ingredients already proved in this project: Mertens' bounded-error theorem for
the reciprocal-prime prefix and the finite centered second-moment estimate for `divisorCount`.
-/

open Classical Filter Finset Topology
open scoped Real

namespace Erdos878

noncomputable section

def primePrefixMass (X : ℕ) : ℝ :=
  ∑ p ∈ X.primesLE, ((p : ℝ)⁻¹)

theorem primePrefixMass_eq_partialSum (X : ℕ) :
    primePrefixMass X = primeReciprocalPartialSum (X : ℝ) := by
  simpa [primePrefixMass] using (primeReciprocalPartialSum_nat X).symm

theorem tendsto_primePrefixMass_atTop :
    Tendsto primePrefixMass atTop atTop := by
  obtain ⟨B, _hBpos, hB⟩ := reciprocal_prime_mertens_bounded_error
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro C
  filter_upwards [hll.eventually (eventually_ge_atTop (C + B)),
    eventually_ge_atTop (2 : ℕ)] with X hlarge hX
  have herr := hB (show (2 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX)
  rw [← primePrefixMass_eq_partialSum] at herr
  have hlower := neg_le_of_abs_le herr
  linarith

theorem tendsto_primePrefixMass_div_loglog_one :
    Tendsto (fun X : ℕ ↦ primePrefixMass X /
      Real.log (Real.log (X : ℝ))) atTop (𝓝 1) := by
  obtain ⟨B, _hBpos, hB⟩ := reciprocal_prime_mertens_bounded_error
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have habs : Tendsto (fun X : ℕ ↦ |(primePrefixMass X -
      Real.log (Real.log (X : ℝ))) / Real.log (Real.log (X : ℝ))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun X : ℕ ↦ B / Real.log (Real.log (X : ℝ)))
    · exact Filter.Eventually.of_forall (fun X ↦ abs_nonneg _)
    · filter_upwards [eventually_ge_atTop (2 : ℕ),
        hll.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hpos
      have herr := hB (show (2 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX)
      rw [← primePrefixMass_eq_partialSum] at herr
      rw [abs_div, abs_of_pos hpos]
      exact div_le_div_of_nonneg_right herr hpos.le
    · exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ B) atTop (𝓝 B)).div_atTop hll
  have hdiff : Tendsto (fun X : ℕ ↦
      (primePrefixMass X - Real.log (Real.log (X : ℝ))) /
        Real.log (Real.log (X : ℝ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hadd := hdiff.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  have heq : (fun X : ℕ ↦
      (primePrefixMass X - Real.log (Real.log (X : ℝ))) /
          Real.log (Real.log (X : ℝ)) + 1) =ᶠ[atTop]
      (fun X : ℕ ↦ primePrefixMass X / Real.log (Real.log (X : ℝ))) := by
    filter_upwards [hll.eventually (eventually_ne_atTop (0 : ℝ))] with X hne
    field_simp
    ring
  convert hadd.congr' heq using 1
  all_goals norm_num

/-- For `1 ≤ n ≤ X`, the primes up to `X` detect every distinct prime divisor of `n`. -/
theorem divisorCount_primesLE_eq_omega {X n : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    divisorCount X.primesLE n = omega n := by
  unfold divisorCount omega
  have hfin : X.primesLE.filter (fun p ↦ p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpX, hpprime⟩, hpdvd⟩
      exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvd, by omega⟩
    · intro hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hpdvd := Nat.dvd_of_mem_primeFactors hp
      have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
      exact ⟨⟨hpn.trans hnX, hpprime⟩, hpdvd⟩
  rw [hfin]

/-- Symmetric finite Chebyshev counting, stated in the form used for `omega`. -/
theorem card_filter_abs_sub_ge_mul_sq_le
    {α : Type*} [DecidableEq α] (U : Finset α) (Z : α → ℝ)
    {μ t V : ℝ} (ht : 0 < t)
    (hvar : ∑ x ∈ U, (Z x - μ) ^ 2 ≤ V) :
    (((U.filter (fun x ↦ t ≤ |Z x - μ|)).card : ℕ) : ℝ) * t ^ 2 ≤ V := by
  let E : Finset α := U.filter (fun x ↦ t ≤ |Z x - μ|)
  have hpoint : ∀ x ∈ E, t ^ 2 ≤ (Z x - μ) ^ 2 := by
    intro x hx
    have hx' : t ≤ |Z x - μ| := (Finset.mem_filter.mp hx).2
    nlinarith [sq_abs (Z x - μ)]
  calc
    (((E.card : ℕ) : ℝ) * t ^ 2) = ∑ x ∈ E, t ^ 2 := by simp
    _ ≤ ∑ x ∈ E, (Z x - μ) ^ 2 :=
      Finset.sum_le_sum (fun x hx ↦ hpoint x hx)
    _ ≤ ∑ x ∈ U, (Z x - μ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro x hxU hxE; positivity)
    _ ≤ V := hvar

def omegaPrefixDeviationUpTo (X : ℕ) (epsilon : ℝ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n ↦
    epsilon * primePrefixMass X ≤ |(omega n : ℝ) - primePrefixMass X|)

theorem omegaPrefixDeviation_ratio_le
    {X : ℕ} (hX : 0 < X) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hmu : 0 < primePrefixMass X) :
    ((omegaPrefixDeviationUpTo X epsilon).card : ℝ) / (X : ℝ) ≤
      3 / (epsilon ^ 2 * primePrefixMass X) := by
  let mu := primePrefixMass X
  have hprime : ∀ p ∈ X.primesLE, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2
  have hvar0 := sum_divisorCount_centered_sq_Icc_le_primeReciprocal_sharp
    X.primesLE X hprime hX
  have hvar :
      ∑ n ∈ Finset.Icc 1 X, ((omega n : ℝ) - mu) ^ 2 ≤
        (X : ℝ) * mu + 2 * mu * (X.primesLE.card : ℝ) := by
    calc
      ∑ n ∈ Finset.Icc 1 X, ((omega n : ℝ) - mu) ^ 2 =
          ∑ n ∈ Finset.Icc 1 X, (divisorCount X.primesLE n - mu) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [divisorCount_primesLE_eq_omega (Finset.mem_Icc.mp hn).1
          (Finset.mem_Icc.mp hn).2]
      _ ≤ (X : ℝ) * mu + 2 * mu * (X.primesLE.card : ℝ) := by
        simpa [mu, primePrefixMass] using hvar0
  have hcardPrime : X.primesLE.card ≤ X := by
    have hsub : X.primesLE ⊆ Finset.Icc 1 X := by
      intro p hp
      have hdata := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr ⟨hdata.2.one_le, hdata.1⟩
    have hc := Finset.card_le_card hsub
    simpa using hc
  have hV :
      (X : ℝ) * mu + 2 * mu * (X.primesLE.card : ℝ) ≤ 3 * (X : ℝ) * mu := by
    have hcR : (X.primesLE.card : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcardPrime
    nlinarith [show 0 ≤ mu from hmu.le]
  have ht : 0 < epsilon * mu := mul_pos hepsilon hmu
  have hcheb :
      ((omegaPrefixDeviationUpTo X epsilon).card : ℝ) * (epsilon * mu) ^ 2 ≤
        (X : ℝ) * mu + 2 * mu * (X.primesLE.card : ℝ) := by
    unfold omegaPrefixDeviationUpTo
    exact card_filter_abs_sub_ge_mul_sq_le (Finset.Icc 1 X)
      (fun n ↦ (omega n : ℝ)) ht hvar
  have hmain :
      ((omegaPrefixDeviationUpTo X epsilon).card : ℝ) * (epsilon * mu) ^ 2 ≤
        3 * (X : ℝ) * mu := hcheb.trans hV
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  apply (div_le_iff₀ hXR).2
  have ht2 : 0 < (epsilon * mu) ^ 2 := sq_pos_of_pos ht
  have hcard : ((omegaPrefixDeviationUpTo X epsilon).card : ℝ) ≤
      (3 * (X : ℝ) * mu) / (epsilon * mu) ^ 2 :=
    (le_div_iff₀ ht2).2 hmain
  have hmu0 : mu ≠ 0 := hmu.ne'
  have heps0 : epsilon ≠ 0 := hepsilon.ne'
  calc
    ((omegaPrefixDeviationUpTo X epsilon).card : ℝ) ≤
        (3 * (X : ℝ) * mu) / (epsilon * mu) ^ 2 := hcard
    _ = 3 / (epsilon ^ 2 * primePrefixMass X) * (X : ℝ) := by
      dsimp [mu]
      field_simp [heps0, hmu0]

theorem tendsto_omegaPrefixDeviation_ratio_zero
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fun X : ℕ ↦ ((omegaPrefixDeviationUpTo X epsilon).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  have hmuPos : ∀ᶠ X : ℕ in atTop, 0 < primePrefixMass X :=
    tendsto_primePrefixMass_atTop.eventually (eventually_gt_atTop (0 : ℝ))
  have hden : Tendsto (fun X : ℕ ↦ epsilon ^ 2 * primePrefixMass X) atTop atTop :=
    tendsto_primePrefixMass_atTop.const_mul_atTop (sq_pos_of_pos hepsilon)
  have hupper : Tendsto (fun X : ℕ ↦ 3 / (epsilon ^ 2 * primePrefixMass X))
      atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (𝓝 3)).div_atTop hden
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun X ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hmuPos] with X hX hmu
    exact omegaPrefixDeviation_ratio_le hX hepsilon hmu
  · exact hupper

def dyadicOmegaDeviationSet (epsilon : ℝ) : Set ℕ :=
  dyadicBlockExceptionalSet (fun k ↦
    omegaPrefixDeviationUpTo (dyadicReportEndpoint k) epsilon)

theorem dyadicOmegaDeviationSet_hasDensity_zero
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (dyadicOmegaDeviationSet epsilon).HasDensity 0 := by
  have hendpoint : Tendsto dyadicReportEndpoint atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  have hratio := (tendsto_omegaPrefixDeviation_ratio_zero hepsilon).comp hendpoint
  simpa [dyadicOmegaDeviationSet, Function.comp_def] using
    dyadicBlockExceptionalSet_hasDensity_zero_of_endpoint_ratio
      (fun k ↦ omegaPrefixDeviationUpTo (dyadicReportEndpoint k) epsilon) hratio

theorem omega_close_to_dyadic_endpoint_mass_off_deviation
    {epsilon : ℝ} (_hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, n ∉ dyadicOmegaDeviationSet epsilon →
      |(omega n : ℝ) - primePrefixMass
          (dyadicReportEndpoint (Nat.log 2 n))| <
        epsilon * primePrefixMass (dyadicReportEndpoint (Nat.log 2 n)) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn hnot
  let k := Nat.log 2 n
  let X := dyadicReportEndpoint k
  have hn0 : n ≠ 0 := by omega
  have hnX : n ≤ X := by
    exact (Nat.lt_pow_succ_log_self (by norm_num) n).le
  have hnIcc : n ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨hn, hnX⟩
  have hnotE : n ∉ omegaPrefixDeviationUpTo X epsilon := by
    intro hmem
    apply hnot
    exact ⟨hn0, by simpa [k, X, dyadicOmegaDeviationSet] using hmem⟩
  have hnotThreshold : ¬ epsilon * primePrefixMass X ≤
      |(omega n : ℝ) - primePrefixMass X| := by
    intro hle
    apply hnotE
    exact Finset.mem_filter.mpr ⟨hnIcc, hle⟩
  simpa [k, X] using lt_of_not_ge hnotThreshold

theorem tendsto_loglog_two_mul_div_loglog_one :
    Tendsto (fun n : ℕ ↦
      Real.log (Real.log ((2 * n : ℕ) : ℝ)) /
        Real.log (Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hdiff0 : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (n : ℝ) + Real.log 2) -
        Real.log (Real.log (n : ℝ))) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log (Real.log 2)).comp hlog
  have hdiff : Tendsto (fun n : ℕ ↦
      Real.log (Real.log ((2 * n : ℕ) : ℝ)) -
        Real.log (Real.log (n : ℝ))) atTop (𝓝 0) := by
    apply hdiff0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hinner : Real.log ((2 * n : ℕ) : ℝ) =
        Real.log (n : ℝ) + Real.log 2 := by
      rw [Nat.cast_mul]
      change Real.log ((2 : ℝ) * (n : ℝ)) =
        Real.log (n : ℝ) + Real.log 2
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
      ring
    rw [hinner]
  have hquot := hdiff.div_atTop hll
  have hadd := hquot.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  have heq : (fun n : ℕ ↦
      (Real.log (Real.log ((2 * n : ℕ) : ℝ)) -
          Real.log (Real.log (n : ℝ))) /
          Real.log (Real.log (n : ℝ)) + 1) =ᶠ[atTop]
      (fun n : ℕ ↦ Real.log (Real.log ((2 * n : ℕ) : ℝ)) /
        Real.log (Real.log (n : ℝ))) := by
    filter_upwards [hll.eventually (eventually_ne_atTop (0 : ℝ))] with n hn
    field_simp
    ring
  convert hadd.congr' heq using 1
  all_goals norm_num

/-- Replacing `n` by the right endpoint of its dyadic block does not change `log log n`
asymptotically. -/
theorem tendsto_loglog_dyadicReportEndpoint_div_loglog_one :
    Tendsto (fun n : ℕ ↦
      Real.log (Real.log (dyadicReportEndpoint (Nat.log 2 n) : ℝ)) /
        Real.log (Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hll : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
    tendsto_loglog_two_mul_div_loglog_one
  · filter_upwards [eventually_gt_atTop (1 : ℕ),
      hll.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hllpos
    let X := dyadicReportEndpoint (Nat.log 2 n)
    have hn0 : n ≠ 0 := by omega
    have hnX : n ≤ X := (Nat.lt_pow_succ_log_self (by norm_num) n).le
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hlogle : Real.log (n : ℝ) ≤ Real.log (X : ℝ) := by
      apply Real.log_le_log hnR
      exact_mod_cast hnX
    have hllle : Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (X : ℝ)) :=
      Real.log_le_log hlogn hlogle
    calc
      (1 : ℝ) = Real.log (Real.log (n : ℝ)) /
          Real.log (Real.log (n : ℝ)) :=
        (div_self hllpos.ne').symm
      _ ≤ Real.log (Real.log (X : ℝ)) /
          Real.log (Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_right hllle hllpos.le
      _ = _ := by rfl
  · filter_upwards [eventually_gt_atTop (1 : ℕ),
      hll.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hllpos
    let k := Nat.log 2 n
    let X := dyadicReportEndpoint k
    have hn0 : n ≠ 0 := by omega
    have hpow : 2 ^ k ≤ n := by
      simpa [k] using Nat.pow_log_le_self 2 hn0
    have hXle : X ≤ 2 * n := by
      dsimp [X, dyadicReportEndpoint]
      rw [pow_succ]
      omega
    have hXNat : 0 < X := by
      dsimp [X, dyadicReportEndpoint]
      positivity
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXNat
    have hlogX : 0 < Real.log (X : ℝ) := by
      apply Real.log_pos
      have : 1 < X := by
        dsimp [X, dyadicReportEndpoint]
        exact one_lt_pow₀ (by norm_num) (by omega)
      exact_mod_cast this
    have hlogle : Real.log (X : ℝ) ≤ Real.log ((2 * n : ℕ) : ℝ) := by
      apply Real.log_le_log hXR
      exact_mod_cast hXle
    have hllle : Real.log (Real.log (X : ℝ)) ≤
        Real.log (Real.log ((2 * n : ℕ) : ℝ)) :=
      Real.log_le_log hlogX hlogle
    exact (div_le_div_of_nonneg_right hllle hllpos.le)

theorem tendsto_dyadicPrimePrefixMass_div_loglog_one :
    Tendsto (fun n : ℕ ↦
      primePrefixMass (dyadicReportEndpoint (Nat.log 2 n)) /
        Real.log (Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hindex : Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop :=
    tendsto_nat_log_base_atTop (by norm_num)
  have hendpoint : Tendsto (fun n : ℕ ↦
      dyadicReportEndpoint (Nat.log 2 n)) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)).comp hindex
  have hmass := tendsto_primePrefixMass_div_loglog_one.comp hendpoint
  have hblock := tendsto_loglog_dyadicReportEndpoint_div_loglog_one
  have hprod := hmass.mul hblock
  have heq : (fun n : ℕ ↦
      ((fun X : ℕ ↦ primePrefixMass X / Real.log (Real.log (X : ℝ))) ∘
          (fun n : ℕ ↦ dyadicReportEndpoint (Nat.log 2 n))) n *
        (Real.log (Real.log (dyadicReportEndpoint (Nat.log 2 n) : ℝ)) /
          Real.log (Real.log (n : ℝ)))) =ᶠ[atTop]
      (fun n : ℕ ↦ primePrefixMass (dyadicReportEndpoint (Nat.log 2 n)) /
        Real.log (Real.log (n : ℝ))) := by
    filter_upwards [
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      (tendsto_natCast_atTop_atTop.comp hendpoint)).eventually
        (eventually_ne_atTop (0 : ℝ))] with n hllX
    have hllX' : Real.log (Real.log
        (dyadicReportEndpoint (Nat.log 2 n) : ℝ)) ≠ 0 := by
      simpa only [Function.comp_apply] using hllX
    dsimp only [Function.comp_apply]
    field_simp [hllX']
  convert hprod.congr' heq using 1
  all_goals norm_num

def omegaNormalOrderBadSet (delta : ℝ) : Set ℕ :=
  dyadicOmegaDeviationSet (delta / 4)

theorem omegaNormalOrderBadSet_hasDensity_zero
    {delta : ℝ} (hdelta : 0 < delta) :
    (omegaNormalOrderBadSet delta).HasDensity 0 := by
  exact dyadicOmegaDeviationSet_hasDensity_zero (by
    simpa [omegaNormalOrderBadSet] using div_pos hdelta (by norm_num : (0 : ℝ) < 4))

/-- Outside a density-zero set depending on `delta`, the normal-order ratio is eventually within
`delta` of one. -/
theorem eventually_omega_normal_order_off_badSet
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, n ∉ omegaNormalOrderBadSet delta →
      |(omega n : ℝ) / Real.log (Real.log (n : ℝ)) - 1| < delta := by
  have hmuLL := tendsto_dyadicPrimePrefixMass_div_loglog_one
  have hll : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hindex : Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop :=
    tendsto_nat_log_base_atTop (by norm_num)
  have hendpoint : Tendsto (fun n : ℕ ↦
      dyadicReportEndpoint (Nat.log 2 n)) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)).comp hindex
  have hmu := tendsto_primePrefixMass_atTop.comp hendpoint
  have hclose := omega_close_to_dyadic_endpoint_mass_off_deviation
    (show 0 < delta / 4 by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hmuLL) (delta / 2) (by positivity)
  have hratioClose : ∀ᶠ n : ℕ in atTop,
      |primePrefixMass (dyadicReportEndpoint (Nat.log 2 n)) /
          Real.log (Real.log (n : ℝ)) - 1| < delta / 2 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa [Real.dist_eq] using hN n hn
  filter_upwards [hclose, hratioClose,
      (tendsto_order.1 hmuLL).2 2 (by norm_num),
      hll.eventually (eventually_gt_atTop (0 : ℝ)),
      hmu.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hcloseN hratio hratioTwo hllpos hmupos hnot
  have hraw := hcloseN (show n ∉ dyadicOmegaDeviationSet (delta / 4) by
    simpa [omegaNormalOrderBadSet] using hnot)
  let mu := primePrefixMass (dyadicReportEndpoint (Nat.log 2 n))
  let L := Real.log (Real.log (n : ℝ))
  have hterm : |(omega n : ℝ) / L - mu / L| < delta / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hllpos]
    have hdiv := div_lt_div_of_pos_right hraw hllpos
    have hratioPos : 0 < mu / L := div_pos hmupos hllpos
    calc
      |(omega n : ℝ) - mu| / L < (delta / 4 * mu) / L := hdiv
      _ = delta / 4 * (mu / L) := by ring
      _ < delta / 4 * 2 := by
        exact mul_lt_mul_of_pos_left hratioTwo (by positivity)
      _ = delta / 2 := by ring
  have htriangle := abs_add_le ((omega n : ℝ) / L - mu / L) (mu / L - 1)
  have hid : (omega n : ℝ) / L - 1 =
      ((omega n : ℝ) / L - mu / L) + (mu / L - 1) := by ring
  rw [hid]
  exact lt_of_le_of_lt htriangle (by linarith)

/-- Hardy--Ramanujan normal order in the exact density-one subtype form consumed by the final
Problem 878 squeeze. -/
theorem exists_density_one_omega_normal_order :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦ (omega (n : ℕ) : ℝ) /
        Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 1) := by
  let delta : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ) + 1)
  let B : ℕ → Set ℕ := fun i ↦ omegaNormalOrderBadSet (delta i)
  have hdelta : ∀ i, 0 < delta i := by
    intro i
    dsimp [delta]
    positivity
  have hB : ∀ i, (B i).HasDensity 0 := by
    intro i
    dsimp [B]
    exact omegaNormalOrderBadSet_hasDensity_zero (hdelta i)
  rcases exists_density_one_eventually_avoids B hB with ⟨A, hA, havoid⟩
  have hAinf : A.Infinite := Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hAinf b
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : A)] with n hn
    exact hba.le.trans hn
  refine ⟨A, hA, ?_⟩
  obtain ⟨a, ha⟩ := hAinf.nonempty
  let _ : Nonempty A := ⟨⟨a, ha⟩⟩
  apply Metric.tendsto_atTop.2
  intro epsilon hepsilon
  have hdelta0 : Tendsto delta atTop (𝓝 0) := by
    change Tendsto (fun i : ℕ ↦ 1 / ((i : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ i : ℕ in atTop, delta i < epsilon :=
    (tendsto_order.1 hdelta0).2 epsilon hepsilon
  obtain ⟨i, hi⟩ := hevent.exists
  have hoff := eventually_omega_normal_order_off_badSet (hdelta i)
  apply eventually_atTop.1
  filter_upwards [havoid i, hcoe.eventually hoff] with n hnAvoid hnOff
  have hn : |(omega (n : ℕ) : ℝ) /
      Real.log (Real.log ((n : ℕ) : ℝ)) - 1| < delta i := by
    apply hnOff
    simpa [B] using hnAvoid
  simpa [Real.dist_eq] using hn.trans hi

end

end Erdos878

#print axioms Erdos878.tendsto_primePrefixMass_div_loglog_one
#print axioms Erdos878.divisorCount_primesLE_eq_omega
#print axioms Erdos878.card_filter_abs_sub_ge_mul_sq_le
#print axioms Erdos878.tendsto_omegaPrefixDeviation_ratio_zero
#print axioms Erdos878.dyadicOmegaDeviationSet_hasDensity_zero
#print axioms Erdos878.omega_close_to_dyadic_endpoint_mass_off_deviation
#print axioms Erdos878.tendsto_loglog_dyadicReportEndpoint_div_loglog_one
#print axioms Erdos878.tendsto_dyadicPrimePrefixMass_div_loglog_one
#print axioms Erdos878.omegaNormalOrderBadSet_hasDensity_zero
#print axioms Erdos878.eventually_omega_normal_order_off_badSet
#print axioms Erdos878.exists_density_one_omega_normal_order
