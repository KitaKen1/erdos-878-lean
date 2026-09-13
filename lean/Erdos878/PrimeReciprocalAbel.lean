import Erdos878.ReportWindowMass

/-!
# Abel summation for reciprocal primes

This module isolates the exact analytic identity needed to upgrade the coarse report-window mass
bound to its sharp main term.  The weighted prefix is `A(x) = sum_{p<=x} log p / p`; Abel
summation expresses the reciprocal-prime prefix in terms of `A` and one elementary integral.
-/

open Classical Filter Finset Topology MeasureTheory
open scoped Real

namespace Erdos878

noncomputable section

def primeLogDivPartialSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
    if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0

def primeReciprocalPartialSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
    if n.Prime then ((n : ℝ)⁻¹) else 0

theorem primeLogDivPartialSum_nat (N : ℕ) :
    primeLogDivPartialSum (N : ℝ) =
      ∑ p ∈ N.primesLE, Real.log (p : ℝ) / (p : ℝ) := by
  rw [primeLogDivPartialSum, Nat.floor_natCast, Nat.primesLE_eq_filter_Icc_zero,
    Finset.sum_filter]

theorem primeReciprocalPartialSum_nat (N : ℕ) :
    primeReciprocalPartialSum (N : ℝ) =
      ∑ p ∈ N.primesLE, ((p : ℝ)⁻¹) := by
  rw [primeReciprocalPartialSum, Nat.floor_natCast, Nat.primesLE_eq_filter_Icc_zero,
    Finset.sum_filter]

/- A report-style prime window is exactly the difference of two reciprocal-prime prefixes. -/
theorem primeWindow_reciprocal_mass_eq_partialSum_sub
    {T a b : ℝ} (hab : Real.rpow T a ≤ Real.rpow T b) :
    (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) =
      primeReciprocalPartialSum (Real.exp (Real.rpow T b)) -
        primeReciprocalPartialSum (Real.exp (Real.rpow T a)) := by
  let u : ℝ := Real.exp (Real.rpow T a)
  let v : ℝ := Real.exp (Real.rpow T b)
  have huv : u ≤ v := by
    dsimp [u, v]
    exact Real.exp_le_exp.mpr hab
  have hfloor : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
  have hsubsetIcc : Finset.Icc 0 ⌊u⌋₊ ⊆ Finset.Icc 0 ⌊v⌋₊ :=
    Finset.Icc_subset_Icc le_rfl hfloor
  change (∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) =
    (∑ n ∈ Finset.Icc 0 ⌊v⌋₊, if n.Prime then ((n : ℝ)⁻¹) else 0) -
      ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, if n.Prime then ((n : ℝ)⁻¹) else 0
  rw [← Finset.sum_sdiff_eq_sub hsubsetIcc]
  trans ∑ p ∈ primeWindow T a b,
      if p.Prime then ((p : ℝ)⁻¹) else 0
  · apply Finset.sum_congr rfl
    intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
    simp [hpprime]
  · apply Finset.sum_subset
    · intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hpIcc := Finset.mem_Icc.mp hpdata.1
      have hpprime : p.Prime := hpdata.2.1
      have hplow : ⌊u⌋₊ < p := by
        apply (Nat.floor_lt' hpprime.ne_zero).2
        simpa [u] using hpdata.2.2
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le p, by simpa [v] using hpIcc.2⟩,
          fun hpold ↦ (not_lt_of_ge (Finset.mem_Icc.mp hpold).2) hplow⟩
    · intro p hp hpnot
      by_cases hpprime : p.Prime
      · exfalso
        apply hpnot
        have hpdata := Finset.mem_sdiff.mp hp
        have hpV := Finset.mem_Icc.mp hpdata.1
        have hplowFloor : ⌊u⌋₊ < p := by
          by_contra hnot
          apply hpdata.2
          exact Finset.mem_Icc.mpr ⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩
        have hplowReal : u < (p : ℝ) :=
          (Nat.floor_lt' hpprime.ne_zero).1 hplowFloor
        have hceil : Nat.ceil u ≤ p := Nat.ceil_le.mpr hplowReal.le
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by simpa [u] using hceil, by simpa [v] using hpV.2⟩,
            ⟨hpprime, by simpa [u] using hplowReal⟩⟩
      · simp [hpprime]

/- Raw Abel identity.  Keeping the derivative visible makes the theorem reusable with alternative
weight functions and separates finite summation from calculus normalization. -/
theorem primeReciprocalPartialSum_eq_abel_raw {x : ℝ} (_hx : 2 ≤ x) :
    primeReciprocalPartialSum x =
      (Real.log x)⁻¹ * primeLogDivPartialSum x -
        ∫ t in Set.Ioc 2 x,
          deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * primeLogDivPartialSum t := by
  let c : ℕ → ℝ := fun n ↦
    if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0
  have hrewrite : primeReciprocalPartialSum x =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n : ℝ))⁻¹ * c n := by
    unfold primeReciprocalPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
      have hnone : (n : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
      have hlog : Real.log (n : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one hnpos hnone
      simp only [hp, ite_true, c]
      field_simp
    · simp [hp, c]
  rw [hrewrite]
  rw [sum_mul_eq_sub_integral_mul₁ c (f := fun u : ℝ ↦ (Real.log u)⁻¹)
    (by simp [c]) (by simp [c]) x]
  · simp only [primeLogDivPartialSum, c]
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht1 : t ≠ 1 := by linarith [ht.1]
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht.1
    have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one htpos ht1
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1])
        (by linarith [ht.1]))
    exact ContinuousAt.continuousWithinAt (by fun_prop)

/- Calculus-normalized form of the same identity. -/
theorem primeReciprocalPartialSum_eq_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalPartialSum x =
      primeLogDivPartialSum x / Real.log x +
        ∫ t in 2..x,
          primeLogDivPartialSum t / (t * Real.log t ^ 2) := by
  have hraw := primeReciprocalPartialSum_eq_abel_raw hx
  rw [← intervalIntegral.integral_of_le hx] at hraw
  have hint :
      (∫ t in 2..x,
        deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * primeLogDivPartialSum t) =
      ∫ t in 2..x,
        -(primeLogDivPartialSum t / (t * Real.log t ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp [field]
  rw [hint] at hraw
  rw [intervalIntegral.integral_neg] at hraw
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hraw

/- The Abel integral is genuinely integrable, rather than merely assigned the default value zero
by the integral operator.  This is exposed for the later main-term/error-term decomposition. -/
theorem intervalIntegrable_primeLogDivPartialSum_div_log_sq {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ ↦ primeLogDivPartialSum t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x := by
  let c : ℕ → ℝ := fun n ↦
    if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0
  have hderiv : IntegrableOn (deriv fun u : ℝ ↦ (Real.log u)⁻¹) (Set.Icc 2 x) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1])
        (by linarith [ht.1]))
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hraw : IntegrableOn
      (fun t : ℝ ↦ deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) (Set.Icc 2 x) :=
    integrableOn_mul_sum_Icc (c := c) (a := (2 : ℝ)) (b := x) (by norm_num) hderiv
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  refine hraw.neg.congr_fun ?_ measurableSet_Icc
  intro t ht
  change -(deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
    primeLogDivPartialSum t / (t * Real.log t ^ 2)
  rw [Real.deriv_inv_log_apply]
  simp only [primeLogDivPartialSum, c]
  ring

/- The non-prime part of the von Mangoldt Mertens sum.  It consists precisely of higher prime
powers; defining it as a difference lets the next analytic estimate be developed independently
of the finite reindexing. -/
def primePowerMertensExcess (N : ℕ) : ℝ :=
  PrimitiveSetsAboveX.mertensPartialSum N - primeLogDivPartialSum (N : ℝ)

/- The coefficient left after removing the prime terms from `Λ`.  It vanishes at primes and is
supported on higher prime powers (the values at zero and one vanish as well). -/
def primePowerCoefficient (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

@[simp]
theorem primePowerCoefficient_zero : primePowerCoefficient 0 = 0 := by
  simp [primePowerCoefficient]

/- Its prefix sum is exactly the classical Chebyshev gap `ψ - θ`. -/
theorem sum_primePowerCoefficient_eq_psi_sub_theta (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primePowerCoefficient n) =
      Chebyshev.psi x - Chebyshev.theta x := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons,
    primePowerCoefficient_zero, zero_add]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [primePowerCoefficient, hp]
  · simp [primePowerCoefficient, hp]

/- The difference between the von Mangoldt and prime-only Mertens sums is the reciprocal-weighted
sum of `primePowerCoefficient`. -/
theorem primePowerMertensExcess_eq_sum (N : ℕ) :
    primePowerMertensExcess N =
      ∑ n ∈ Finset.Icc 0 N, ((n : ℝ)⁻¹) * primePowerCoefficient n := by
  rw [primePowerMertensExcess, PrimitiveSetsAboveX.mertensPartialSum,
    primeLogDivPartialSum_nat, Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
  have hdiff :
      (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
          (∑ n ∈ Finset.Icc 1 N,
            if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0) =
        ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) * primePowerCoefficient n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      simp [primePowerCoefficient, hp]
    · simp [primePowerCoefficient, hp, div_eq_mul_inv, mul_comm]
  rw [hdiff]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons,
    primePowerCoefficient_zero, mul_zero, zero_add]
  congr 1

/- Exact Abel representation of the higher-prime-power excess.  This reduces its uniform
boundedness to the standard square-root estimate for `ψ - θ` plus one convergent integral. -/
theorem primePowerMertensExcess_eq_abel {N : ℕ} (hN : 1 ≤ N) :
    primePowerMertensExcess N =
      (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) / (N : ℝ) +
        ∫ t in (1 : ℝ)..(N : ℝ),
          (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
  let c : ℕ → ℝ := primePowerCoefficient
  have habel := sum_mul_eq_sub_integral_mul₀ c (f := fun t : ℝ ↦ t⁻¹)
    (by simp [c]) (N : ℝ)
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ),
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (by linarith [ht.1])
  have hint : IntegrableOn (deriv fun u : ℝ ↦ u⁻¹)
      (Set.Icc (1 : ℝ) (N : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ deriv_inv) deriv_inv
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg).continuousWithinAt
  specialize habel hdiff hint
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hN)] at habel
  have hprefix : ∀ t : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
        Chebyshev.psi t - Chebyshev.theta t := by
    intro t
    exact sum_primePowerCoefficient_eq_psi_sub_theta t
  simp_rw [hprefix] at habel
  have hnormalized :
      (∫ t in (1 : ℝ)..(N : ℝ),
        deriv (fun u : ℝ ↦ u⁻¹) t *
          (Chebyshev.psi t - Chebyshev.theta t)) =
      -(∫ t in (1 : ℝ)..(N : ℝ),
        (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    change deriv (fun u : ℝ ↦ u⁻¹) t *
        (Chebyshev.psi t - Chebyshev.theta t) =
      -((Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
    rw [deriv_inv]
    ring
  rw [hnormalized] at habel
  rw [primePowerMertensExcess_eq_sum N]
  simpa [c, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habel

/- The square-root Chebyshev bound makes the endpoint term at most `K` and the integral at most
`2K`.  We keep the constant existential because its numerical value is irrelevant downstream. -/
theorem primePowerMertensExcess_uniformly_bounded :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ ⦃N : ℕ⦄, 2 ≤ N → primePowerMertensExcess N ≤ E := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K : ℝ := max C 0
  have hK0 : 0 ≤ K := by simp [K]
  have hgap : ∀ x : ℝ,
      Chebyshev.psi x - Chebyshev.theta x ≤ K * Real.sqrt x := by
    intro x
    exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg x))
  refine ⟨3 * K, mul_nonneg (by norm_num) hK0, ?_⟩
  intro N hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNreal
  have hsqrt_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    rw [Real.sqrt_le_self_iff]
    exact Or.inr hNreal
  have hendpoint :
      (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) / (N : ℝ) ≤ K := by
    calc
      (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) / (N : ℝ) ≤
          (K * Real.sqrt (N : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hgap (N : ℝ)) hNpos.le
      _ ≤ (K * (N : ℝ)) / (N : ℝ) := by gcongr
      _ = K := by field_simp
  let c : ℕ → ℝ := primePowerCoefficient
  have hderivInt : IntegrableOn (deriv fun u : ℝ ↦ u⁻¹)
      (Set.Icc (1 : ℝ) (N : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ deriv_inv) deriv_inv
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg).continuousWithinAt
  have hrawInt : IntegrableOn
      (fun t : ℝ ↦ deriv (fun u : ℝ ↦ u⁻¹) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      (Set.Icc (1 : ℝ) (N : ℝ)) :=
    integrableOn_mul_sum_Icc (c := c) (a := (1 : ℝ)) (b := (N : ℝ))
      zero_le_one hderivInt
  have htargetInt : IntervalIntegrable
      (fun t : ℝ ↦ (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      MeasureTheory.volume (1 : ℝ) (N : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNreal]
    refine hrawInt.neg.congr_fun ?_ measurableSet_Icc
    intro t ht
    change -(deriv (fun u : ℝ ↦ u⁻¹) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2
    rw [sum_primePowerCoefficient_eq_psi_sub_theta, deriv_inv]
    ring
  have hzero_not_mem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le hNreal]
    simp
  have hrpowInt : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(3 / 2 : ℝ)))
      MeasureTheory.volume (1 : ℝ) (N : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero_not_mem)
  have hpointwise : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ),
      (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 ≤
        K * t ^ (-(3 / 2 : ℝ)) := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans_le ht.1
    calc
      (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 ≤
          (K * Real.sqrt t) / t ^ 2 :=
        div_le_div_of_nonneg_right (hgap t) (sq_nonneg t)
      _ = K * (Real.sqrt t / t ^ 2) := by ring
      _ = K * t ^ (-(3 / 2 : ℝ)) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub htpos]
        norm_num
  have hintegralMajorized :
      (∫ t in (1 : ℝ)..(N : ℝ),
        (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) ≤
      ∫ t in (1 : ℝ)..(N : ℝ), K * t ^ (-(3 / 2 : ℝ)) := by
    exact intervalIntegral.integral_mono_on hNreal htargetInt
      (hrpowInt.const_mul K) hpointwise
  have hrpowIntegralLe :
      (∫ t in (1 : ℝ)..(N : ℝ), t ^ (-(3 / 2 : ℝ))) ≤ 2 := by
    rw [integral_rpow (Or.inr ⟨by norm_num, hzero_not_mem⟩)]
    have hpow : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg N) _
    norm_num [Real.one_rpow]
    linarith
  have hintegral :
      (∫ t in (1 : ℝ)..(N : ℝ),
        (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) ≤ 2 * K := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..(N : ℝ), K * t ^ (-(3 / 2 : ℝ)) := hintegralMajorized
      _ = K * ∫ t in (1 : ℝ)..(N : ℝ), t ^ (-(3 / 2 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ K * 2 := mul_le_mul_of_nonneg_left hrpowIntegralLe hK0
      _ = 2 * K := by ring
  rw [primePowerMertensExcess_eq_abel (show 1 ≤ N by omega)]
  linarith

theorem primePowerMertensExcess_nonneg (N : ℕ) :
    0 ≤ primePowerMertensExcess N := by
  rw [primePowerMertensExcess]
  apply sub_nonneg.mpr
  rw [primeLogDivPartialSum_nat]
  apply sum_log_prime_div_le_mertens
  · intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
  · intro p hp
    exact Nat.prime_of_mem_primesLE hp

/- Once the higher-prime-power excess is uniformly bounded, LeanPool's von Mangoldt estimate
immediately becomes the weighted-prime Mertens estimate. -/
theorem primeLogDivPartialSum_sub_log_le_of_excess
    {N : ℕ} {C E : ℝ}
    (hMertens :
      |PrimitiveSetsAboveX.mertensPartialSum N - Real.log (N : ℝ)| ≤ C)
    (hExcess : primePowerMertensExcess N ≤ E) :
    |primeLogDivPartialSum (N : ℝ) - Real.log (N : ℝ)| ≤ C + E := by
  have hExcess0 := primePowerMertensExcess_nonneg N
  have hid : primeLogDivPartialSum (N : ℝ) - Real.log (N : ℝ) =
      (PrimitiveSetsAboveX.mertensPartialSum N - Real.log (N : ℝ)) -
        primePowerMertensExcess N := by
    unfold primePowerMertensExcess
    ring
  rw [hid]
  calc
    |(PrimitiveSetsAboveX.mertensPartialSum N - Real.log (N : ℝ)) -
        primePowerMertensExcess N| ≤
      |PrimitiveSetsAboveX.mertensPartialSum N - Real.log (N : ℝ)| +
        |primePowerMertensExcess N| := abs_sub _ _
    _ ≤ C + E := by
      rw [abs_of_nonneg hExcess0]
      exact add_le_add hMertens hExcess

theorem weighted_prime_mertens_bounded_error_of_excess
    {E : ℝ} (hE0 : 0 ≤ E)
    (hExcess : ∀ ⦃N : ℕ⦄, 2 ≤ N → primePowerMertensExcess N ≤ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃N : ℕ⦄, 2 ≤ N →
      |primeLogDivPartialSum (N : ℝ) - Real.log (N : ℝ)| ≤ C := by
  obtain ⟨C, hC, hMertens⟩ := Upstream.vonMangoldt_mertens_bounded_error
  refine ⟨C + E, add_pos_of_pos_of_nonneg hC hE0, ?_⟩
  intro N hN
  exact primeLogDivPartialSum_sub_log_le_of_excess (hMertens hN) (hExcess hN)

/- Unconditional weighted-prime Mertens estimate, obtained by combining LeanPool's von Mangoldt
estimate with the now-bounded higher-prime-power contribution. -/
theorem weighted_prime_mertens_bounded_error :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃N : ℕ⦄, 2 ≤ N →
      |primeLogDivPartialSum (N : ℝ) - Real.log (N : ℝ)| ≤ C := by
  obtain ⟨E, hE0, hExcess⟩ := primePowerMertensExcess_uniformly_bounded
  exact weighted_prime_mertens_bounded_error_of_excess hE0 hExcess

/- The same bounded-error estimate at every real endpoint.  Passing from `x` to `floor x` costs
at most one because `floor x ≤ x ≤ 2 floor x` for `x ≥ 2`. -/
theorem weighted_prime_mertens_bounded_error_real :
    ∃ D : ℝ, 0 < D ∧ ∀ ⦃x : ℝ⦄, 2 ≤ x →
      |primeLogDivPartialSum x - Real.log x| ≤ D := by
  obtain ⟨C, hC0, hC⟩ := weighted_prime_mertens_bounded_error
  refine ⟨C + 1, by linarith, ?_⟩
  intro x hx
  let N : ℕ := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hN : 2 ≤ N := by
    exact Nat.le_floor hx
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hfloor_le : (N : ℝ) ≤ x := by
    exact Nat.floor_le hx0
  have hx_lt_floor_add_one : x < (N : ℝ) + 1 := by
    simpa [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hx_le_two_floor : x ≤ 2 * (N : ℝ) := by
    have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  have hratio_pos : 0 < x / (N : ℝ) := div_pos hxpos hNpos
  have hratio_le : x / (N : ℝ) ≤ 2 := by
    exact (div_le_iff₀ hNpos).2 hx_le_two_floor
  have hlog_le : Real.log (N : ℝ) ≤ Real.log x :=
    Real.log_le_log hNpos hfloor_le
  have hlog_diff : Real.log x - Real.log (N : ℝ) ≤ 1 := by
    rw [← Real.log_div (ne_of_gt hxpos) (ne_of_gt hNpos)]
    exact (Real.log_le_sub_one_of_pos hratio_pos).trans (by linarith)
  have hAfloor : primeLogDivPartialSum x = primeLogDivPartialSum (N : ℝ) := by
    unfold primeLogDivPartialSum
    simp [N]
  have hid : primeLogDivPartialSum x - Real.log x =
      (primeLogDivPartialSum (N : ℝ) - Real.log (N : ℝ)) +
        (Real.log (N : ℝ) - Real.log x) := by
    rw [hAfloor]
    ring
  rw [hid]
  calc
    |(primeLogDivPartialSum (N : ℝ) - Real.log (N : ℝ)) +
        (Real.log (N : ℝ) - Real.log x)| ≤
      |primeLogDivPartialSum (N : ℝ) - Real.log (N : ℝ)| +
        |Real.log (N : ℝ) - Real.log x| := abs_add_le _ _
    _ ≤ C + 1 := by
      apply add_le_add (hC hN)
      rw [abs_of_nonpos (sub_nonpos.mpr hlog_le)]
      linarith

/- Mertens' second theorem in the bounded-error form needed for report windows. -/
theorem reciprocal_prime_mertens_bounded_error :
    ∃ B : ℝ, 0 < B ∧ ∀ ⦃x : ℝ⦄, 2 ≤ x →
      |primeReciprocalPartialSum x - Real.log (Real.log x)| ≤ B := by
  obtain ⟨D, hDpos, hD⟩ := weighted_prime_mertens_bounded_error_real
  have hD0 : 0 ≤ D := hDpos.le
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := |1 - Real.log (Real.log 2)| + 2 * (D / Real.log 2)
  have hBpos : 0 < B := by
    dsimp [B]
    have : 0 < D / Real.log 2 := div_pos hDpos hlog2pos
    positivity
  refine ⟨B, hBpos, ?_⟩
  intro x hx
  have hlogxpos : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
  have hlog2le : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hAInt := intervalIntegrable_primeLogDivPartialSum_div_log_sq hx
  have hmainInt : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / Real.log t)
      MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlogt0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    fun_prop
  let err : ℝ → ℝ := fun t ↦
    primeLogDivPartialSum t / (t * Real.log t ^ 2) - t⁻¹ / Real.log t
  have herrInt : IntervalIntegrable err MeasureTheory.volume 2 x := by
    exact hAInt.sub hmainInt
  have hsplit :
      (∫ t in 2..x, primeLogDivPartialSum t / (t * Real.log t ^ 2)) =
        (∫ t in 2..x, err t) + ∫ t in 2..x, t⁻¹ / Real.log t := by
    rw [← intervalIntegral.integral_add herrInt hmainInt]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [err]
    ring
  have hendpoint :
      |(primeLogDivPartialSum x - Real.log x) / Real.log x| ≤ D / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogxpos]
    calc
      |primeLogDivPartialSum x - Real.log x| / Real.log x ≤ D / Real.log x :=
        div_le_div_of_nonneg_right (hD hx) hlogxpos.le
      _ ≤ D / Real.log 2 := by
        exact div_le_div_of_nonneg_left hD0 hlog2pos hlog2le
  have hbaseInt : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / Real.log t ^ 2)
      MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlogt0 : Real.log t ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1])
        (by linarith [ht.1]))
    fun_prop
  have herrPointwise : ∀ t ∈ Set.Icc (2 : ℝ) x,
      |err t| ≤ D * (t⁻¹ / Real.log t ^ 2) := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hdenpos : 0 < t * Real.log t ^ 2 := mul_pos htpos (sq_pos_of_pos hlogtpos)
    have herrRewrite : err t =
        (primeLogDivPartialSum t - Real.log t) / (t * Real.log t ^ 2) := by
      dsimp [err]
      field_simp
    rw [herrRewrite, abs_div, abs_of_pos hdenpos]
    calc
      |primeLogDivPartialSum t - Real.log t| / (t * Real.log t ^ 2) ≤
          D / (t * Real.log t ^ 2) :=
        div_le_div_of_nonneg_right (hD (by linarith [ht.1])) hdenpos.le
      _ = D * (t⁻¹ / Real.log t ^ 2) := by field_simp
  have herrIntegral : |∫ t in 2..x, err t| ≤ D / Real.log 2 := by
    calc
      |∫ t in 2..x, err t| ≤ ∫ t in 2..x, |err t| :=
        intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in 2..x, D * (t⁻¹ / Real.log t ^ 2) :=
        intervalIntegral.integral_mono_on hx herrInt.abs (hbaseInt.const_mul D) herrPointwise
      _ = D * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_div_log_sq
          (by norm_num) (lt_of_lt_of_le (by norm_num) hx)]
      _ ≤ D / Real.log 2 := by
        have hinvlogx : 0 ≤ (Real.log x)⁻¹ := inv_nonneg.mpr hlogxpos.le
        rw [div_eq_mul_inv]
        nlinarith [mul_nonneg hD0 hinvlogx]
  have hdecomp :
      primeReciprocalPartialSum x - Real.log (Real.log x) =
        (primeLogDivPartialSum x - Real.log x) / Real.log x +
          (1 - Real.log (Real.log 2)) + ∫ t in 2..x, err t := by
    rw [primeReciprocalPartialSum_eq_abel hx, hsplit,
      integral_inv_div_log (by norm_num) (lt_of_lt_of_le (by norm_num) hx)]
    have hquot : primeLogDivPartialSum x / Real.log x =
        (primeLogDivPartialSum x - Real.log x) / Real.log x + 1 := by
      field_simp
      ring
    rw [hquot]
    ring
  rw [hdecomp]
  calc
    |(primeLogDivPartialSum x - Real.log x) / Real.log x +
        (1 - Real.log (Real.log 2)) + ∫ t in 2..x, err t| ≤
      |(primeLogDivPartialSum x - Real.log x) / Real.log x| +
        |1 - Real.log (Real.log 2)| + |∫ t in 2..x, err t| := by
      calc
        _ ≤ |(primeLogDivPartialSum x - Real.log x) / Real.log x +
              (1 - Real.log (Real.log 2))| + |∫ t in 2..x, err t| := abs_add_le _ _
        _ ≤ (|(primeLogDivPartialSum x - Real.log x) / Real.log x| +
              |1 - Real.log (Real.log 2)|) + |∫ t in 2..x, err t| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ D / Real.log 2 + |1 - Real.log (Real.log 2)| + D / Real.log 2 := by
      gcongr
    _ = B := by
      dsimp [B]
      ring

/- Subtracting two copies of Mertens' second theorem gives a uniform error for every report-style
prime window whose lower endpoint is at least two. -/
theorem primeWindow_reciprocal_mass_bounded_error :
    ∃ B : ℝ, 0 < B ∧ ∀ ⦃T a b : ℝ⦄,
      Real.rpow T a ≤ Real.rpow T b →
      2 ≤ Real.exp (Real.rpow T a) →
      |(∑ p ∈ primeWindow T a b, ((p : ℝ)⁻¹)) -
        (Real.log (Real.log (Real.exp (Real.rpow T b))) -
          Real.log (Real.log (Real.exp (Real.rpow T a))))| ≤ B := by
  obtain ⟨C, hCpos, hC⟩ := reciprocal_prime_mertens_bounded_error
  refine ⟨2 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro T a b hab hlower
  have hupper : 2 ≤ Real.exp (Real.rpow T b) :=
    hlower.trans (Real.exp_le_exp.mpr hab)
  rw [primeWindow_reciprocal_mass_eq_partialSum_sub hab]
  have hid :
      (primeReciprocalPartialSum (Real.exp (Real.rpow T b)) -
          primeReciprocalPartialSum (Real.exp (Real.rpow T a))) -
        (Real.log (Real.log (Real.exp (Real.rpow T b))) -
          Real.log (Real.log (Real.exp (Real.rpow T a)))) =
      (primeReciprocalPartialSum (Real.exp (Real.rpow T b)) -
          Real.log (Real.log (Real.exp (Real.rpow T b)))) -
        (primeReciprocalPartialSum (Real.exp (Real.rpow T a)) -
          Real.log (Real.log (Real.exp (Real.rpow T a)))) := by ring
  rw [hid]
  exact (abs_sub _ _).trans <| by
    linarith [hC hupper, hC hlower]

theorem report_loglog_endpoint_difference {T a b : ℝ} (hT : 0 < T) :
    Real.log (Real.log (Real.exp (Real.rpow T b))) -
        Real.log (Real.log (Real.exp (Real.rpow T a))) =
      (b - a) * Real.log T := by
  rw [Real.log_exp, Real.log_exp]
  calc
    Real.log (Real.rpow T b) - Real.log (Real.rpow T a) =
        b * Real.log T - a * Real.log T :=
      congrArg₂ (fun u v : ℝ ↦ u - v) (Real.log_rpow hT b) (Real.log_rpow hT a)
    _ = (b - a) * Real.log T := by ring

/- If the upper exponent is at most one, the endpoint truncation in the report definition is
redundant once `log X ≥ 1`. -/
theorem reportPrimeWindowEndpointMass_eq_primeWindow_mass
    {X : ℕ} {a b : ℝ} (hX : 0 < X)
    (hlog : 1 ≤ Real.log (X : ℝ)) (hb1 : b ≤ 1) :
    reportPrimeWindowEndpointMass X a b =
      ∑ p ∈ primeWindow (Real.log (X : ℝ)) a b, ((p : ℝ)⁻¹) := by
  unfold reportPrimeWindowEndpointMass reportPrimeWindowInEndpoint reportPrimeWindow
  rw [Finset.inter_eq_left.mpr]
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  have hpIcc := Finset.mem_Icc.mp hpdata.1
  have hpprime : p.Prime := hpdata.2.1
  have hpUpper : (p : ℝ) ≤
      Real.exp (Real.rpow (Real.log (X : ℝ)) b) := by
    have hpFloor : (p : ℝ) ≤
        (Nat.floor (Real.exp (Real.rpow (Real.log (X : ℝ)) b)) : ℝ) := by
      exact_mod_cast hpIcc.2
    exact hpFloor.trans (Nat.floor_le (Real.exp_nonneg _))
  have hrpow : Real.rpow (Real.log (X : ℝ)) b ≤ Real.log (X : ℝ) :=
    Real.rpow_le_self_of_one_le hlog hb1
  have hexp : Real.exp (Real.rpow (Real.log (X : ℝ)) b) ≤ (X : ℝ) := by
    have h := Real.exp_le_exp.mpr hrpow
    rw [Real.exp_log (by exact_mod_cast hX)] at h
    exact h
  exact Finset.mem_Icc.mpr
    ⟨hpprime.one_le, by exact_mod_cast hpUpper.trans hexp⟩

/- Sharp main term for the endpoint-truncated report window, up to one uniform additive error. -/
theorem reportPrimeWindowEndpointMass_bounded_error
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℕ in atTop,
      |reportPrimeWindowEndpointMass X a b -
        (b - a) * Real.log (Real.log (X : ℝ))| ≤ B := by
  obtain ⟨B, hBpos, hwindow⟩ := primeWindow_reciprocal_mass_bounded_error
  refine ⟨B, hBpos, ?_⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ ↦
      Real.rpow (Real.log (X : ℝ)) a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp hlog
  have hexp : Tendsto (fun X : ℕ ↦
      Real.exp (Real.rpow (Real.log (X : ℝ)) a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hpow
  filter_upwards [eventually_gt_atTop (0 : ℕ),
      hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      hexp.eventually (eventually_ge_atTop (2 : ℝ))]
    with X hX hlogX hlower
  have hTpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hpowers : Real.rpow (Real.log (X : ℝ)) a ≤
      Real.rpow (Real.log (X : ℝ)) b :=
    Real.rpow_le_rpow_of_exponent_le hlogX hab.le
  have hraw := hwindow hpowers hlower
  rw [reportPrimeWindowEndpointMass_eq_primeWindow_mass hX hlogX hb1.le]
  rw [← report_loglog_endpoint_difference hTpos]
  exact hraw

/- In particular the report-window mass has an eventual lower bound with half of its sharp main
coefficient.  Unlike the dyadic proof, this only requires `a < b`, not `2a < b`. -/
theorem eventually_reportPrimeWindowEndpointMass_ge_half_main
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1) :
    ∀ᶠ X : ℕ in atTop,
      (b - a) / 2 * Real.log (Real.log (X : ℝ)) ≤
        reportPrimeWindowEndpointMass X a b := by
  obtain ⟨B, hBpos, hbound⟩ :=
    reportPrimeWindowEndpointMass_bounded_error ha hab hb1
  have hloglog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hhalf : 0 < (b - a) / 2 := by linarith
  have hscaled : Tendsto (fun X : ℕ ↦
      (b - a) / 2 * Real.log (Real.log (X : ℝ))) atTop atTop :=
    hloglog.const_mul_atTop hhalf
  filter_upwards [hbound, hscaled.eventually (eventually_ge_atTop B)]
    with X herror hlarge
  have hlower := neg_le_of_abs_le herror
  linarith

/- The factor `1/2` above is only a convenient specialization.  Every fixed positive relative
error may be absorbed by the divergent main term. -/
theorem eventually_reportPrimeWindowEndpointMass_ge_one_sub_mul_main
    {a b eta : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1)
    (heta : 0 < eta) :
    ∀ᶠ X : ℕ in atTop,
      (1 - eta) * (b - a) * Real.log (Real.log (X : ℝ)) ≤
        reportPrimeWindowEndpointMass X a b := by
  obtain ⟨B, hBpos, hbound⟩ :=
    reportPrimeWindowEndpointMass_bounded_error ha hab hb1
  have hloglog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hcoef : 0 < eta * (b - a) := mul_pos heta (sub_pos.mpr hab)
  have hscaled : Tendsto (fun X : ℕ ↦
      eta * (b - a) * Real.log (Real.log (X : ℝ))) atTop atTop :=
    hloglog.const_mul_atTop hcoef
  filter_upwards [hbound, hscaled.eventually (eventually_ge_atTop B)]
    with X herror hlarge
  have hlower := neg_le_of_abs_le herror
  nlinarith

theorem tendsto_reportPrimeWindowEndpointMass_atTop_of_lt
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1) :
    Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X a b) atTop atTop := by
  have hlower := eventually_reportPrimeWindowEndpointMass_ge_half_main ha hab hb1
  have hloglog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hhalf : 0 < (b - a) / 2 := by linarith
  have hscaled : Tendsto (fun X : ℕ ↦
      (b - a) / 2 * Real.log (Real.log (X : ℝ))) atTop atTop :=
    hloglog.const_mul_atTop hhalf
  exact Filter.tendsto_atTop_mono' atTop hlower hscaled

end

end Erdos878

#print axioms Erdos878.primeReciprocalPartialSum_eq_abel
#print axioms Erdos878.primePowerMertensExcess_uniformly_bounded
#print axioms Erdos878.weighted_prime_mertens_bounded_error_of_excess
#print axioms Erdos878.weighted_prime_mertens_bounded_error
#print axioms Erdos878.weighted_prime_mertens_bounded_error_real
#print axioms Erdos878.reciprocal_prime_mertens_bounded_error
#print axioms Erdos878.primeWindow_reciprocal_mass_bounded_error
#print axioms Erdos878.reportPrimeWindowEndpointMass_bounded_error
#print axioms Erdos878.eventually_reportPrimeWindowEndpointMass_ge_half_main
#print axioms Erdos878.eventually_reportPrimeWindowEndpointMass_ge_one_sub_mul_main
