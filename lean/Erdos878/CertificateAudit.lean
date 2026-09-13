import Erdos878FC

/-!
# Feasibility checks for proposed analytic certificates

A conditional theorem can compile even when its assumptions are impossible.  This module
checks two recently proposed shortcuts against elementary upper bounds.  The results rule out
the shortcuts, not any of the three Erdős targets.
-/

open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

theorem weightedDivisorCount_le_f_of_prime_power_weights
    {n : ℕ} (hn : n ≠ 0) (R : Finset ℕ) (w : ℕ → ℝ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hweight : ∀ p ∈ R, p ∣ n → w p ≤ (p ^ Nat.log p n : ℕ)) :
    weightedDivisorCount R w n ≤ (f n : ℝ) := by
  let S := R.filter (fun p ↦ p ∣ n)
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hpR, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hpR, hpd, hn⟩
  calc
    weightedDivisorCount R w n = ∑ p ∈ S, w p := by
      simp only [weightedDivisorCount, S, Finset.sum_filter]
    _ ≤ ∑ p ∈ S, ((p ^ Nat.log p n : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hweight p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
    _ ≤ ∑ p ∈ n.primeFactors, ((p ^ Nat.log p n : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = (f n : ℝ) := by simp [f]

private theorem sum_le_prod_of_two_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) : (∑ p ∈ S, p) ≤ ∏ p ∈ S, p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have ha2 := hS a (Finset.mem_insert_self _ _)
    have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp ↦ hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    by_cases hEmpty : S = ∅
    · simp [hEmpty]
    · have hprod2 : 2 ≤ ∏ p ∈ S, p := by
        obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
        exact (hS2 p hp).trans (Nat.le_of_dvd
          (Finset.prod_pos (fun q hq ↦ lt_of_lt_of_le (by norm_num) (hS2 q hq)))
          (Finset.dvd_prod_of_mem id hp))
      exact (Nat.add_le_add_left (ih hS2) a).trans (Nat.add_le_mul ha2 hprod2)

theorem sum_primeFactors_le_self {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ n.primeFactors, p) ≤ n := by
  exact (sum_le_prod_of_two_le n.primeFactors
    (fun _ hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le)).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

/-- Requiring one weight to be valid for every `1 ≤ n ≤ X` forces `w p ≤ p`, by taking `n=p`.
Thus these prefix-uniform weights cannot benefit from large powers at the endpoint. -/
theorem weightedDivisorCount_le_self_of_prefix_weights
    {X n : ℕ} (hn : n ∈ Finset.Icc 1 X) (R : Finset ℕ) (w : ℕ → ℝ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hweight : ∀ m ∈ Finset.Icc 1 X, ∀ p ∈ R, p ∣ m →
      w p ≤ (p ^ Nat.log p m : ℕ)) :
    weightedDivisorCount R w n ≤ (n : ℝ) := by
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  let S := R.filter (fun p ↦ p ∣ n)
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hpR, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hpR, hpd, hn0⟩
  have hw : ∀ p ∈ S, w p ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpR, hpd⟩ := Finset.mem_filter.mp hp
    have hpp := hprime p hpR
    have hpX : p ≤ X := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd).trans
      (Finset.mem_Icc.mp hn).2
    have hbound := hweight p (Finset.mem_Icc.mpr ⟨hpp.one_le, hpX⟩) p hpR (dvd_refl p)
    have hlogp : Nat.log p p = 1 := by simpa using Nat.log_pow hpp.one_lt 1
    simpa [hlogp] using hbound
  calc
    weightedDivisorCount R w n = ∑ p ∈ S, w p := by
      simp only [weightedDivisorCount, S, Finset.sum_filter]
    _ ≤ ∑ p ∈ S, (p : ℝ) := Finset.sum_le_sum hw
    _ ≤ ∑ p ∈ n.primeFactors, (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ (n : ℝ) := by
      have hnat := sum_primeFactors_le_self hn0
      have hcast := Nat.cast_le (α := ℝ).mpr hnat
      simpa only [Nat.cast_sum] using hcast

/-- The normalized variance of the proposed prefix-uniform certificate is at least one once
`log log X ≥ 2`.  This is a finite obstruction, independent of normal-order theorems. -/
theorem normalized_variance_ge_one_of_prefix_weights
    {X : ℕ} (hX : 0 < X) (hlog : 2 ≤ Real.log (Real.log (X : ℝ)))
    (R : Finset ℕ) (w : ℕ → ℝ) (V : ℝ)
    (hprime : ∀ p ∈ R, p.Prime)
    (hweight : ∀ m ∈ Finset.Icc 1 X, ∀ p ∈ R, p ∣ m →
      w p ≤ (p ^ Nat.log p m : ℕ))
    (hvar : ∑ n ∈ Finset.Icc 1 X,
      (weightedDivisorCount R w n - scale X) ^ 2 ≤ V) :
    1 ≤ 4 * V / (scale X ^ 2 * (X : ℝ)) := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hscale : 2 * (X : ℝ) ≤ scale X := by
    simpa [scale, mul_comm] using mul_le_mul_of_nonneg_left hlog hXR.le
  have hscalePos : 0 < scale X := by linarith
  have hpoint : ∀ n ∈ Finset.Icc 1 X,
      scale X ^ 2 / 4 ≤ (weightedDivisorCount R w n - scale X) ^ 2 := by
    intro n hn
    have hnX : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hw := weightedDivisorCount_le_self_of_prefix_weights hn R w hprime hweight
    have hdiff : scale X / 2 ≤ scale X - weightedDivisorCount R w n := by linarith
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ scale X / 2)
      (by linarith : 0 ≤ scale X - weightedDivisorCount R w n)
    have := hsq.mpr hdiff
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  have hcard : (Finset.Icc 1 X).card = X := by simp
  have htotal : (X : ℝ) * (scale X ^ 2 / 4) ≤ V := by
    simpa [hcard] using hsum.trans hvar
  apply (le_div_iff₀ (by positivity : 0 < scale X ^ 2 * (X : ℝ))).mpr
  nlinarith

/-- Refutes the exact four-input weighted-moment package previously presented as Track A's
remaining analytic obligation.  It is not an available proof route. -/
theorem not_prefix_prime_power_moment_certificate
    (R : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (hprime : ∀ X, ∀ p ∈ R X, p.Prime)
    (hweight : ∀ᶠ X : ℕ in atTop, ∀ n ∈ Finset.Icc 1 X,
      ∀ p ∈ R X, p ∣ n → 0 ≤ w X p ∧ w X p ≤ (p ^ Nat.log p n : ℕ))
    (hvar : ∀ᶠ X : ℕ in atTop, ∑ n ∈ Finset.Icc 1 X,
      (weightedDivisorCount (R X) (w X) n - scale X) ^ 2 ≤ V X) :
    ¬ Tendsto (fun X : ℕ ↦ 4 * V X / (scale X ^ 2 * (X : ℝ))) atTop (𝓝 0) := by
  intro hvanish
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  obtain ⟨X, hX, hlogX, hw, hv, hsmall⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and ((hlog.eventually (eventually_ge_atTop (2 : ℝ))).and
      (hweight.and (hvar.and (hvanish.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))))))).exists
  have hlarge := normalized_variance_ge_one_of_prefix_weights hX hlogX
    (R X) (w X) (V X) (hprime X) (fun n hn p hp hd ↦ (hw n hn p hp hd).2) hv
  exact (not_lt_of_ge hlarge) hsmall

theorem reciprocal_prime_mass_le_half_card (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤ (S.card : ℝ) / 2 := by
  calc
    (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤ ∑ _p ∈ S, (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    _ = (S.card : ℝ) / 2 := by simp [div_eq_mul_inv]

theorem card_le_h_of_prime_product_le {X : ℕ} (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hprod : primeProduct S ≤ X) : S.card ≤ h X := by
  have hpos := primeProduct_pos hprime
  have hsub : S ⊆ (primeProduct S).primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr
      ⟨hprime p hp, Finset.dvd_prod_of_mem id hp, hpos.ne'⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.le_sup (f := omega) (Finset.mem_range.mpr (Nat.lt_succ_of_le hprod)))

theorem packed_reciprocal_mass_le_half_mul_h {X : ℕ} (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hprod : primeProduct S ≤ X) :
    (multipleBelow X S : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) ≤
      (X : ℝ) * (h X : ℝ) / 2 := by
  have hcard : (S.card : ℝ) ≤ (h X : ℝ) := by
    exact_mod_cast card_le_h_of_prime_product_le S hprime hprod
  have hnX : (multipleBelow X S : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast multipleBelow_le X S
  have hmass := (reciprocal_prime_mass_le_half_card S hprime).trans
    (div_le_div_of_nonneg_right hcard (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ (multipleBelow X S : ℝ) * ((h X : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (X : ℝ) * ((h X : ℝ) / 2) := mul_le_mul_of_nonneg_right hnX (by positivity)
    _ = _ := by ring

/-- A uniform `3/4` ceiling already contradicts the proposed `1-o(1)` reciprocal-mass route. -/
theorem eventually_packed_reciprocal_mass_ratio_le_three_quarters :
    ∀ᶠ X : ℕ in atTop, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      primeProduct S ≤ X →
      (multipleBelow X S : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) / maximalOrderScale X ≤ 3 / 4 := by
  filter_upwards [eventually_max_card_primeFactors_le_log_div_loglog
    (1 / 2 : ℝ) (by norm_num), eventually_maximalOrderScale_pos] with X hω hscale S hprime hprod
  have hω' : (h X : ℝ) ≤
      (1 + (1 / 2 : ℝ)) * Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) := hω
  have hmul := mul_le_mul_of_nonneg_left hω' (show 0 ≤ (X : ℝ) by positivity)
  have hbound : (X : ℝ) * (h X : ℝ) ≤ (3 / 2 : ℝ) * maximalOrderScale X := by
    calc
      _ ≤ (X : ℝ) * ((1 + (1 / 2 : ℝ)) * Real.log (X : ℝ) /
        Real.log (Real.log (X : ℝ))) := hmul
      _ = _ := by unfold maximalOrderScale; ring
  apply (div_le_iff₀ hscale).mpr
  have hfinite := packed_reciprocal_mass_le_half_mul_h S hprime hprod
  linarith

theorem not_selected_reciprocal_mass_certificate :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) ∧ primeProduct S ≤ X ∧
        1 - ε ≤ (multipleBelow X S : ℝ) * (∑ p ∈ S, ((p : ℝ)⁻¹)) /
          maximalOrderScale X) := by
  intro hselect
  obtain ⟨X, hu, S, hp, hprod, hl⟩ :=
    (eventually_packed_reciprocal_mass_ratio_le_three_quarters.and
      (hselect (1 / 8) (by norm_num))).exists
  have := hu S hp hprod
  linarith

end Erdos878
