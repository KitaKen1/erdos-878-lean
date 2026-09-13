import Erdos878FC

/-!
# Track A: counting and endpoint losses of an admissible matching

The terms in this module are actual admissible integers (in particular, products of powers of
two matched primes may be used).  They are not weights bounded by a single prime power.
The two analytic errors are the number of unmatched prime slots and the total endpoint loss.
Both may be nonzero: their normalized limits must vanish.  No exact eventual `F/scale ≥ 1/2`
is required.
-/

open Classical Filter Asymptotics
open scoped Topology Real

namespace Erdos878

def admissibleEndpointLoss (n : ℕ) (P : Finset ℕ) : ℕ := ∑ a ∈ P, (n - a)

noncomputable def unusedPrimeFactors (n : ℕ) (P : Finset ℕ) : Finset ℕ :=
  n.primeFactors \ P.biUnion Nat.primeFactors

/-- In a two-prime matching, the abstract cardinality deficit is exactly the number of
prime factors left unused. Pairwise coprimality prevents double counting. -/
theorem paired_card_add_unused_eq_omega {n : ℕ} (hn : n ≠ 0) {P : Finset ℕ}
    (hP : IsAdmissible n P) (hpairs : ∀ a ∈ P, a.primeFactors.card = 2) :
    2 * P.card + (unusedPrimeFactors n P).card = omega n := by
  have hdisj : (P : Set ℕ).PairwiseDisjoint Nat.primeFactors := by
    intro a ha b hb hab
    exact (hP.2.1 ha hb hab).disjoint_primeFactors
  have hsub : P.biUnion Nat.primeFactors ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpa
    exact Nat.mem_primeFactors.mpr
      ⟨hpp, hP.2.2 a ha p hpp (Nat.dvd_of_mem_primeFactors hpa), hn⟩
  have hcovered : (P.biUnion Nat.primeFactors).card = 2 * P.card := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ a ∈ P, a.primeFactors.card) = ∑ _a ∈ P, 2 :=
        Finset.sum_congr rfl hpairs
      _ = 2 * P.card := by simp [Nat.mul_comm]
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  rw [hcovered] at hsplit
  simpa [unusedPrimeFactors, omega, Nat.add_comm] using hsplit

theorem matching_deficit_eq_unusedPrimeFactors {n : ℕ} (hn : n ≠ 0) {P : Finset ℕ}
    (hP : IsAdmissible n P) (hpairs : ∀ a ∈ P, a.primeFactors.card = 2) :
    (omega n : ℝ) - 2 * (P.card : ℝ) = ((unusedPrimeFactors n P).card : ℝ) := by
  have hnat := paired_card_add_unused_eq_omega hn hP hpairs
  have hcast : 2 * (P.card : ℝ) + ((unusedPrimeFactors n P).card : ℝ) = (omega n : ℝ) := by
    exact_mod_cast hnat
  linarith

theorem admissible_sum_add_endpointLoss {n : ℕ} (P : Finset ℕ)
    (hupper : ∀ a ∈ P, a ≤ n) :
    (∑ a ∈ P, a) + admissibleEndpointLoss n P = n * P.card := by
  unfold admissibleEndpointLoss
  rw [← Finset.sum_add_distrib]
  calc
    (∑ a ∈ P, (a + (n - a))) = ∑ _a ∈ P, n := by
      apply Finset.sum_congr rfl
      intro a ha
      have := hupper a ha
      omega
    _ = n * P.card := by simp [Nat.mul_comm]

/-- Exact loss accounting; the term count and the endpoint loss remain separate. -/
theorem normalized_admissible_sum_eq_card_sub_loss
    {n : ℕ} (hn : n ≠ 0) (P : Finset ℕ) (hupper : ∀ a ∈ P, a ≤ n) :
    ((∑ a ∈ P, a : ℕ) : ℝ) / scale n =
      (P.card : ℝ) / Real.log (Real.log (n : ℝ)) -
        (admissibleEndpointLoss n P : ℝ) / scale n := by
  have hid : ((∑ a ∈ P, a : ℕ) : ℝ) + (admissibleEndpointLoss n P : ℝ) =
      (n : ℝ) * (P.card : ℝ) := by
    exact_mod_cast admissible_sum_add_endpointLoss P hupper
  have hdiv := congrArg (fun t : ℝ ↦ t / scale n) hid
  have hcancel : (n : ℝ) * (P.card : ℝ) / scale n =
      (P.card : ℝ) / Real.log (Real.log (n : ℝ)) := by
    unfold scale
    rw [mul_div_mul_left _ _ (by exact_mod_cast hn : (n : ℝ) ≠ 0)]
  rw [add_div, hcancel] at hdiv
  linarith

theorem F_div_scale_ge_card_sub_endpointLoss
    {n : ℕ} (hn : n ≠ 0) {P : Finset ℕ}
    (hP : IsAdmissible n P) (hscale : 0 < scale n) :
    (P.card : ℝ) / Real.log (Real.log (n : ℝ)) -
        (admissibleEndpointLoss n P : ℝ) / scale n ≤ (F n : ℝ) / scale n := by
  rw [← normalized_admissible_sum_eq_card_sub_loss hn P
    (fun a ha ↦ (Finset.mem_Icc.mp (hP.1 ha)).2)]
  apply div_le_div_of_nonneg_right _ hscale.le
  exact_mod_cast sum_le_F_of_admissible hP

/-- The true matching target: density-one normal order, almost `ω(n)/2` admissible terms,
and endpoint loss `o(n log log n)`.  The source-block theorem supplies the `f` term on a
second density-one set; the two sets are intersected in the proof. -/
theorem proposed_first_question_sharp_of_matching_deficits
    (A : Set ℕ) (hA : A.HasDensity 1) (P : A → Finset ℕ)
    (hP : ∀ᶠ n : A in atTop, IsAdmissible (n : ℕ) (P n))
    (hω : Tendsto (fun n : A ↦ (omega (n : ℕ) : ℝ) /
      Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 1))
    (hmiss : Tendsto (fun n : A ↦
      ((omega (n : ℕ) : ℝ) - 2 * ((P n).card : ℝ)) /
        Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 0))
    (hloss : Tendsto (fun n : A ↦
      (admissibleEndpointLoss (n : ℕ) (P n) : ℝ) / scale (n : ℕ)) atTop (𝓝 0)) :
    erdos_878.variants.proposed_first_question_sharp := by
  obtain ⟨S, hS, hfS⟩ := exists_density_one_f_div_scale_littleO_of_source_blocks
  let J : Set ℕ := S ∩ A
  have hJ : J.HasDensity 1 := hasDensity_one_inter_of_hasDensity_one hS hA
  have hJinf : J.Infinite := Nat.infinite_of_hasDensity_pos hJ (by norm_num)
  let toA : J → A := fun n ↦ ⟨(n : ℕ), n.property.2⟩
  have htoA : Tendsto toA atTop atTop :=
    tendsto_inter_subtype_to_right hJinf
  have htoS : Tendsto (fun n : J ↦ (⟨(n : ℕ), n.property.1⟩ : S)) atTop atTop :=
    tendsto_inter_subtype_to_left (S := S) (T := A) hJinf
  have hcoe : Tendsto (fun n : J ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hJinf b
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : J)] with n hn
    exact hba.le.trans hn
  have hfJ : (fun n : J ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : J ↦ scale (n : ℕ)) := by
    simpa [Function.comp_def] using hfS.comp_tendsto htoS
  have hωJ : Tendsto (fun n : J ↦ (omega (n : ℕ) : ℝ) /
      Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, toA] using hω.comp htoA
  have hcardA : Tendsto (fun n : A ↦ ((P n).card : ℝ) /
      Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 (1 / 2 : ℝ)) := by
    have ht := (hω.sub hmiss).div_const 2
    convert ht using 1 <;> try norm_num
    funext n
    ring
  have hlower : Tendsto (fun n : J ↦
      ((P (toA n)).card : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)) -
        (admissibleEndpointLoss (n : ℕ) (P (toA n)) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Function.comp_def, toA, sub_zero] using (hcardA.sub hloss).comp htoA
  have hupper : Tendsto (fun n : J ↦
      (f (n : ℕ) : ℝ) / scale (n : ℕ) +
        ((omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ))) / 2 +
        1 / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (hfJ.tendsto_div_nhds_zero.add (hωJ.div_const 2)).add
      (tendsto_inv_scale_zero.comp hcoe)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  have hbounds : ∀ᶠ n : J in atTop,
      ((P (toA n)).card : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ)) -
        (admissibleEndpointLoss (n : ℕ) (P (toA n)) : ℝ) / scale (n : ℕ) ≤
          (F (n : ℕ) : ℝ) / scale (n : ℕ) ∧
      (F (n : ℕ) : ℝ) / scale (n : ℕ) ≤
        (f (n : ℕ) : ℝ) / scale (n : ℕ) +
          ((omega (n : ℕ) : ℝ) / Real.log (Real.log ((n : ℕ) : ℝ))) / 2 +
          1 / scale (n : ℕ) := by
    filter_upwards [htoA.eventually hP, hcoe.eventually (eventually_gt_atTop (1 : ℕ)),
      hcoe.eventually eventually_scale_pos,
      (hlog.comp hcoe).eventually (eventually_gt_atTop (0 : ℝ))] with n hn hn1 hscale hll
    exact ⟨F_div_scale_ge_card_sub_endpointLoss (by omega) hn hscale,
      F_div_scale_le hn1 hll⟩
  apply proposed_first_question_sharp_of_component_inputs J hJ hfJ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hbounds.mono fun _ hn ↦ hn.1) (hbounds.mono fun _ hn ↦ hn.2)

end Erdos878
