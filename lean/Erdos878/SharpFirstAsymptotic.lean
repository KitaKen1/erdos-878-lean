import Erdos878.SharpFirstLower
import Erdos878.OmegaNormalOrder

/-!
# The sharp first-question asymptotic

This file diagonalizes the fixed-coefficient lower bounds from the multi-window construction,
then combines the resulting lower half-limit with the elementary upper bound, the normal order
of `omega`, and the already proved little-`o` estimate for `f`.
-/

open Classical Filter Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

/-- Transfers an eventual statement to an eventually contained infinite set. -/
theorem eventually_of_eventually_mem_of_eventually_subtype
    {A D : Set ℕ} (hAinf : A.Infinite) (hDinf : D.Infinite) {P : ℕ → Prop}
    (hmem : ∀ᶠ n : D in atTop, (n : ℕ) ∈ A)
    (hP : ∀ᶠ n : A in atTop, P (n : ℕ)) :
    ∀ᶠ n : D in atTop, P (n : ℕ) := by
  obtain ⟨a, ha⟩ := hAinf.nonempty
  let _ : Nonempty A := ⟨⟨a, ha⟩⟩
  obtain ⟨b, hb⟩ := eventually_atTop.1 hP
  have hcoe : Tendsto (fun n : D ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    obtain ⟨d, hd, hbd⟩ := Set.Infinite.exists_gt hDinf bound
    filter_upwards [eventually_ge_atTop (⟨d, hd⟩ : D)] with n hn
    exact hbd.le.trans hn
  filter_upwards [hmem, hcoe.eventually (eventually_ge_atTop (b : ℕ))]
    with n hnA hbn
  exact hb (⟨(n : ℕ), hnA⟩ : A) hbn

/-- One density-one set supports every fixed lower coefficient strictly below `1/2`. -/
theorem exists_density_one_F_div_scale_eventually_gt_of_lt_half :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ c : ℝ, c < 1 / 2 →
        ∀ᶠ n : A in atTop, c < (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
  let coefficient : ℕ → ℝ := fun i ↦ 1 / 2 - sharpFirstLoss i
  have hcoefficient : Tendsto coefficient atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa [coefficient] using
      (tendsto_const_nhds.sub tendsto_sharpFirstLoss_zero)
  have hcoefficient_lt : ∀ i, coefficient i < 1 / 2 := by
    intro i
    dsimp [coefficient]
    have hloss : 0 < sharpFirstLoss i := by
      unfold sharpFirstLoss
      positivity
    linarith
  have hexists : ∀ i : ℕ, ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : A in atTop,
        coefficient i ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    intro i
    exact exists_density_one_F_div_scale_ge_of_lt_half (hcoefficient_lt i)
  choose A hA hLower using hexists
  let B : ℕ → Set ℕ := fun i ↦ (A i)ᶜ
  have hB : ∀ i, (B i).HasDensity 0 := by
    intro i
    dsimp [B]
    exact hasDensity_zero_of_hasDensity_one_compl (hA i)
  rcases exists_density_one_eventually_avoids B hB with ⟨D, hD, hAvoid⟩
  have hDinf : D.Infinite := Nat.infinite_of_hasDensity_pos hD (by norm_num)
  have hAinf : ∀ i, (A i).Infinite := fun i ↦
    Nat.infinite_of_hasDensity_pos (hA i) (by norm_num)
  have hLowerD : ∀ i, ∀ᶠ n : D in atTop,
      coefficient i ≤ (F (n : ℕ) : ℝ) / scale (n : ℕ) := by
    intro i
    exact eventually_of_eventually_mem_of_eventually_subtype
      (P := fun n ↦ coefficient i ≤ (F n : ℝ) / scale n)
      (hAinf i) hDinf
      (by
        filter_upwards [hAvoid i] with n hn
        simpa [B] using hn)
      (hLower i)
  refine ⟨D, hD, ?_⟩
  intro c hc
  have hlate : ∀ᶠ i : ℕ in atTop, c < coefficient i :=
    (tendsto_order.1 hcoefficient).1 c hc
  obtain ⟨i, hci⟩ := hlate.exists
  filter_upwards [hLowerD i] with n hn
  exact hci.trans_le hn

/-- The normalized extremal sum has sharp coefficient `1/2` on a density-one set. -/
theorem exists_density_one_F_div_scale_tendsto_half :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
        atTop (𝓝 (1 / 2 : ℝ)) := by
  rcases exists_density_one_F_div_scale_eventually_gt_of_lt_half with
    ⟨L, hL, hLowerL⟩
  rcases exists_density_one_f_div_scale_littleO_of_source_blocks with
    ⟨S, hS, hfS⟩
  rcases exists_density_one_omega_normal_order with
    ⟨O, hO, homegaO⟩
  let I : Set ℕ := S ∩ O
  let J : Set ℕ := I ∩ L
  have hI : I.HasDensity 1 := by
    dsimp [I]
    exact hasDensity_one_inter_of_hasDensity_one hS hO
  have hJ : J.HasDensity 1 := by
    dsimp [J]
    exact hasDensity_one_inter_of_hasDensity_one hI hL
  have hIinf : I.Infinite := Nat.infinite_of_hasDensity_pos hI (by norm_num)
  have hJinf : J.Infinite := Nat.infinite_of_hasDensity_pos hJ (by norm_num)
  let toI : J → I := fun n ↦ ⟨(n : ℕ), n.property.1⟩
  let toL : J → L := fun n ↦ ⟨(n : ℕ), n.property.2⟩
  let toS : I → S := fun n ↦ ⟨(n : ℕ), n.property.1⟩
  let toO : I → O := fun n ↦ ⟨(n : ℕ), n.property.2⟩
  have htoI : Tendsto toI atTop atTop := by
    simpa [toI, J] using
      (tendsto_inter_subtype_to_left (S := I) (T := L) hJinf)
  have htoL : Tendsto toL atTop atTop := by
    simpa [toL, J] using
      (tendsto_inter_subtype_to_right (S := I) (T := L) hJinf)
  have htoS : Tendsto toS atTop atTop := by
    simpa [toS, I] using
      (tendsto_inter_subtype_to_left (S := S) (T := O) hIinf)
  have htoO : Tendsto toO atTop atTop := by
    simpa [toO, I] using
      (tendsto_inter_subtype_to_right (S := S) (T := O) hIinf)
  have hcoe : Tendsto (fun n : J ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hJinf bound
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : J)] with n hn
    exact hba.le.trans hn
  have hfJ : (fun n : J ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : J ↦ scale (n : ℕ)) := by
    simpa only [Function.comp_def, toI, toS] using
      hfS.comp_tendsto (htoS.comp htoI)
  have homegaJ : Tendsto (fun n : J ↦ (omega (n : ℕ) : ℝ) /
      Real.log (Real.log ((n : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, toI, toO] using
      homegaO.comp (htoO.comp htoI)
  have hupper : Tendsto (fun n : J ↦
      (f (n : ℕ) : ℝ) / scale (n : ℕ) +
        ((omega (n : ℕ) : ℝ) /
          Real.log (Real.log ((n : ℕ) : ℝ))) / 2 +
        1 / scale (n : ℕ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (hfJ.tendsto_div_nhds_zero.add (homegaJ.div_const 2)).add
      (tendsto_inv_scale_zero.comp hcoe)
  have hloglog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  have hUpperBound : ∀ᶠ n : J in atTop,
      (F (n : ℕ) : ℝ) / scale (n : ℕ) ≤
        (f (n : ℕ) : ℝ) / scale (n : ℕ) +
          ((omega (n : ℕ) : ℝ) /
            Real.log (Real.log ((n : ℕ) : ℝ))) / 2 +
          1 / scale (n : ℕ) := by
    filter_upwards [hcoe.eventually (eventually_gt_atTop (1 : ℕ)),
      (hloglog.comp hcoe).eventually (eventually_gt_atTop (0 : ℝ))]
      with n hn hll
    exact F_div_scale_le hn hll
  refine ⟨J, hJ, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro c hc
    exact htoL.eventually (hLowerL c hc)
  · intro c hc
    filter_upwards [(tendsto_order.1 hupper).2 c hc, hUpperBound]
      with n hn hbound
    exact hbound.trans_lt hn

/-- Closed proof of the FC-like sharp first-question entry. -/
theorem proposed_first_question_sharp :
    erdos_878.variants.proposed_first_question_sharp := by
  rcases exists_density_one_F_div_scale_tendsto_half with ⟨A, hA, hF⟩
  rcases exists_density_one_f_div_scale_littleO_of_source_blocks with
    ⟨S, hS, hfS⟩
  let J : Set ℕ := S ∩ A
  have hJ : J.HasDensity 1 := hasDensity_one_inter_of_hasDensity_one hS hA
  have hJinf : J.Infinite := Nat.infinite_of_hasDensity_pos hJ (by norm_num)
  have htoS : Tendsto (fun n : J ↦ (⟨(n : ℕ), n.property.1⟩ : S)) atTop atTop :=
    tendsto_inter_subtype_to_left hJinf
  have htoA : Tendsto (fun n : J ↦ (⟨(n : ℕ), n.property.2⟩ : A)) atTop atTop :=
    tendsto_inter_subtype_to_right hJinf
  have hfJ : (fun n : J ↦ (f (n : ℕ) : ℝ)) =o[atTop]
      (fun n : J ↦ scale (n : ℕ)) := by
    simpa only [Function.comp_def] using hfS.comp_tendsto htoS
  have hFJ : Tendsto (fun n : J ↦ (F (n : ℕ) : ℝ) / scale (n : ℕ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Function.comp_def] using hF.comp htoA
  exact proposed_first_question_sharp_of_component_inputs J hJ hfJ hFJ

end

end Erdos878

#print axioms Erdos878.eventually_of_eventually_mem_of_eventually_subtype
#print axioms Erdos878.exists_density_one_F_div_scale_eventually_gt_of_lt_half
#print axioms Erdos878.exists_density_one_F_div_scale_tendsto_half
#print axioms Erdos878.proposed_first_question_sharp
