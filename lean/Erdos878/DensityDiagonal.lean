import Erdos878.MultiWindowExceptional

/-!
# A density-one diagonal set

Natural-density-zero sets are not closed under countable unions.  This module proves the precise
pseudointersection statement needed below: from countably many density-zero bad sets, choose one
density-one set which eventually avoids every bad set.
-/

open Classical Filter Finset Topology
open scoped Real

namespace Erdos878

noncomputable section

theorem finiteSetUnion_mono {ι : Type*} [DecidableEq ι]
    {s t : Finset ι} (hst : s ⊆ t) (A : ι → Set ℕ) :
    finiteSetUnion s A ⊆ finiteSetUnion t A := by
  intro n hn
  rcases hn with ⟨i, hi, hni⟩
  exact ⟨i, hst hi, hni⟩

/-- A countable family of density-zero sets has a density-one pseudointersection of their
complements.  Equivalently, one density-one set eventually avoids each member of the family. -/
theorem exists_density_one_eventually_avoids
    (B : ℕ → Set ℕ) (hB : ∀ i, (B i).HasDensity 0) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ i : ℕ, ∀ᶠ n : A in atTop, (n : ℕ) ∉ B i := by
  let C : ℕ → Set ℕ := fun i ↦ finiteSetUnion (Finset.range (i + 1)) B
  have hC : ∀ i, (C i).HasDensity 0 := by
    intro i
    dsimp [C]
    apply finiteSetUnion_hasDensity_zero
    intro j hj
    exact hB j
  have hsmall : ∀ i : ℕ, ∀ᶠ n : ℕ in atTop,
      (C i).partialDensity Set.univ n < 1 / ((i : ℝ) + 1) := by
    intro i
    have hi : 0 < 1 / ((i : ℝ) + 1) := by positivity
    have hCi := hC i
    rw [Set.HasDensity] at hCi
    exact (tendsto_order.1 hCi).2 (1 / ((i : ℝ) + 1)) hi
  have hcutExists : ∀ i : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      (C i).partialDensity Set.univ n < 1 / ((i : ℝ) + 1) := by
    intro i
    exact (eventually_atTop.1 (hsmall i))
  choose cutoff hcutoff using hcutExists
  let M : ℕ → ℕ := fun i ↦ cutoff i + i + 1
  let level : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun i ↦ M i ≤ n) n
  have hMcutoff : ∀ i, cutoff i ≤ M i := by
    intro i
    dsimp [M]
    omega
  have hMindex : ∀ i, i ≤ M i := by
    intro i
    dsimp [M]
    omega
  have hlevel : Tendsto level atTop atTop := by
    apply tendsto_atTop.2
    intro i
    filter_upwards [eventually_ge_atTop (M i)] with n hn
    have hin : i ≤ n := (hMindex i).trans hn
    exact Nat.le_findGreatest hin hn
  let D : Set ℕ := {n | n ∈ C (level n)}
  have hD : D.HasDensity 0 := by
    rw [Set.HasDensity]
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    have hinv : Tendsto (fun n : ℕ ↦ 1 / (((level n : ℕ) : ℝ) + 1))
        atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hlevel
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n ↦ by positivity)
    · filter_upwards [eventually_ge_atTop (M 0), eventually_gt_atTop (0 : ℕ)]
        with n hnM hnpos
      have hlevelSpec : M (level n) ≤ n := by
        dsimp [level]
        exact Nat.findGreatest_spec (P := fun i ↦ M i ≤ n) (m := 0)
          (Nat.zero_le n) hnM
      have hcut : cutoff (level n) ≤ n :=
        (hMcutoff (level n)).trans hlevelSpec
      have hratio := hcutoff (level n) n hcut
      simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
        Nat.ncard_Iio] at hratio
      have hsub : D ∩ Set.Iio n ⊆ C (level n) ∩ Set.Iio n := by
        intro m hm
        have hmD : m ∈ C (level m) := hm.1
        have hlevels : level m ≤ level n := by
          dsimp [level]
          exact Nat.findGreatest_mono
            (P := fun i ↦ M i ≤ m) (Q := fun i ↦ M i ≤ n)
            (fun _ hi ↦ hi.trans hm.2.le) hm.2.le
        have hCsub : C (level m) ⊆ C (level n) := by
          dsimp [C]
          apply finiteSetUnion_mono
          exact Finset.range_mono (Nat.succ_le_succ hlevels)
        exact ⟨hCsub hmD, hm.2⟩
      have hfin : (C (level n) ∩ Set.Iio n).Finite :=
        (Set.finite_Iio n).subset (fun _ hm ↦ hm.2)
      have hcard := Set.ncard_le_ncard hsub hfin
      have hcardR : (((D ∩ Set.Iio n).ncard : ℕ) : ℝ) ≤
          (((C (level n) ∩ Set.Iio n).ncard : ℕ) : ℝ) := by
        exact_mod_cast hcard
      have hdiv := div_le_div_of_nonneg_right hcardR
        (show 0 ≤ (n : ℝ) by positivity)
      exact hdiv.trans hratio.le
    · simpa only [Nat.cast_add, Nat.cast_one] using hinv
  let A : Set ℕ := Dᶜ
  have hA : A.HasDensity 1 := by
    dsimp [A]
    exact compl_hasDensity_one_of_hasDensity_zero hD
  have hAinf : A.Infinite := Nat.infinite_of_hasDensity_pos hA (by norm_num)
  have hcoe : Tendsto (fun n : A ↦ (n : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨a, ha, hba⟩ := Set.Infinite.exists_gt hAinf b
    filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : A)] with n hn
    exact hba.le.trans hn
  refine ⟨A, hA, ?_⟩
  intro i
  filter_upwards [hcoe.eventually (hlevel.eventually (eventually_ge_atTop i))] with n hilevel
  intro hni
  have hiRange : i ∈ Finset.range (level (n : ℕ) + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hilevel)
  have hnC : (n : ℕ) ∈ C (level (n : ℕ)) :=
    ⟨i, hiRange, hni⟩
  exact n.property hnC

end

end Erdos878

#print axioms Erdos878.exists_density_one_eventually_avoids
