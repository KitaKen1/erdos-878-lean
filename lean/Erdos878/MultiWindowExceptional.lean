import Erdos878.MultiWindowAnalytic

/-!
# One exceptional set for a finite multi-window family

Each report-window pair already has a density-zero dyadic exceptional set containing both its
bad-pair multiples and its low-divisor-count integers.  This file takes their genuine finite
union.  No countable-union closure of natural density is used.
-/

open Classical Filter Finset Topology Asymptotics
open scoped Real

namespace Erdos878

noncomputable section

def finiteSetUnion {ι : Type*} (s : Finset ι) (A : ι → Set ℕ) : Set ℕ :=
  {n | ∃ i ∈ s, n ∈ A i}

@[simp] theorem finiteSetUnion_empty {ι : Type*} (A : ι → Set ℕ) :
    finiteSetUnion ∅ A = ∅ := by
  ext n
  simp [finiteSetUnion]

theorem finiteSetUnion_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (A : ι → Set ℕ) :
    finiteSetUnion (insert a s) A = A a ∪ finiteSetUnion s A := by
  ext n
  simp only [finiteSetUnion, mem_insert, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hn⟩
    rcases hi with rfl | hi
    · exact Or.inl hn
    · exact Or.inr ⟨i, hi, hn⟩
  · rintro (hn | ⟨i, hi, hn⟩)
    · exact ⟨a, Or.inl rfl, hn⟩
    · exact ⟨i, Or.inr hi, hn⟩

theorem finiteSetUnion_hasDensity_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Set ℕ)
    (hA : ∀ i ∈ s, (A i).HasDensity 0) :
    (finiteSetUnion s A).HasDensity 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [finiteSetUnion_insert]
      exact hasDensity_zero_union (hA a (by simp))
        (ih (fun i hi ↦ hA i (by simp [hi])))

def multiWindowExceptionalSet (k : ℕ) (rho epsilon : ℝ) : Set ℕ :=
  finiteSetUnion (Finset.univ : Finset (Fin k)) (fun i ↦
    dyadicTrackAExceptionalSetAdjustable
      (multiWindowAlpha k i) (multiWindowBeta k i)
      (multiWindowGamma k i) (multiWindowDelta k i) rho epsilon)

/-- All bad-pair and low-count failures for a fixed finite multi-window family form one
density-zero set. -/
theorem multiWindowExceptionalSet_hasDensity_zero
    (k : ℕ) {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    (multiWindowExceptionalSet k rho epsilon).HasDensity 0 := by
  apply finiteSetUnion_hasDensity_zero
  intro i _
  rcases multiWindow_report_parameter_conditions i with
    ⟨hα, hαβ, hβ, hβγ, hγδ, hδ0, hδ1, hβδ⟩
  have hmasses := all_multiWindow_endpointMass_tendsto_atTop k
  exact dyadicTrackAExceptionalSetAdjustable_hasDensity_zero_of_mass
    hα hβ hβγ hδ0 hδ1 hβδ hrho hepsilon
    (hmasses.1 i) (hmasses.2 i)

theorem not_mem_single_exception_of_not_mem_multiWindowExceptionalSet
    {k : ℕ} {rho epsilon : ℝ} {n : ℕ}
    (hn : n ∉ multiWindowExceptionalSet k rho epsilon) (i : Fin k) :
    n ∉ dyadicTrackAExceptionalSetAdjustable
      (multiWindowAlpha k i) (multiWindowBeta k i)
      (multiWindowGamma k i) (multiWindowDelta k i) rho epsilon := by
  intro hi
  apply hn
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- The complement is the single density-one set used for every window at fixed parameters. -/
theorem multiWindowExceptionalSet_compl_hasDensity_one
    (k : ℕ) {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    (multiWindowExceptionalSet k rho epsilon)ᶜ.HasDensity 1 :=
  compl_hasDensity_one_of_hasDensity_zero
    (multiWindowExceptionalSet_hasDensity_zero k hrho hepsilon)

end

end Erdos878

#print axioms Erdos878.finiteSetUnion_hasDensity_zero
#print axioms Erdos878.multiWindowExceptionalSet_hasDensity_zero
