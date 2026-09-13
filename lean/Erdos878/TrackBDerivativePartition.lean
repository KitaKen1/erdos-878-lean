import Erdos878.TrackBDerivativeGeometry

/-!
# Track B: disjoint floor-label decomposition of derivative samples

The classification is made at integer samples. Monotonicity fills the real hull
of each far-from-integer band, so no inverse function or chosen crossing points
are needed. Strict upper endpoints ensure that no sample is counted twice.
-/

namespace Erdos878.TrackB
open Finset Set
noncomputable section

def derivativeNear (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => ⌊d k + δ⌋ = z ∧ d k < (z : ℝ) + δ)

def derivativeFar (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => ⌊d k + δ⌋ = z ∧ (z : ℝ) + δ ≤ d k)

theorem derivativeNear_bounds (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ)
    {k : ℕ} (hk : k ∈ derivativeNear d N δ z) :
    k ≤ N ∧ (z : ℝ) - δ ≤ d k ∧ d k < (z : ℝ) + δ := by
  obtain ⟨hk, he, hlt⟩ := Finset.mem_filter.mp hk
  have hfloor := Int.floor_le (d k + δ)
  rw [he] at hfloor
  exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), by linarith, hlt⟩

theorem derivativeFar_eq_band (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (z : ℤ) (hδ : 0 ≤ δ) :
    derivativeFar d N δ z = (Finset.range (N + 1)).filter
      (fun k => (z : ℝ) + δ ≤ d k ∧ d k < (z : ℝ) + 1 - δ) := by
  ext k
  simp only [derivativeFar, Finset.mem_filter]
  constructor
  · rintro ⟨hk, he, hlo⟩
    have hfloor := Int.lt_floor_add_one (d k + δ)
    rw [he] at hfloor
    exact ⟨hk, hlo, by linarith⟩
  · rintro ⟨hk, hlo, hhi⟩
    refine ⟨hk, Int.floor_eq_iff.mpr ⟨?_, ?_⟩, hlo⟩ <;> linarith

/-- A nonempty level band of a monotone sequence is exactly one integer interval. -/
theorem monotone_band_eq_Icc (d : ℕ → ℝ) (N : ℕ) (A B : ℝ)
    (hm : MonotoneOn d (Set.Icc 0 N))
    (hne : ((Finset.range (N + 1)).filter (fun k => A ≤ d k ∧ d k < B)).Nonempty) :
    let S := (Finset.range (N + 1)).filter (fun k => A ≤ d k ∧ d k < B)
    S = Finset.Icc (S.min' hne) (S.max' hne) := by
  let S := (Finset.range (N + 1)).filter (fun k => A ≤ d k ∧ d k < B)
  change S = _
  have hmin := Finset.mem_filter.mp (S.min'_mem hne)
  have hmax := Finset.mem_filter.mp (S.max'_mem hne)
  have hlo : S.min' hne ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmin.1)
  have hhi : S.max' hne ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmax.1)
  ext k
  constructor
  · intro hk
    exact Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
  · intro hk
    obtain ⟨hkl, hkr⟩ := Finset.mem_Icc.mp hk
    have hkN := hkr.trans hhi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hkN), ?_, ?_⟩
    · exact hmin.2.1.trans (hm ⟨Nat.zero_le _, hlo⟩ ⟨Nat.zero_le _, hkN⟩ hkl)
    · exact (hm ⟨Nat.zero_le _, hkN⟩ ⟨Nat.zero_le _, hhi⟩ hkr).trans_lt hmax.2.2

theorem sum_eq_derivative_near_add_far (d : ℕ → ℝ) (N : ℕ) (δ : ℝ) (w : ℕ → ℂ) :
    (∑ k ∈ Finset.range (N + 1), w k) =
      ∑ z ∈ (Finset.range (N + 1)).image (fun k => ⌊d k + δ⌋),
        ((∑ k ∈ derivativeNear d N δ z, w k) + (∑ k ∈ derivativeFar d N δ z, w k)) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun k hk =>
    Finset.mem_image_of_mem (fun k => ⌊d k + δ⌋) hk) w]
  apply Finset.sum_congr rfl
  intro z hz
  have h := Finset.sum_filter_add_sum_filter_not
    ((Finset.range (N + 1)).filter (fun k => ⌊d k + δ⌋ = z))
    (fun k => d k < (z : ℝ) + δ) w
  simpa only [Finset.filter_filter, not_lt, derivativeNear, derivativeFar] using h.symm

theorem card_derivativeNear_le (d : ℕ → ℝ) (N : ℕ) (δ l : ℝ) (z : ℤ)
    (hδ : 0 ≤ δ) (hl : 0 < l)
    (hsep : ∀ i ≤ N, ∀ j ≤ N, i ≤ j → l * ((j : ℝ) - i) ≤ d j - d i) :
    ((derivativeNear d N δ z).card : ℝ) ≤ 2 * δ / l + 1 := by
  have h := card_le_of_separated_band (derivativeNear d N δ z) d l
    ((z : ℝ) - δ) ((z : ℝ) + δ) hl (by linarith)
    (fun i hi j hj hij => hsep i (derivativeNear_bounds d N δ z hi).1
      j (derivativeNear_bounds d N δ z hj).1 hij)
    (fun i hi => ⟨(derivativeNear_bounds d N δ z hi).2.1,
      (derivativeNear_bounds d N δ z hi).2.2.le⟩)
  convert h using 1
  ring

/-- First-derivative cancellation on a sampled far band, including its real hull. -/
theorem norm_sum_derivativeFar_le (f h : ℝ → ℝ) (a : ℝ) (N : ℕ) (δ : ℝ) (z : ℤ)
    (hδ : 0 < δ) (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hm : MonotoneOn h (Set.Icc a (a + N))) :
    ‖∑ k ∈ derivativeFar (fun k => h (a + k)) N δ z, phaseCharacter (f (a + k))‖ ≤
      1 + 1 / δ := by
  rw [derivativeFar_eq_band _ _ _ _ hδ.le]
  let S := (Finset.range (N + 1)).filter
    (fun k : ℕ => (z : ℝ) + δ ≤ h (a + k) ∧ h (a + k) < (z : ℝ) + 1 - δ)
  change ‖∑ k ∈ S, _‖ ≤ _
  obtain hS | hS := S.eq_empty_or_nonempty
  · rw [hS, Finset.sum_empty, norm_zero]
    positivity
  · have hsamp (k : ℕ) (hk : k ≤ N) : a + (k : ℝ) ∈ Set.Icc a (a + N) :=
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) k], by linarith [show (k : ℝ) ≤ N by exact_mod_cast hk]⟩
    have hmono : MonotoneOn (fun k : ℕ => h (a + k)) (Set.Icc 0 N) := by
      intro i hi j hj hij
      exact hm (hsamp i hi.2) (hsamp j hj.2) (by linarith [show (i : ℝ) ≤ j by exact_mod_cast hij])
    have he := monotone_band_eq_Icc (fun k => h (a + k)) N ((z : ℝ) + δ)
      ((z : ℝ) + 1 - δ) hmono hS
    let L := S.min' hS
    let R := S.max' hS
    have hL := Finset.mem_filter.mp (S.min'_mem hS)
    have hR := Finset.mem_filter.mp (S.max'_mem hS)
    have hLN : L ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hL.1)
    have hRN : R ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hR.1)
    have hLR : L ≤ R := S.min'_le_max' hS
    have hright : a + (L : ℝ) + ((R - L : ℕ) : ℝ) = a + R := by
      rw [Nat.cast_sub hLR]
      ring
    have hsub : Set.Icc (a + L) (a + L + (R - L : ℕ)) ⊆ Set.Icc a (a + N) := by
      rw [hright]
      exact Set.Icc_subset_Icc (hsamp L hLN).1 (hsamp R hRN).2
    have hsubopen : Set.Ioo (a + L) (a + L + (R - L : ℕ)) ⊆ Set.Ioo a (a + N) := by
      rw [hright]
      exact fun x hx => ⟨(hsamp L hLN).1.trans_lt hx.1, hx.2.trans_le (hsamp R hRN).2⟩
    have hbound := norm_sum_phaseCharacter_le_of_monotone_deriv_strip f h (a + L) (R - L) δ z
      hδ (hc.mono hsub) (fun x hx => hd x (hsubopen hx))
      (fun x hx y hy hxy => hm (hsub (Set.Ioo_subset_Icc_self hx))
        (hsub (Set.Ioo_subset_Icc_self hy)) hxy)
      (fun x hx => hL.2.1.trans (hm (hsamp L hLN)
        (hsub (Set.Ioo_subset_Icc_self hx)) hx.1.le))
      (fun x hx => by
        have hxR : x ≤ a + R := hx.2.le.trans_eq hright
        exact ((hm (hsub (Set.Ioo_subset_Icc_self hx)) (hsamp R hRN) hxR).trans_lt hR.2.2).le)
    have hI : Finset.Icc L R = Finset.Ico L (R + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    change S = Finset.Icc L R at he
    rw [he, hI, Finset.sum_Ico_eq_sum_range]
    have hlen : R + 1 - L = R - L + 1 := by omega
    simpa only [hlen, Nat.cast_add, add_assoc] using hbound

end
end Erdos878.TrackB
