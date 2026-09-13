import Erdos878.TrackBFirstDerivativeTest
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max

/-!
# Track B: derivative bands and integer-point counting

Positive curvature separates samples of the first derivative. A narrow band
therefore contains few integer samples, including both possible endpoints.
-/

namespace Erdos878.TrackB
open Finset Set
noncomputable section

theorem sub_bounds_of_hasDerivAt_bounds (h h' : ℝ → ℝ) (a b l v s t : ℝ)
    (hc : ContinuousOn h (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x)
    (hb : ∀ x ∈ Set.Ioo a b, l ≤ h' x ∧ h' x ≤ v)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    l * (t - s) ≤ h t - h s ∧ h t - h s ≤ v * (t - s) := by
  rcases lt_or_eq_of_le hst with hst | rfl
  · have hsub : Set.Ioo s t ⊆ Set.Ioo a b := fun x hx =>
      ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope h h' hst
      (hc.mono (Set.Icc_subset_Icc hs.1 ht.2)) (fun x hx => hd x (hsub hx))
    have heq := (eq_div_iff (sub_ne_zero.mpr hst.ne')).mp he
    have hxbound := hb x (hsub hx)
    constructor
    · simpa only [heq] using mul_le_mul_of_nonneg_right hxbound.1 (sub_nonneg.mpr hst.le)
    · simpa only [heq] using mul_le_mul_of_nonneg_right hxbound.2 (sub_nonneg.mpr hst.le)
  · simp

/-- A finite set of natural numbers has at most diameter plus one points. -/
theorem card_nat_le_real_diameter (S : Finset ℕ) (hS : S.Nonempty) :
    (S.card : ℝ) ≤ (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
  have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := fun k hk =>
    Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hminmax := S.min'_le_max' hS
  have hcast : ((S.max' hS + 1 - S.min' hS : ℕ) : ℝ) =
      (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  exact (Nat.cast_le.mpr hcard).trans_eq hcast

/-- Uniform count in a derivative band; does not assume the sampled subset is an interval. -/
theorem card_le_of_separated_band (S : Finset ℕ) (d : ℕ → ℝ) (l A B : ℝ)
    (hl : 0 < l) (hAB : A ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → l * ((j : ℝ) - i) ≤ d j - d i)
    (hband : ∀ i ∈ S, A ≤ d i ∧ d i ≤ B) :
    (S.card : ℝ) ≤ (B - A) / l + 1 := by
  obtain hS | hS := S.eq_empty_or_nonempty
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hs := hsep _ (S.min'_mem hS) _ (S.max'_mem hS) (S.min'_le_max' hS)
    have ha := (hband _ (S.min'_mem hS)).1
    have hb := (hband _ (S.max'_mem hS)).2
    have hwidth : (S.max' hS : ℝ) - (S.min' hS : ℝ) ≤ (B - A) / l := by
      apply (le_div_iff₀ hl).mpr
      nlinarith
    linarith [card_nat_le_real_diameter S hS]

theorem card_int_le_real_diameter (S : Finset ℤ) (hS : S.Nonempty) :
    (S.card : ℝ) ≤ (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
  have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := fun k hk =>
    Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hminmax := S.min'_le_max' hS
  have hcast : (((S.max' hS + 1 - S.min' hS).toNat : ℕ) : ℝ) =
      (S.max' hS : ℝ) - (S.min' hS : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  exact (Nat.cast_le.mpr hcard).trans_eq hcast

/-- Floor labels of any finite sample set occupy at most value-range plus two labels. -/
theorem card_image_floor_le (S : Finset ℕ) (d : ℕ → ℝ) (δ A B : ℝ)
    (hAB : A ≤ B) (hd : ∀ i ∈ S, A ≤ d i ∧ d i ≤ B) :
    ((S.image (fun i => ⌊d i + δ⌋)).card : ℝ) ≤ B - A + 2 := by
  let K := S.image (fun i => ⌊d i + δ⌋)
  obtain hK | hK := K.eq_empty_or_nonempty
  · change (K.card : ℝ) ≤ _
    rw [hK, Finset.card_empty, Nat.cast_zero]
    linarith
  · obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp (K.min'_mem hK)
    obtain ⟨j, hj, hej⟩ := Finset.mem_image.mp (K.max'_mem hK)
    have hlo := Int.lt_floor_add_one (d i + δ)
    have hhi := Int.floor_le (d j + δ)
    rw [hei] at hlo
    rw [hej] at hhi
    have hwidth : (K.max' hK : ℝ) - (K.min' hK : ℝ) + 1 ≤ B - A + 2 := by
      linarith [(hd i hi).1, (hd j hj).2]
    exact (card_int_le_real_diameter K hK).trans hwidth

end
end Erdos878.TrackB
