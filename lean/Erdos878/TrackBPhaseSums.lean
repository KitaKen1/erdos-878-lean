import Erdos878.TrackBSecondDerivative
import Erdos878.TrackBExponentialPhase

/-!
# Track B: apply the second-derivative test to reciprocal-log phases

The finite theorem is instantiated on closed integer intervals. The curvature
scale and comparison constants are the ones proved in `TrackBCurvature`.
-/

namespace Erdos878.TrackB
open Finset Set
noncomputable section

theorem sum_Icc_eq_sum_range_shift {R : Type*} [AddCommMonoid R]
    (u : ℕ → R) (A B : ℕ) (hAB : A ≤ B) :
    (∑ k ∈ Finset.Icc A B, u k) = ∑ k ∈ Finset.range (B - A + 1), u (A + k) := by
  calc
    _ = ∑ k ∈ Finset.Ico A (B + 1), u k := by
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      · intro k hk
        rfl
    _ = ∑ k ∈ Finset.range (B + 1 - A), u (A + k) :=
      Finset.sum_Ico_eq_sum_range u A (B + 1)
    _ = _ := by rw [show B + 1 - A = B - A + 1 by omega]

/-- Type-I inner phase on an arbitrary closed integer interval inside a dyadic box. -/
theorem norm_sum_reciprocalLogPhase_Icc_le
    (a n L M : ℝ) (A B : ℕ) (ha : 0 < a) (hn : 0 < n)
    (hL : 1 ≤ L) (hM : 0 < M) (hAB : A ≤ B)
    (hlam : a / (16 * M ^ 2 * L ^ 2) ≤ 1)
    (hbox : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ), M ≤ x ∧ x ≤ 2 * M)
    (hlog : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
      L ≤ Real.log (n * x) ∧ Real.log (n * x) ≤ 2 * L) :
    ‖∑ k ∈ Finset.Icc A B, phaseCharacter (reciprocalLogPhase a n k)‖ ≤
      10 * (48 * (B - A : ℕ) * Real.sqrt (a / (16 * M ^ 2 * L ^ 2)) +
        1 / Real.sqrt (a / (16 * M ^ 2 * L ^ 2))) := by
  let lam := a / (16 * M ^ 2 * L ^ 2)
  have hlampos : 0 < lam := by dsimp [lam]; positivity
  have hend : (A : ℝ) + (B - A : ℕ) = B := by
    rw [Nat.cast_sub hAB]
    ring
  have hmem {x : ℝ} (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      x ∈ Set.Icc (A : ℝ) (B : ℝ) := by rwa [hend] at hx
  have hfirst (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      HasDerivAt (reciprocalLogPhase a n) (reciprocalLogSlope a n x) x := by
    have hm := (hbox x (hmem hx)).1
    have hxp : 0 < x := hM.trans_le hm
    have hl := (hlog x (hmem hx)).1
    have hp : 1 < n * x :=
      (Real.log_pos_iff (mul_nonneg hn.le hxp.le)).mp
        ((lt_of_lt_of_le zero_lt_one hL).trans_le hl)
    exact hasDerivAt_reciprocalLogPhase a n x hn hxp hp
  have hsecond (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      HasDerivAt (reciprocalLogSlope a n)
        (a / x ^ 2 * logCurvature (Real.log (n * x))) x := by
    have hm := (hbox x (hmem hx)).1
    have hxp : 0 < x := hM.trans_le hm
    have hl := (hlog x (hmem hx)).1
    have hp : 1 < n * x :=
      (Real.log_pos_iff (mul_nonneg hn.le hxp.le)).mp
        ((lt_of_lt_of_le zero_lt_one hL).trans_le hl)
    exact hasDerivAt_reciprocalLogSlope a n x hn hxp hp
  have hcurv (x : ℝ) (hx : x ∈ Set.Ioo (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      lam ≤ a / x ^ 2 * logCurvature (Real.log (n * x)) ∧
        a / x ^ 2 * logCurvature (Real.log (n * x)) ≤ 48 * lam := by
    have hm := hbox x (hmem (Set.Ioo_subset_Icc_self hx))
    have hlg := hlog x (hmem (Set.Ioo_subset_Icc_self hx))
    have hb := deriv2_reciprocalLogPhase_bounds a n L M x ha.le hn hL hM
      hm.1 hm.2 hlg.1 hlg.2
    have hxp := hM.trans_le hm.1
    have hp : 1 < n * x :=
      (Real.log_pos_iff (mul_nonneg hn.le hxp.le)).mp
        ((lt_of_lt_of_le zero_lt_one hL).trans_le hlg.1)
    rw [deriv2_reciprocalLogPhase a n x hn hxp hp] at hb
    dsimp [lam]
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    ring
  have ht := second_derivative_test_small (reciprocalLogPhase a n)
    (reciprocalLogSlope a n)
    (fun x => a / x ^ 2 * logCurvature (Real.log (n * x))) (A : ℝ) (B - A)
    lam 48 hlampos hlam (by norm_num)
    (fun x hx => (hfirst x hx).continuousAt.continuousWithinAt)
    (fun x hx => hfirst x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => (hsecond x hx).continuousAt.continuousWithinAt)
    (fun x hx => hsecond x (Set.Ioo_subset_Icc_self hx)) hcurv
  rw [sum_Icc_eq_sum_range_shift _ A B hAB]
  simpa only [Nat.cast_add] using ht

/-- Type-II difference phase on a closed interval. The comparison constant is `256`. -/
theorem norm_sum_reciprocalLogCorrelation_Icc_le
    (a L M N n₁ n₂ : ℝ) (A B : ℕ)
    (ha : 0 < a) (hL : 1 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hnlo : N ≤ n₁) (hnord : n₁ < n₂) (hnhi : n₂ ≤ 2 * N) (hAB : A ≤ B)
    (hlam : a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3) ≤ 1)
    (hbox : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ), M ≤ x ∧ x ≤ 2 * M)
    (hlog : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
      L ≤ Real.log (n₁ * x) ∧ Real.log (n₂ * x) ≤ 2 * L) :
    ‖∑ k ∈ Finset.Icc A B,
        phaseCharacter (reciprocalLogCorrelation a n₁ n₂ k)‖ ≤
      10 * (256 * (B - A : ℕ) *
          Real.sqrt (a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3)) +
        1 / Real.sqrt (a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3))) := by
  let lam := a * (n₂ - n₁) / (32 * N * M ^ 2 * L ^ 3)
  have hn₁ : 0 < n₁ := hN.trans_le hnlo
  have hn₂ : 0 < n₂ := hn₁.trans hnord
  have hlampos : 0 < lam := by dsimp [lam]; positivity
  have hend : (A : ℝ) + (B - A : ℕ) = B := by
    rw [Nat.cast_sub hAB]
    ring
  have hmem {x : ℝ} (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      x ∈ Set.Icc (A : ℝ) (B : ℝ) := by rwa [hend] at hx
  let slope : ℝ → ℝ := fun x => reciprocalLogSlope a n₁ x - reciprocalLogSlope a n₂ x
  let curve : ℝ → ℝ := fun x => a / x ^ 2 *
    (logCurvature (Real.log (n₁ * x)) - logCurvature (Real.log (n₂ * x)))
  have hdomain (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      0 < x ∧ 1 < n₁ * x ∧ 1 < n₂ * x := by
    have hm := (hbox x (hmem hx)).1
    have hxp : 0 < x := hM.trans_le hm
    have hl := (hlog x (hmem hx)).1
    have hp₁ : 1 < n₁ * x :=
      (Real.log_pos_iff (mul_nonneg hn₁.le hxp.le)).mp
        ((lt_of_lt_of_le zero_lt_one hL).trans_le hl)
    exact ⟨hxp, hp₁, hp₁.trans_le (mul_le_mul_of_nonneg_right hnord.le hxp.le)⟩
  have hfirst (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      HasDerivAt (reciprocalLogCorrelation a n₁ n₂) (slope x) x := by
    have hd := hdomain x hx
    exact (hasDerivAt_reciprocalLogPhase a n₁ x hn₁ hd.1 hd.2.1).sub
      (hasDerivAt_reciprocalLogPhase a n₂ x hn₂ hd.1 hd.2.2)
  have hsecond (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      HasDerivAt slope (curve x) x := by
    have hd := hdomain x hx
    convert (hasDerivAt_reciprocalLogSlope a n₁ x hn₁ hd.1 hd.2.1).sub
      (hasDerivAt_reciprocalLogSlope a n₂ x hn₂ hd.1 hd.2.2) using 1 <;>
      first | rfl | (dsimp [slope, curve]; ring)
  have hcurv (x : ℝ) (hx : x ∈ Set.Ioo (A : ℝ) ((A : ℝ) + (B - A : ℕ))) :
      lam ≤ curve x ∧ curve x ≤ 256 * lam := by
    have hm := hbox x (hmem (Set.Ioo_subset_Icc_self hx))
    have hlg := hlog x (hmem (Set.Ioo_subset_Icc_self hx))
    have hb := deriv2_reciprocalLogCorrelation_bounds a L M N n₁ n₂ x ha.le hL hM hN
      hm.1 hm.2 hnlo hnord.le hnhi hlg.1 hlg.2
    have hd := hdomain x (Set.Ioo_subset_Icc_self hx)
    rw [deriv2_reciprocalLogCorrelation a n₁ n₂ x hn₁ hn₂ hd.1 hd.2.1 hd.2.2] at hb
    dsimp [lam, curve]
    refine ⟨hb.1, hb.2.trans_eq ?_⟩
    ring
  have ht := second_derivative_test_small (reciprocalLogCorrelation a n₁ n₂)
    slope curve (A : ℝ) (B - A) lam 256 hlampos hlam (by norm_num)
    (fun x hx => (hfirst x hx).continuousAt.continuousWithinAt)
    (fun x hx => hfirst x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => (hsecond x hx).continuousAt.continuousWithinAt)
    (fun x hx => hsecond x (Set.Ioo_subset_Icc_self hx)) hcurv
  rw [sum_Icc_eq_sum_range_shift _ A B hAB]
  simpa only [Nat.cast_add] using ht

end
end Erdos878.TrackB
