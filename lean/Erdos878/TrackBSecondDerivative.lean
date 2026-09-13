import Erdos878.TrackBDerivativePartition

/-!
# Track B: a finite second-derivative exponential-sum test

The near/far decomposition is constructed from floor labels of derivative samples.
Every sample occurs exactly once, and the far fibers are genuine intervals.
The explicit derivatives in the hypotheses are linked by `HasDerivAt`.
-/

namespace Erdos878.TrackB
open Finset Set
noncomputable section

theorem norm_sum_phaseCharacter_le_card (S : Finset ℕ) (u : ℕ → ℝ) :
    ‖∑ k ∈ S, phaseCharacter (u k)‖ ≤ (S.card : ℝ) := by
  simpa only [norm_phaseCharacter, Finset.sum_const, nsmul_eq_mul, mul_one] using
    norm_sum_le S (fun k => phaseCharacter (u k))

/-- Combine the near-integer count and first-derivative cancellation over all labels. -/
theorem norm_sum_le_of_derivative_separation (f h : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (δ l A B : ℝ) (hδ : 0 < δ) (hl : 0 < l) (hAB : A ≤ B)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hm : MonotoneOn h (Set.Icc a (a + N)))
    (hsep : ∀ i ≤ N, ∀ j ≤ N, i ≤ j →
      l * ((j : ℝ) - i) ≤ h (a + j) - h (a + i))
    (hband : ∀ k ≤ N, A ≤ h (a + k) ∧ h (a + k) ≤ B) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤
      (B - A + 2) * (2 * δ / l + 2 + 1 / δ) := by
  let d : ℕ → ℝ := fun k => h (a + k)
  let K := (Finset.range (N + 1)).image (fun k => ⌊d k + δ⌋)
  have hcount : (K.card : ℝ) ≤ B - A + 2 :=
    card_image_floor_le (Finset.range (N + 1)) d δ A B hAB
      (fun k hk => hband k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hfiber (z : ℤ) :
      ‖(∑ k ∈ derivativeNear d N δ z, phaseCharacter (f (a + k))) +
        (∑ k ∈ derivativeFar d N δ z, phaseCharacter (f (a + k)))‖ ≤
        2 * δ / l + 2 + 1 / δ := by
    have hn := (norm_sum_phaseCharacter_le_card (derivativeNear d N δ z)
      (fun k => f (a + k))).trans (card_derivativeNear_le d N δ l z hδ.le hl hsep)
    have hf := norm_sum_derivativeFar_le f h a N δ z hδ hc hd hm
    exact (norm_add_le _ _).trans (by linarith)
  rw [sum_eq_derivative_near_add_far d N δ]
  calc
    _ ≤ ∑ z ∈ K, ‖(∑ k ∈ derivativeNear d N δ z, phaseCharacter (f (a + k))) +
        (∑ k ∈ derivativeFar d N δ z, phaseCharacter (f (a + k)))‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ K, (2 * δ / l + 2 + 1 / δ) := Finset.sum_le_sum (fun z _ => hfiber z)
    _ = (K.card : ℝ) * (2 * δ / l + 2 + 1 / δ) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (by positivity)

/-- A second-derivative estimate with a free decomposition width `δ`. -/
theorem second_derivative_test_parameterized (f h h' : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (δ l v : ℝ) (hδ : 0 < δ) (hl : 0 < l)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hhc : ContinuousOn h (Set.Icc a (a + N)))
    (hhd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt h (h' x) x)
    (hcurv : ∀ x ∈ Set.Ioo a (a + N), l ≤ h' x ∧ h' x ≤ v) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤
      (v * N + 2) * (2 * δ / l + 2 + 1 / δ) := by
  have hab : a ≤ a + (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsamp (k : ℕ) (hk : k ≤ N) : a + (k : ℝ) ∈ Set.Icc a (a + N) :=
    ⟨by linarith [Nat.cast_nonneg (α := ℝ) k], by linarith [show (k : ℝ) ≤ N by exact_mod_cast hk]⟩
  have hmono : MonotoneOn h (Set.Icc a (a + N)) := by
    intro s hs t ht hst
    have hb := (sub_bounds_of_hasDerivAt_bounds h h' a (a + N) l v s t hhc hhd hcurv hs ht hst).1
    have hh := mul_nonneg hl.le (sub_nonneg.mpr hst)
    linarith
  have hbound := norm_sum_le_of_derivative_separation f h a N δ l (h a) (h (a + N)) hδ hl
    (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab) hc hd hmono
    (fun i hi j hj hij => by
      have hb := (sub_bounds_of_hasDerivAt_bounds h h' a (a + N) l v (a + i) (a + j)
        hhc hhd hcurv (hsamp i hi) (hsamp j hj) (by linarith [show (i : ℝ) ≤ j by exact_mod_cast hij])).1
      simpa only [add_sub_add_left_eq_sub] using hb)
    (fun k hk => ⟨hmono ⟨le_rfl, hab⟩ (hsamp k hk) (hsamp k hk).1,
      hmono (hsamp k hk) ⟨hab, le_rfl⟩ (hsamp k hk).2⟩)
  have hspan := (sub_bounds_of_hasDerivAt_bounds h h' a (a + N) l v a (a + N)
    hhc hhd hcurv ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab).2
  rw [add_sub_cancel_left] at hspan
  exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- Optimize the width without asymptotic notation; the constant is uniform. -/
theorem second_derivative_parameter_bound (l A n : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hA : 0 ≤ A) (hn : 0 ≤ n) :
    (A * l * n + 2) * (2 * Real.sqrt l / l + 2 + 1 / Real.sqrt l) ≤
      10 * (A * n * Real.sqrt l + 1 / Real.sqrt l) := by
  let r := Real.sqrt l
  have hr : 0 < r := Real.sqrt_pos.mpr hl
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hl1
  have hrsq : r ^ 2 = l := Real.sq_sqrt hl.le
  have hlr : l ≤ r := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hlr (mul_nonneg hA hn)
  have hinv : 1 ≤ 1 / r := (le_div_iff₀ hr).mpr (by linarith)
  have he : (A * l * n + 2) * (2 * r / l + 2 + 1 / r) =
      3 * A * n * r + 2 * A * n * l + 6 / r + 4 := by
    rw [← hrsq]
    field_simp
    ring
  change (A * l * n + 2) * (2 * r / l + 2 + 1 / r) ≤ 10 * (A * n * r + 1 / r)
  rw [he]
  have hpos := mul_nonneg (mul_nonneg hA hn) hr.le
  simp only [div_eq_mul_inv, one_mul] at hinv ⊢
  nlinarith only [hscale, hinv, hpos]

/-- Positive small curvature: a genuine finite van der Corput second-derivative test.
The right-hand side has no parameter-dependent hidden constant. -/
theorem second_derivative_test_small (f h h' : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (l A : ℝ) (hl : 0 < l) (hl1 : l ≤ 1) (hA : 0 ≤ A)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (h x) x)
    (hhc : ContinuousOn h (Set.Icc a (a + N)))
    (hhd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt h (h' x) x)
    (hcurv : ∀ x ∈ Set.Ioo a (a + N), l ≤ h' x ∧ h' x ≤ A * l) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤
      10 * (A * N * Real.sqrt l + 1 / Real.sqrt l) := by
  exact (second_derivative_test_parameterized f h h' a N (Real.sqrt l) l (A * l)
    (Real.sqrt_pos.mpr hl) hl hc hd hhc hhd hcurv).trans
      (second_derivative_parameter_bound l A N hl hl1 hA (Nat.cast_nonneg N))

/-- An entry point stated with actual iterated derivatives. The endpoint
differentiability assumptions are convenient for smooth reciprocal-log phases. -/
theorem second_derivative_test_small_of_deriv (f : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (l A : ℝ) (hl : 0 < l) (hl1 : l ≤ 1) (hA : 0 ≤ A)
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (deriv f x) x)
    (hdd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt (deriv f) (deriv (deriv f) x) x)
    (hcurv : ∀ x ∈ Set.Icc a (a + N),
      l ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ A * l) :
    ‖∑ k ∈ Finset.range (N + 1), phaseCharacter (f (a + k))‖ ≤
      10 * (A * N * Real.sqrt l + 1 / Real.sqrt l) := by
  exact second_derivative_test_small f (deriv f) (deriv (deriv f)) a N l A hl hl1 hA
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => (hdd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hdd x (Set.Ioo_subset_Icc_self hx))
    (fun x hx => hcurv x (Set.Ioo_subset_Icc_self hx))

end
end Erdos878.TrackB
