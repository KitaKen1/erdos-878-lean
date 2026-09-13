import Erdos878.TrackBFirstDerivative

/-!
# Track B: the finite Kusmin--Landau estimate

Monotone increments in `[δ, 1-δ]` give a bound independent of the number of terms.
One extra phase value is used at the right endpoint; a separate theorem removes it.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

/-- Summation by parts in the form adapted to reciprocal phase increments. -/
theorem sum_range_mul_sub_identity (c z : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ range (N + 1), c k * (z k - z (k + 1))) =
      c 0 * z 0 - c N * z (N + 1) +
        ∑ k ∈ range N, (c (k + 1) - c k) * z (k + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

theorem norm_phaseResolvent_sub (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    ‖phaseResolvent t - phaseResolvent s‖ = halfCotPhase s - halfCotPhase t := by
  rw [phaseResolvent_eq t (hs.trans_le hst) ht,
    phaseResolvent_eq s hs (hst.trans_lt ht)]
  have he : (1 / 2 : ℂ) + (halfCotPhase t : ℂ) * Complex.I -
      ((1 / 2 : ℂ) + (halfCotPhase s : ℂ) * Complex.I) =
      ((halfCotPhase t - halfCotPhase s : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (halfCotPhase_antitone s t hs hst ht))]
  ring

/-- The total variation is an endpoint difference, not a length-dependent bound. -/
theorem sum_norm_phaseResolvent_sub (d : ℕ → ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < d k) (hlt : ∀ k ≤ N, d k < 1)
    (hmono : MonotoneOn d (Set.Icc 0 N)) :
    (∑ k ∈ range N, ‖phaseResolvent (d (k + 1)) - phaseResolvent (d k)‖) =
      halfCotPhase (d 0) - halfCotPhase (d N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih (fun k hk => hpos k (by omega))
      (fun k hk => hlt k (by omega))
      (fun i hi j hj hij => hmono ⟨hi.1, Nat.le_succ_of_le hi.2⟩
        ⟨hj.1, Nat.le_succ_of_le hj.2⟩ hij)]
    rw [norm_phaseResolvent_sub (d N) (d (N + 1)) (hpos N (by omega))
      (hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)) (hlt _ le_rfl)]
    ring

theorem phaseCharacter_eq_resolvent_mul_sub (s t : ℝ)
    (hpos : 0 < t - s) (hlt : t - s < 1) :
    phaseCharacter s = phaseResolvent (t - s) * (phaseCharacter s - phaseCharacter t) := by
  have hstep : phaseCharacter t = phaseCharacter s * phaseCharacter (t - s) := by
    rw [← phaseCharacter_add]
    congr 1
    ring
  rw [hstep, phaseResolvent, ← mul_one_sub]
  rw [mul_left_comm, inv_mul_cancel₀ (one_sub_phaseCharacter_ne_zero _ hpos hlt), mul_one]

/-- Discrete first-derivative cancellation. All increment assumptions are local
to the finite interval; no global monotonicity or asymptotic assumption is used. -/
theorem norm_sum_phaseCharacter_le_of_monotone_increments
    (u : ℕ → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hlo : ∀ k ≤ N, δ ≤ u (k + 1) - u k)
    (hhi : ∀ k ≤ N, u (k + 1) - u k ≤ 1 - δ)
    (hmono : MonotoneOn (fun k => u (k + 1) - u k) (Set.Icc 0 N)) :
    ‖∑ k ∈ range (N + 1), phaseCharacter (u k)‖ ≤ 1 / δ := by
  let d : ℕ → ℝ := fun k => u (k + 1) - u k
  have hpos (k : ℕ) (hk : k ≤ N) : 0 < d k := hδ.trans_le (hlo k hk)
  have hlt (k : ℕ) (hk : k ≤ N) : d k < 1 := by dsimp [d]; linarith [hhi k hk]
  have he : (∑ k ∈ range (N + 1), phaseCharacter (u k)) =
      phaseResolvent (d 0) * phaseCharacter (u 0) -
        phaseResolvent (d N) * phaseCharacter (u (N + 1)) +
        ∑ k ∈ range N, (phaseResolvent (d (k + 1)) - phaseResolvent (d k)) *
          phaseCharacter (u (k + 1)) := by
    calc
      _ = ∑ k ∈ range (N + 1), phaseResolvent (d k) *
          (phaseCharacter (u k) - phaseCharacter (u (k + 1))) := by
        apply sum_congr rfl
        intro k hk
        exact phaseCharacter_eq_resolvent_mul_sub _ _ (hpos k (by simpa using hk))
          (hlt k (by simpa using hk))
      _ = _ := sum_range_mul_sub_identity _ _ N
  have hvar := sum_norm_phaseResolvent_sub d N hpos hlt hmono
  have hq (k : ℕ) (hk : k ≤ N) : |halfCotPhase (d k)| ≤ ‖phaseResolvent (d k)‖ := by
    have h := Complex.abs_im_le_norm (phaseResolvent (d k))
    simpa [phaseResolvent_eq _ (hpos k hk) (hlt k hk)] using h
  have hvarle : halfCotPhase (d 0) - halfCotPhase (d N) ≤
      ‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖ := by
    have h0 := (abs_le.mp (hq 0 (Nat.zero_le N))).2
    have hN := (abs_le.mp (hq N le_rfl)).1
    linarith
  rw [he]
  calc
    _ ≤ ‖phaseResolvent (d 0) * phaseCharacter (u 0) -
          phaseResolvent (d N) * phaseCharacter (u (N + 1))‖ +
        ‖∑ k ∈ range N, (phaseResolvent (d (k + 1)) - phaseResolvent (d k)) *
          phaseCharacter (u (k + 1))‖ := norm_add_le _ _
    _ ≤ (‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖) +
        ∑ k ∈ range N, ‖phaseResolvent (d (k + 1)) - phaseResolvent (d k)‖ := by
      apply add_le_add
      · simpa only [norm_mul, norm_phaseCharacter, mul_one] using norm_sub_le
          (phaseResolvent (d 0) * phaseCharacter (u 0))
          (phaseResolvent (d N) * phaseCharacter (u (N + 1)))
      · simpa only [norm_mul, norm_phaseCharacter, mul_one] using norm_sum_le (range N)
          (fun k => (phaseResolvent (d (k + 1)) - phaseResolvent (d k)) *
            phaseCharacter (u (k + 1)))
    _ = (‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖) +
        (halfCotPhase (d 0) - halfCotPhase (d N)) := by rw [hvar]
    _ ≤ 2 * (‖phaseResolvent (d 0)‖ + ‖phaseResolvent (d N)‖) := by linarith
    _ ≤ 2 * (1 / (4 * δ) + 1 / (4 * δ)) := by
      gcongr
      · exact norm_phaseResolvent_le δ _ hδ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
      · exact norm_phaseResolvent_le δ _ hδ (hlo N le_rfl) (hhi N le_rfl)
    _ = 1 / δ := by ring

/-- Closed-endpoint form: only differences between included phase values are
required. The final term is kept, costing at most one. -/
theorem norm_sum_phaseCharacter_le_of_monotone_increments_closed
    (u : ℕ → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hlo : ∀ k < N, δ ≤ u (k + 1) - u k)
    (hhi : ∀ k < N, u (k + 1) - u k ≤ 1 - δ)
    (hmono : MonotoneOn (fun k => u (k + 1) - u k) (Set.Ico 0 N)) :
    ‖∑ k ∈ range (N + 1), phaseCharacter (u k)‖ ≤ 1 + 1 / δ := by
  cases N with
  | zero => simpa using (show (1 : ℝ) ≤ 1 + 1 / δ from le_add_of_nonneg_right (by positivity))
  | succ N =>
    have h := norm_sum_phaseCharacter_le_of_monotone_increments u N δ hδ
      (fun k hk => hlo k (by omega)) (fun k hk => hhi k (by omega))
      (fun i hi j hj hij => hmono ⟨hi.1, Nat.lt_succ_of_le hi.2⟩
        ⟨hj.1, Nat.lt_succ_of_le hj.2⟩ hij)
    rw [sum_range_succ]
    calc
      _ ≤ ‖∑ k ∈ range (N + 1), phaseCharacter (u k)‖ +
          ‖phaseCharacter (u (N + 1))‖ := norm_add_le _ _
      _ ≤ 1 / δ + 1 := add_le_add h (le_of_eq (norm_phaseCharacter _))
      _ = 1 + 1 / δ := add_comm _ _

end
end Erdos878.TrackB
