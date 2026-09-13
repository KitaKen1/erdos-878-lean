import Erdos878.TrackBFrequencyWindow

/-!
# Track B: a finite Fejér kernel and a circular-window minorant

The kernel is defined as a square of a finite sum. All estimates are finite;
no Fourier series or convergence interchange is used.
-/

namespace Erdos878.TrackB
open Finset
open scoped ComplexConjugate
noncomputable section

def fejerPhaseSum (K : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ range K, phaseCharacter ((j : ℝ)*u)

def finiteFejerKernel (K : ℕ) (u : ℝ) : ℝ := ‖fejerPhaseSum K u‖^2 / (K : ℝ)^2

/-- The closed circular interval with center `c` and half-width `b`.
This definition deliberately allows the interval to wrap around 0. -/
def inPhaseWindow (c b u : ℝ) : Prop :=
  Int.fract (u-c) ≤ b ∨ 1-b ≤ Int.fract (u-c)

instance (c b u : ℝ) : Decidable (inPhaseWindow c b u) :=
  inferInstanceAs (Decidable (Int.fract (u-c) ≤ b ∨ 1-b ≤ Int.fract (u-c)))

def fejerLeakage (K : ℕ) (b : ℝ) : ℝ := 1 / (4*(K : ℝ)^2*b^2)

def finiteFejerMinorant (K : ℕ) (c b u : ℝ) : ℝ :=
  finiteFejerKernel K (u-c) - fejerLeakage K b

/-- When the window does not wrap, the circular predicate is exactly the
ordinary closed interval for the fractional part. -/
theorem inPhaseWindow_iff_fract_mem (c b u : ℝ) (hb : 0 < b)
    (hlo : 0 < c-b) (hhi : c+b < 1) :
    inPhaseWindow c b u ↔ c-b ≤ Int.fract u ∧ Int.fract u ≤ c+b := by
  let f := Int.fract u
  have hf0 : 0 ≤ f := Int.fract_nonneg u
  have hf1 : f < 1 := Int.fract_lt_one u
  have hfract : Int.fract (u-c) = Int.fract (f-c) := by
    apply Int.fract_eq_fract.mpr
    refine ⟨⌊u⌋, ?_⟩
    change (u-c)-(Int.fract u-c) = (⌊u⌋ : ℝ)
    linarith [Int.fract_add_floor u]
  unfold inPhaseWindow
  rw [hfract]
  change Int.fract (f-c) ≤ b ∨ 1-b ≤ Int.fract (f-c) ↔ c-b ≤ f ∧ f ≤ c+b
  by_cases hfc : c ≤ f
  · rw [Int.fract_eq_self.mpr (show 0 ≤ f-c ∧ f-c < 1 by constructor <;> linarith)]
    constructor
    · rintro (hleft | hright) <;> constructor <;> linarith
    · rintro ⟨_, hupper⟩
      left
      linarith
  · have hfr : Int.fract (f-c) = f-c+1 := by
      rw [← Int.fract_add_one (f-c)]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hfr]
    constructor
    · rintro (hleft | hright) <;> constructor <;> linarith
    · rintro ⟨hlower, _⟩
      right
      linarith

theorem phaseCharacter_fract (u : ℝ) : phaseCharacter (Int.fract u) = phaseCharacter u := by
  exact phaseCharacter_sub_int u ⌊u⌋

theorem fejerPhaseSum_mul_one_sub (K : ℕ) (u : ℝ) :
    fejerPhaseSum K u * (1-phaseCharacter u) = 1-phaseCharacter ((K : ℝ)*u) := by
  induction K with
  | zero => simp [fejerPhaseSum, phaseCharacter]
  | succ K ih =>
    have hphase : phaseCharacter (((K+1 : ℕ) : ℝ)*u) =
        phaseCharacter ((K : ℝ)*u) * phaseCharacter u := by
      rw [show (((K+1 : ℕ) : ℝ)*u) = (K : ℝ)*u+u by push_cast; ring, phaseCharacter_add]
    simp only [fejerPhaseSum, sum_range_succ] at ih ⊢
    rw [hphase, add_mul, ih]
    ring

theorem norm_fejerPhaseSum_le (K : ℕ) (u : ℝ) : ‖fejerPhaseSum K u‖ ≤ K := by
  calc
    _ ≤ ∑ j ∈ range K, ‖phaseCharacter ((j : ℝ)*u)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem finiteFejerKernel_nonneg (K : ℕ) (u : ℝ) : 0 ≤ finiteFejerKernel K u := by
  unfold finiteFejerKernel
  positivity

theorem finiteFejerKernel_le_one (K : ℕ) (u : ℝ) : finiteFejerKernel K u ≤ 1 := by
  by_cases hK : K = 0
  · simp [finiteFejerKernel, hK]
  · have hKr : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
    apply (div_le_one (pow_pos hKr 2)).2
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fejerPhaseSum_le K u) 2

theorem finiteFejerKernel_zero (K : ℕ) (hK : 0 < K) : finiteFejerKernel K 0 = 1 := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  simp [finiteFejerKernel, fejerPhaseSum, phaseCharacter, hKr]

/-- Outside the central circular interval, the geometric sum is small. -/
theorem norm_fejerPhaseSum_le_of_far (K : ℕ) (u b : ℝ) (hb : 0 < b)
    (hlo : b ≤ Int.fract u) (hhi : Int.fract u ≤ 1-b) :
    ‖fejerPhaseSum K u‖ ≤ 1/(2*b) := by
  have hf0 : 0 < Int.fract u := hb.trans_le hlo
  have hf1 : Int.fract u < 1 := by linarith
  have hne : 1-phaseCharacter u ≠ 0 := by
    rw [← phaseCharacter_fract u]
    exact one_sub_phaseCharacter_ne_zero _ hf0 hf1
  have he : fejerPhaseSum K u = (1-phaseCharacter ((K : ℝ)*u))*phaseResolvent u := by
    have ht := congrArg (fun z : ℂ => z * (1-phaseCharacter u)⁻¹)
      (fejerPhaseSum_mul_one_sub K u)
    simpa only [mul_assoc, mul_inv_cancel₀ hne, mul_one, phaseResolvent] using ht
  have hr : ‖phaseResolvent u‖ ≤ 1/(4*b) := by
    have ht := norm_phaseResolvent_le b (Int.fract u) hb hlo hhi
    simpa only [phaseResolvent, phaseCharacter_fract] using ht
  have hnum : ‖1-phaseCharacter ((K : ℝ)*u)‖ ≤ 2 := by
    convert norm_sub_le (1 : ℂ) (phaseCharacter ((K : ℝ)*u)) using 1; norm_num
  rw [he, norm_mul]
  calc
    _ ≤ 2*(1/(4*b)) := mul_le_mul hnum hr (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem finiteFejerKernel_le_leakage (K : ℕ) (u b : ℝ) (hK : 0 < K) (hb : 0 < b)
    (hlo : b ≤ Int.fract u) (hhi : Int.fract u ≤ 1-b) :
    finiteFejerKernel K u ≤ fejerLeakage K b := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  calc
    _ ≤ (1/(2*b))^2/(K : ℝ)^2 := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fejerPhaseSum_le_of_far K u b hb hlo hhi) 2)
      (sq_nonneg _)
    _ = _ := by unfold fejerLeakage; field_simp; ring

/-- Pointwise minorization of a circular-window indicator. -/
theorem finiteFejerMinorant_le_indicator (K : ℕ) (c b u : ℝ) (hK : 0 < K) (hb : 0 < b) :
    finiteFejerMinorant K c b u ≤ if inPhaseWindow c b u then 1 else 0 := by
  classical
  have he0 : 0 ≤ fejerLeakage K b := by unfold fejerLeakage; positivity
  by_cases hw : inPhaseWindow c b u
  · simp only [ite_eq_left hw, finiteFejerMinorant]
    linarith [finiteFejerKernel_le_one K (u-c)]
  · simp only [ite_eq_right hw, finiteFejerMinorant]
    have hfar : b ≤ Int.fract (u-c) ∧ Int.fract (u-c) ≤ 1-b := by
      simp only [inPhaseWindow, not_or] at hw
      exact ⟨(lt_of_not_ge hw.1).le, (lt_of_not_ge hw.2).le⟩
    linarith [finiteFejerKernel_le_leakage K (u-c) b hK hb hfar.1 hfar.2]

/-- The constant coefficient remains positive once the kernel is sufficiently narrow. -/
theorem fejer_constant_coefficient_lower (K : ℕ) (b : ℝ) (hK : 0 < K) (_hb : 0 < b)
    (hwidth : 1 ≤ 2*(K : ℝ)*b^2) :
    1/(2*(K : ℝ)) ≤ 1/(K : ℝ) - fejerLeakage K b := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have he : fejerLeakage K b ≤ 1/(2*(K : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 2*(K : ℝ) by positivity)]
  have hid : 1/(K : ℝ) = 1/(2*(K : ℝ)) + 1/(2*(K : ℝ)) := by ring
  linarith

end
end Erdos878.TrackB
