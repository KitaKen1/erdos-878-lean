import Erdos878.TrackBTypeI

/-!
# Track B: a proved finite bound for the full von Mangoldt phase sum

All three Vaughan pieces are estimated here with their actual coefficients.
The remaining analytic task is to insert a concrete parameter range and prove
the required logarithmic saving; no such asymptotic claim is made by this file.
-/

namespace Erdos878.TrackB
open Finset
noncomputable section

/-- Explicit majorant for the full reciprocal-log von Mangoldt sum. -/
def vaughanReciprocalLogBound (a C : ℝ) (U V P X : ℕ) : ℝ :=
  2 * Real.log (X+1 : ℕ) * typeIOuterBound a C P U +
    Real.log (U*V : ℕ) * typeIOuterBound a C P (U*V) +
    18 * (X : ℝ) * Real.log (X : ℝ) ^ 2 * typeIICommonLog X ^ 3 *
      Real.sqrt (typeIIUniformError a P (min U V))

theorem vaughanReciprocalLogBound_nonneg
    (a C : ℝ) (U V P X : ℕ) (hC : 0 ≤ C) :
    0 ≤ vaughanReciprocalLogBound a C U V P X := by
  have hU := typeIOuterBound_nonneg a C P U hC
  have hUV := typeIOuterBound_nonneg a C P (U*V) hC
  have hlogUV := Real.log_natCast_nonneg (U*V)
  have hlogX := Real.log_natCast_nonneg (X+1)
  have hH : 0 ≤ typeIICommonLog X := zero_le_one.trans (one_le_typeIICommonLog X)
  unfold vaughanReciprocalLogBound
  positivity

/-- A finite cancellation bound, uniform over every partial endpoint `Y ≤ X`.
The only assumptions are scalar size/positivity conditions on the parameters;
no Type-I, Type-II, or exponential-sum estimate is assumed. -/
theorem norm_weightedArithmeticSum_vonMangoldt_le_uniform_endpoint
    (a C : ℝ) (U V P Y X : ℕ)
    (ha : 0 < a) (haP : a ≤ (P : ℝ)) (hC : 1 ≤ C) (hP : 0 < P)
    (hPlog : 1 ≤ Real.log (P : ℝ)) (hCP : C ≤ (P : ℝ))
    (hX : (X : ℝ) ≤ C * P) (hYX : Y ≤ X)
    (hU : 0 < U) (hV : 0 < V) (hUVP : (U*V) ^ 2 ≤ P) :
    ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a)
      ArithmeticFunction.vonMangoldt‖ ≤ vaughanReciprocalLogBound a C U V P X := by
  have hCr : 0 < C := zero_lt_one.trans_le hC
  have hY : (Y : ℝ) ≤ C*P := (show (Y : ℝ) ≤ X by exact_mod_cast hYX).trans hX
  have hUUV : U ≤ U*V := Nat.le_mul_of_pos_right U hV
  have hVUV : V ≤ U*V := Nat.le_mul_of_pos_left V hU
  have hUP : U^2 ≤ P := (Nat.pow_le_pow_left hUUV 2).trans hUVP
  have hUVleP : U*V ≤ P := (Nat.le_self_pow (by decide) (U*V)).trans hUVP
  have hVP : V ≤ P := hVUV.trans hUVleP
  have hlow := weightedArithmeticSum_lambdaLE_eq_zero V (Ioc P Y)
    (reciprocalLogWeight a) (fun n hn => hVP.trans_lt (mem_Ioc.mp hn).1)
  have hILog := norm_weightedArithmeticSum_typeILog_le a C U P Y
    ha haP hC hP hPlog hCP hY hUP
  have hILogX : ‖weightedArithmeticSum (Ioc P Y) (reciprocalLogWeight a)
      (vaughanTypeILog U)‖ ≤ 2*Real.log (X+1 : ℕ)*typeIOuterBound a C P U := by
    refine hILog.trans ?_
    apply mul_le_mul_of_nonneg_right _ (typeIOuterBound_nonneg a C P U hCr.le)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hYX 1)
  have hILambda := norm_weightedArithmeticSum_typeILambda_le a C U V P Y
    ha haP hC hP hPlog hCP hY hUVP
  have hII := norm_weightedArithmeticSum_typeII_le_uniform_endpoint a C U V P Y X
    ha haP hCr hP hPlog hCP hX hYX hU hV
  rw [vaughan_weighted_sum U V, hlow, zero_add]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hILogX hILambda)) hII)

end
end Erdos878.TrackB
