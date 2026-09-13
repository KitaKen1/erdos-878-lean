import Erdos878.DyadicDivisorNormalOrder

/-!
# Reciprocal mass of report prime windows

The report windows are real logarithmic intervals, whereas the available unconditional lower
bound is organized into disjoint dyadic prime blocks.  This module isolates the transfer.  A
caller only has to choose moving block indices whose harmonic difference diverges and verify that
their first and last endpoints lie in the desired report window and below the integer endpoint.
-/

open Classical Filter Finset Topology
open scoped Real

namespace Erdos878

noncomputable section

/- The existing eventual lower bound is uniform in the tail length.  Consequently any moving
tail whose initial index tends to infinity and whose harmonic index-width diverges has divergent
reciprocal prime mass. -/
theorem tendsto_dyadicDisjointPrimeTail_mass_atTop_of_harmonic_sub
    (K M : ℕ → ℕ)
    (hK : Tendsto K atTop atTop)
    (hdiff : Tendsto (fun X : ℕ ↦
      (harmonic (M X + K X) : ℝ) - (harmonic (K X) : ℝ)) atTop atTop) :
    Tendsto (fun X : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeTail (K X) (M X), ((p : ℝ)⁻¹)) atTop atTop := by
  have hlower : ∀ᶠ X : ℕ in atTop,
      (1 / 8 : ℝ) *
          ((harmonic (M X + K X) : ℝ) - (harmonic (K X) : ℝ)) ≤
        ∑ p ∈ dyadicDisjointPrimeTail (K X) (M X), ((p : ℝ)⁻¹) := by
    filter_upwards
        [hK.eventually eventually_dyadicDisjointPrimeTail_mass_ge_harmonic_sub]
      with X hX
    exact hX (M X)
  have hscaled : Tendsto (fun X : ℕ ↦
      (1 / 8 : ℝ) *
        ((harmonic (M X + K X) : ℝ) - (harmonic (K X) : ℝ))) atTop atTop := by
    simpa [mul_comm] using hdiff.atTop_mul_const (show (0 : ℝ) < 1 / 8 by norm_num)
  exact Filter.tendsto_atTop_mono' atTop hlower hscaled

/- Quantitative form of the square-tail divergence used below. -/
theorem eventually_dyadicDisjointPrimeTail_square_mass_ge_log :
    ∀ᶠ k : ℕ in atTop,
      (1 / 8 : ℝ) * (Real.log (k : ℝ) - 1) ≤
        ∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹) := by
  have hkone : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
  have hlogpow : ∀ᶠ k : ℕ in atTop,
      2 * Real.log (k : ℝ) ≤ Real.log ((k * k + k + 1 : ℕ) : ℝ) := by
    filter_upwards [hkone] with k hk
    have hsqNat : k ^ 2 ≤ k * k + k + 1 := by
      simpa [pow_two] using (show k * k ≤ k * k + k + 1 by omega)
    have hsq : (k : ℝ) ^ 2 ≤ ((k * k + k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hsqNat
    have hlog := Real.log_le_log (by positivity : 0 < (k : ℝ) ^ 2) hsq
    simpa [Real.log_pow] using hlog
  have hdiff : ∀ᶠ k : ℕ in atTop,
      Real.log (k : ℝ) - 1 ≤
        (harmonic (k * k + k) : ℝ) - (harmonic k : ℝ) := by
    filter_upwards [hkone, hlogpow] with k hk hlogpow
    have hlogadd := log_add_one_le_harmonic (k * k + k)
    have hupp := harmonic_le_one_add_log k
    have hlogadd' : Real.log ((k * k + k + 1 : ℕ) : ℝ) ≤
        (harmonic (k * k + k) : ℝ) := by
      simpa using hlogadd
    linarith
  filter_upwards [eventually_dyadicDisjointPrimeTail_mass_ge_harmonic_sub, hdiff]
    with k htail hdiffk
  calc
    (1 / 8 : ℝ) * (Real.log (k : ℝ) - 1) ≤
        (1 / 8 : ℝ) *
          ((harmonic (k * k + k) : ℝ) - (harmonic k : ℝ)) := by gcongr
    _ ≤ ∑ p ∈ dyadicDisjointPrimeTail k (k * k), ((p : ℝ)⁻¹) := by
      simpa [add_comm] using htail (k * k)

theorem dyadicDisjointPrimeTail_mass_le_reportPrimeWindowEndpointMass
    {X K M : ℕ} {a b : ℝ}
    (hlow : Real.exp (Real.rpow (Real.log (X : ℝ)) a) ≤
      (dyadicDisjointLowerEndpoint K : ℝ))
    (hupp : (dyadicDisjointUpperEndpoint (K + M) : ℝ) ≤
      Real.exp (Real.rpow (Real.log (X : ℝ)) b))
    (hendpoint : dyadicDisjointUpperEndpoint (K + M) ≤ X) :
    (∑ p ∈ dyadicDisjointPrimeTail K M, ((p : ℝ)⁻¹)) ≤
      reportPrimeWindowEndpointMass X a b := by
  have hwindow : dyadicDisjointPrimeTail K M ⊆ reportPrimeWindow X a b := by
    simpa [reportPrimeWindow] using
      (dyadicDisjointPrimeTail_subset_primeWindow_of_endpoint_bounds hlow hupp)
  have hIcc : dyadicDisjointPrimeTail K M ⊆ Finset.Icc 1 X := by
    intro p hp
    have hpIcc := Finset.mem_Icc.mp (dyadicDisjointPrimeTail_subset_Icc K M hp)
    exact Finset.mem_Icc.mpr ⟨hpIcc.1, hpIcc.2.trans hendpoint⟩
  unfold reportPrimeWindowEndpointMass reportPrimeWindowInEndpoint
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_inter.mpr ⟨hwindow hp, hIcc hp⟩
  · intro p hp _
    positivity

/- Transfer any dyadic tail with divergent reciprocal mass into one endpoint-truncated report
window. -/
theorem tendsto_reportPrimeWindowEndpointMass_atTop_of_dyadic_tail_mass
    {a b : ℝ} (K M : ℕ → ℕ)
    (htail : Tendsto (fun X : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeTail (K X) (M X), ((p : ℝ)⁻¹)) atTop atTop)
    (hlow : ∀ᶠ X : ℕ in atTop,
      Real.exp (Real.rpow (Real.log (X : ℝ)) a) ≤
        (dyadicDisjointLowerEndpoint (K X) : ℝ))
    (hupp : ∀ᶠ X : ℕ in atTop,
      (dyadicDisjointUpperEndpoint (K X + M X) : ℝ) ≤
        Real.exp (Real.rpow (Real.log (X : ℝ)) b))
    (hendpoint : ∀ᶠ X : ℕ in atTop,
      dyadicDisjointUpperEndpoint (K X + M X) ≤ X) :
    Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X a b) atTop atTop := by
  have hcompare : ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ dyadicDisjointPrimeTail (K X) (M X), ((p : ℝ)⁻¹)) ≤
        reportPrimeWindowEndpointMass X a b := by
    filter_upwards [hlow, hupp, hendpoint] with X hlowX huppX hendpointX
    exact dyadicDisjointPrimeTail_mass_le_reportPrimeWindowEndpointMass
      hlowX huppX hendpointX
  exact Filter.tendsto_atTop_mono' atTop hcompare htail

/- Harmonic-width specialization of the preceding transfer.  The three finite inclusions are
kept explicit so the later choice of `K,M` can be changed without modifying the density proof. -/
theorem tendsto_reportPrimeWindowEndpointMass_atTop_of_dyadic_tail
    {a b : ℝ} (K M : ℕ → ℕ)
    (hK : Tendsto K atTop atTop)
    (hdiff : Tendsto (fun X : ℕ ↦
      (harmonic (M X + K X) : ℝ) - (harmonic (K X) : ℝ)) atTop atTop)
    (hlow : ∀ᶠ X : ℕ in atTop,
      Real.exp (Real.rpow (Real.log (X : ℝ)) a) ≤
        (dyadicDisjointLowerEndpoint (K X) : ℝ))
    (hupp : ∀ᶠ X : ℕ in atTop,
      (dyadicDisjointUpperEndpoint (K X + M X) : ℝ) ≤
        Real.exp (Real.rpow (Real.log (X : ℝ)) b))
    (hendpoint : ∀ᶠ X : ℕ in atTop,
      dyadicDisjointUpperEndpoint (K X + M X) ≤ X) :
    Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X a b) atTop atTop := by
  exact tendsto_reportPrimeWindowEndpointMass_atTop_of_dyadic_tail_mass K M
    (tendsto_dyadicDisjointPrimeTail_mass_atTop_of_harmonic_sub K M hK hdiff)
    hlow hupp hendpoint

def reportDyadicStartIndex (X : ℕ) (a : ℝ) : ℕ :=
  Nat.ceil (Real.rpow (Real.log (X : ℝ)) a / (4 * Real.log 2))

theorem tendsto_reportDyadicStartIndex_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun X : ℕ ↦ reportDyadicStartIndex X a) atTop atTop := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ ↦ Real.rpow (Real.log (X : ℝ)) a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp hlog
  have hden : 0 < (4 : ℝ) * Real.log 2 := by positivity
  have hdiv : Tendsto (fun X : ℕ ↦
      Real.rpow (Real.log (X : ℝ)) a / (4 * Real.log 2)) atTop atTop :=
    Tendsto.atTop_div_const hden hpow
  exact tendsto_nat_ceil_atTop.comp hdiv

theorem reportDyadicStartIndex_lower_endpoint
    (X : ℕ) (a : ℝ) :
    Real.exp (Real.rpow (Real.log (X : ℝ)) a) ≤
      (dyadicDisjointLowerEndpoint (reportDyadicStartIndex X a) : ℝ) := by
  simpa [reportDyadicStartIndex] using
    (dyadicDisjointLowerEndpoint_ge_exp_rpow
      (T := Real.log (X : ℝ)) (a := a))

theorem eventually_log_reportDyadicStartIndex_ge
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ X : ℕ in atTop,
      a / 4 * Real.log (Real.log (X : ℝ)) + 1 ≤
        Real.log (reportDyadicStartIndex X a : ℝ) := by
  let D : ℝ := 4 * Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  let C : ℝ := 4 * (|Real.log D| + 1) / (3 * a)
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_ge_atTop C)] with X hT hlarge
  let T : ℝ := Real.log (X : ℝ)
  let u : ℝ := Real.rpow T a
  let K : ℕ := reportDyadicStartIndex X a
  have hu : 0 < u := Real.rpow_pos_of_pos hT a
  have hquot : 0 < u / D := div_pos hu hD
  have hceil : u / D ≤ (K : ℝ) := by
    simpa [K, reportDyadicStartIndex, u, T, D] using
      (Nat.le_ceil (u / D))
  have hlogK : Real.log (u / D) ≤ Real.log (K : ℝ) :=
    Real.log_le_log hquot hceil
  rw [Real.log_div hu.ne' hD.ne'] at hlogK
  dsimp [u] at hlogK
  rw [Real.log_rpow hT a] at hlogK
  have hcoef : 0 < 3 * a / 4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlarge hcoef.le
  have hCeq : (3 * a / 4) * C = |Real.log D| + 1 := by
    dsimp [C]
    field_simp [ha.ne']
  rw [hCeq] at hscaled
  change |Real.log D| + 1 ≤ 3 * a / 4 * Real.log T at hscaled
  have hlogD : Real.log D + 1 ≤ 3 * a / 4 * Real.log T := by
    linarith [le_abs_self (Real.log D)]
  change a / 4 * Real.log T + 1 ≤ Real.log (K : ℝ)
  calc
    a / 4 * Real.log T + 1 ≤ a * Real.log T - Real.log D := by
      linarith
    _ ≤ Real.log (K : ℝ) := hlogK

/- A square-length tail fits below the upper logarithmic endpoint whenever `2a < b`.  This is the
one place where ceiling/floor errors are paid; the power gap absorbs them uniformly. -/
theorem eventually_reportDyadicStartIndex_square_le_floor
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a < b) :
    ∀ᶠ X : ℕ in atTop,
      let K := reportDyadicStartIndex X a
      K + K * K + 1 ≤
        Nat.floor (Real.rpow (Real.log (X : ℝ)) b / (4 * Real.log 2)) := by
  let D : ℝ := 4 * Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowdiff : Tendsto (fun X : ℕ ↦
      Real.rpow (Real.log (X : ℝ)) (b - 2 * a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp hlog
  filter_upwards
      [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
       hpowdiff.eventually
        (eventually_ge_atTop (3 * (1 + D) ^ 2 / D))]
    with X hT hv
  let T : ℝ := Real.log (X : ℝ)
  let u : ℝ := Real.rpow T a
  let v : ℝ := Real.rpow T (b - 2 * a)
  let K : ℕ := reportDyadicStartIndex X a
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hu : 1 ≤ u := Real.one_le_rpow hT ha.le
  have hy : 0 ≤ u / D := div_nonneg (by positivity) hD.le
  have hKlt : (K : ℝ) < u / D + 1 := by
    simpa [K, reportDyadicStartIndex, T, u, D] using Nat.ceil_lt_add_one hy
  have hz : 0 ≤ u / D + 1 := by positivity
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hKsq : (K : ℝ) ^ 2 ≤ (u / D + 1) ^ 2 :=
    (sq_le_sq₀ hK0 hz).2 hKlt.le
  have honeSq : (1 : ℝ) ≤ (u / D + 1) ^ 2 := by nlinarith [hy]
  have hpoly : (K : ℝ) + (K : ℝ) ^ 2 + 1 ≤ 3 * (u / D + 1) ^ 2 := by
    nlinarith
  have hzupper : u / D + 1 ≤ u * (1 + D) / D := by
    rw [show u / D + 1 = (u + D) / D by field_simp [hD.ne']]
    apply (div_le_div_iff₀ hD hD).2
    have hmul : 0 ≤ D * (u - 1) := mul_nonneg hD.le (sub_nonneg.mpr hu)
    nlinarith
  have hzupper0 : 0 ≤ u * (1 + D) / D := hz.trans hzupper
  have hzsq : (u / D + 1) ^ 2 ≤ (u * (1 + D) / D) ^ 2 :=
    (sq_le_sq₀ hz hzupper0).2 hzupper
  have hv' : 3 * (1 + D) ^ 2 / D ≤ v := by simpa [v, T, D] using hv
  have hmul := mul_le_mul_of_nonneg_right hv'
    (div_nonneg (sq_nonneg u) hD.le)
  have hsplit : Real.rpow T b = v * u ^ 2 := by
    change T ^ b = (T ^ (b - 2 * a)) * (T ^ a) ^ 2
    rw [show b = (b - 2 * a) + (a + a) by ring,
      Real.rpow_add hTpos (b - 2 * a) (a + a),
      Real.rpow_add hTpos a a]
    ring_nf
  have hmain : 3 * (u * (1 + D) / D) ^ 2 ≤ Real.rpow T b / D := by
    calc
      3 * (u * (1 + D) / D) ^ 2 =
          (3 * (1 + D) ^ 2 / D) * (u ^ 2 / D) := by
            field_simp [hD.ne']
      _ ≤ v * (u ^ 2 / D) := hmul
      _ = Real.rpow T b / D := by rw [hsplit]; ring
  have hcast : (((K + K * K + 1 : ℕ) : ℝ)) ≤ Real.rpow T b / D := by
    calc
      (((K + K * K + 1 : ℕ) : ℝ)) = (K : ℝ) + (K : ℝ) ^ 2 + 1 := by
        norm_num [pow_two]
      _ ≤ 3 * (u / D + 1) ^ 2 := hpoly
      _ ≤ 3 * (u * (1 + D) / D) ^ 2 := by gcongr
      _ ≤ Real.rpow T b / D := hmain
  dsimp only
  exact Nat.le_floor (by simpa [K, T, D] using hcast)

theorem eventually_reportDyadic_square_upper_endpoint
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a < b) :
    ∀ᶠ X : ℕ in atTop,
      let K := reportDyadicStartIndex X a
      (dyadicDisjointUpperEndpoint (K + K * K) : ℝ) ≤
        Real.exp (Real.rpow (Real.log (X : ℝ)) b) := by
  filter_upwards [eventually_reportDyadicStartIndex_square_le_floor ha hab,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with X hfloor hlog
  dsimp only
  exact dyadicDisjointUpperEndpoint_le_exp_rpow hlog (by simpa using hfloor)

theorem eventually_reportDyadic_square_upper_endpoint_le_self
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a < b) (hb1 : b < 1) :
    ∀ᶠ X : ℕ in atTop,
      let K := reportDyadicStartIndex X a
      dyadicDisjointUpperEndpoint (K + K * K) ≤ X := by
  filter_upwards [eventually_reportDyadic_square_upper_endpoint ha hab,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with X hupper hlog hX
  dsimp only at hupper ⊢
  have hrpow : Real.rpow (Real.log (X : ℝ)) b ≤ Real.log (X : ℝ) :=
    Real.rpow_le_self_of_one_le hlog hb1.le
  have hexp : Real.exp (Real.rpow (Real.log (X : ℝ)) b) ≤ (X : ℝ) := by
    have := Real.exp_le_exp.mpr hrpow
    rw [Real.exp_log (by exact_mod_cast hX)] at this
    exact this
  exact_mod_cast hupper.trans hexp

/- A fully concrete coarse-mass theorem.  A square tail beginning at the canonical lower index
fits in every window with `0<a`, `2a<b<1`; its reciprocal mass diverges unconditionally. -/
theorem tendsto_reportPrimeWindowEndpointMass_atTop_of_two_mul_lt
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a < b) (hb1 : b < 1) :
    Tendsto (fun X : ℕ ↦ reportPrimeWindowEndpointMass X a b) atTop atTop := by
  let K : ℕ → ℕ := fun X ↦ reportDyadicStartIndex X a
  let M : ℕ → ℕ := fun X ↦ K X * K X
  have hK : Tendsto K atTop atTop := by
    simpa [K] using tendsto_reportDyadicStartIndex_atTop ha
  have htail : Tendsto (fun X : ℕ ↦
      ∑ p ∈ dyadicDisjointPrimeTail (K X) (M X), ((p : ℝ)⁻¹)) atTop atTop := by
    simpa [K, M, Function.comp_def] using
      tendsto_dyadicDisjointPrimeTail_mass_square_atTop.comp hK
  apply tendsto_reportPrimeWindowEndpointMass_atTop_of_dyadic_tail_mass K M htail
  · exact Filter.Eventually.of_forall (fun X ↦ by
      simpa [K] using reportDyadicStartIndex_lower_endpoint X a)
  · simpa [K, M] using eventually_reportDyadic_square_upper_endpoint ha hab
  · simpa [K, M] using eventually_reportDyadic_square_upper_endpoint_le_self ha hab hb1

theorem eventually_reportPrimeWindowEndpointMass_ge_loglog
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a < b) (hb1 : b < 1) :
    ∀ᶠ X : ℕ in atTop,
      a / 32 * Real.log (Real.log (X : ℝ)) ≤
        reportPrimeWindowEndpointMass X a b := by
  let K : ℕ → ℕ := fun X ↦ reportDyadicStartIndex X a
  have hK : Tendsto K atTop atTop := by
    simpa [K] using tendsto_reportDyadicStartIndex_atTop ha
  filter_upwards
      [hK.eventually eventually_dyadicDisjointPrimeTail_square_mass_ge_log,
       eventually_log_reportDyadicStartIndex_ge ha,
       eventually_reportDyadic_square_upper_endpoint ha hab,
       eventually_reportDyadic_square_upper_endpoint_le_self ha hab hb1]
    with X htail hlogK hupper hendpoint
  have hlow := reportDyadicStartIndex_lower_endpoint X a
  have hcompare := dyadicDisjointPrimeTail_mass_le_reportPrimeWindowEndpointMass
    (X := X) (K := K X) (M := K X * K X) (a := a) (b := b)
    hlow (by simpa [K] using hupper) (by simpa [K] using hendpoint)
  calc
    a / 32 * Real.log (Real.log (X : ℝ)) ≤
        (1 / 8 : ℝ) * (Real.log (K X : ℝ) - 1) := by
          have hlogK' : a / 4 * Real.log (Real.log (X : ℝ)) + 1 ≤
              Real.log (K X : ℝ) := by simpa [K] using hlogK
          nlinarith
    _ ≤ ∑ p ∈ dyadicDisjointPrimeTail (K X) (K X * K X), ((p : ℝ)⁻¹) := by
      simpa [K] using htail
    _ ≤ reportPrimeWindowEndpointMass X a b := hcompare

/- The two analytic mass premises in the Track-A density shell are now discharged by concrete
square tails.  This already yields an unconditional density-one `F/n → ∞`-strength lower shell;
the quantitative `n log log n` comparison is established in the next layer. -/
theorem exists_density_one_dyadicTrackA_F_lower_of_two_mul_lt
    {α β γ δ rho : ℝ}
    (hα : 0 < α) (h2αβ : 2 * α < β) (hβγ : β ≤ γ)
    (hγ : 0 < γ) (h2γδ : 2 * γ < δ)
    (hδ1 : δ < 1) (hβδ : β + δ < 1) (hrho : 0 < rho) :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      ∀ᶠ n : ℕ in atTop, n ∈ A →
        let X := dyadicReportEndpoint (Nat.log 2 n)
        min (reportPrimeWindowEndpointMass X α β / 2)
            (reportPrimeWindowEndpointMass X γ δ / 2) *
            (n : ℝ) / Real.exp rho ≤ (F n : ℝ) := by
  have hβ : 0 < β := lt_trans (by positivity : 0 < 2 * α) h2αβ
  have hδ0 : 0 ≤ δ := (lt_trans (by positivity : 0 < 2 * γ) h2γδ).le
  have hβ1 : β < 1 := by linarith
  exact exists_density_one_dyadicTrackA_F_lower_of_mass
    hα hβ hβγ hδ0 hδ1 hβδ hrho
    (tendsto_reportPrimeWindowEndpointMass_atTop_of_two_mul_lt hα h2αβ hβ1)
    (tendsto_reportPrimeWindowEndpointMass_atTop_of_two_mul_lt hγ h2γδ hδ1)

end


end Erdos878

#print axioms Erdos878.tendsto_dyadicDisjointPrimeTail_mass_atTop_of_harmonic_sub
#print axioms Erdos878.tendsto_reportPrimeWindowEndpointMass_atTop_of_dyadic_tail_mass
#print axioms Erdos878.tendsto_reportPrimeWindowEndpointMass_atTop_of_dyadic_tail
#print axioms Erdos878.tendsto_reportDyadicStartIndex_atTop
#print axioms Erdos878.tendsto_reportPrimeWindowEndpointMass_atTop_of_two_mul_lt
#print axioms Erdos878.eventually_reportPrimeWindowEndpointMass_ge_loglog
#print axioms Erdos878.exists_density_one_dyadicTrackA_F_lower_of_two_mul_lt
