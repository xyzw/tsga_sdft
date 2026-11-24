import TSGA.SSWRate
import TSGA.FrozenEnergy

/-! # Finite SSW rates for frozen tile energies

After covariance identifies the frozen energy per unit cutoff mass with the
oriented tetrahedron energy, the upper and lower rates give the signed
finite-size comparison used on a small-oscillation ball.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory SSW
open scoped ComplexOrder

private theorem cutoffMass_nonneg (T : AveragedTiles) : 0 ≤ ∫ z, T.cutoffProfile z := by
  apply integral_nonneg
  intro z
  let := T.space
  exact integral_nonneg fun i => mul_nonneg (T.weight_nonneg i) (T.shape_mem i z).1

/-- At fixed dilation, multiply the orientation-averaged tetrahedron rate by
the actual mass of the cutoff. The covariance input involves only finite
energies. -/
theorem AveragedTiles.frozen_upper_rate {F : GasEnergies} {η : Mollifier} {K : ℝ}
    (T : AveragedTiles) (H : FiniteRateTiling F.energy η K) {M : SpinMatrix}
    (hM : M.PosSemidef) (q c : Position) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hscale : δ * K ≤ ℓ) (hgas : F.ssw M q = sswEnergy F.energy η M q)
    (covariance : T.frozenEnergy F M q c = (∫ z, T.cutoffProfile z) *
      averagedTile F.energy η M q ℓ δ) :
    T.frozenEnergy F M q c ≤ F.ssw M q * (∫ z, T.cutoffProfile z) +
      (∫ z, T.cutoffProfile z) * ((K ^ 2 + K) * upperRateError M.trace.re q ℓ δ) := by
  have h := mul_le_mul_of_nonneg_left (H.upper_rate hM q hℓ hδ hscale) (cutoffMass_nonneg T)
  rw [covariance, hgas]
  linarith only [h]

theorem upperRateError_dilate {ρ ℓ δ t : ℝ} (q : Position) (hr : 0 ≤ ρ)
    (hℓ : 0 < ℓ) (hδ : 0 < δ) (ht : t ∈ scaleInterval) :
    upperRateError ρ q (t * ℓ) (t * δ) ≤ 4 * upperRateError ρ q ℓ δ := by
  have hlo : (1 / 2 : ℝ) ≤ t := ht.1
  have hhi : t ≤ (3 / 2 : ℝ) := ht.2
  have hp : 0 < t := by linarith
  have hi : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hp (by norm_num)]
    linarith
  have his : (t⁻¹)^2 ≤ 4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (add_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (inv_nonneg.mpr hp.le))]
  have hs : t^2 ≤ 4 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ 2 - t) (by linarith : 0 ≤ 2 + t)]
  have hg : 0 ≤ δ * rateGrowth ρ q :=
    mul_nonneg hδ.le (add_nonneg (add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)) (sq_nonneg _))
  calc
    _ = ρ / ℓ * (t⁻¹ + (t⁻¹)^2 * δ⁻¹ + t^2 * (δ^3 * ρ) + δ * rateGrowth ρ q) := by
      dsimp [upperRateError, lowerRateError]
      field_simp [hp.ne', hℓ.ne', hδ.ne']
      ring
    _ ≤ ρ / ℓ * (4 * (1 + δ⁻¹ + δ^3 * ρ + δ * rateGrowth ρ q)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hr hℓ.le)
      linarith only [hi, mul_le_mul_of_nonneg_right his (inv_nonneg.mpr hδ.le),
        mul_le_mul_of_nonneg_right hs (mul_nonneg (pow_nonneg hδ.le 3) hr), hg]
    _ = _ := by dsimp [upperRateError, lowerRateError]; ring

theorem scaleAverage_le_const {f : ℝ → ℝ} {b : ℝ}
    (hf : IntegrableOn (fun t => f t * scaleWeight t) scaleInterval)
    (hb : ∀ t ∈ scaleInterval, f t ≤ b) : scaleAverage f ≤ b := by
  have hw := scaleWeight_integrableOn
  have hp := scaleWeight_integral_pos
  apply (div_le_iff₀ hp).2
  rw [← integral_const_mul]
  apply integral_mono_ae hf (hw.const_mul b)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
  exact mul_le_mul_of_nonneg_right (hb t ht) (inv_nonneg.mpr (by positivity : 0 ≤ t^4))

/-- The upper comparison also works when the parameter family includes the
dilation average. Uniformity on [1/2,3/2] costs at most a factor of four. -/
theorem AveragedTiles.frozen_upper_averaged_rate {F : GasEnergies} {η : Mollifier} {K : ℝ}
    (T : AveragedTiles) (H : FiniteRateTiling F.energy η K) {M : SpinMatrix}
    (hM : M.PosSemidef) (q c : Position) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hscale : δ * K ≤ ℓ) (hgas : F.ssw M q = sswEnergy F.energy η M q)
    (covariance : T.frozenEnergy F M q c = (∫ z, T.cutoffProfile z) *
      scaleAverage (fun t => averagedTile F.energy η M q (t * ℓ) (t * δ))) :
    T.frozenEnergy F M q c ≤ F.ssw M q * (∫ z, T.cutoffProfile z) +
      (∫ z, T.cutoffProfile z) * ((K ^ 2 + K) * (4 * upperRateError M.trace.re q ℓ δ)) := by
  have hr : 0 ≤ M.trace.re := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hK := zero_le_one.trans H.one_le
  have h := scaleAverage_le_const (H.dilation_integrable M hM q ℓ δ hℓ hδ hscale) (fun t ht => by
    have hlo : (1/2 : ℝ) ≤ t := ht.1
    have hp : 0 < t := by linarith
    have hs : (t * δ) * K ≤ t * ℓ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hscale hp.le
    exact (H.upper_rate hM q (mul_pos hp hℓ) (mul_pos hp hδ) hs).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (upperRateError_dilate q hr hℓ hδ ht)
        (add_nonneg (sq_nonneg K) hK)) _))
  rw [covariance, hgas]
  linarith only [mul_le_mul_of_nonneg_left h (cutoffMass_nonneg T)]

/-- The lower localization uses tetrahedra averaged with the normalized
dilation density proportional to t⁻⁴ before applying the signed bound. -/
theorem AveragedTiles.frozen_lower_rate {F : GasEnergies} {η : Mollifier} {K : ℝ}
    (T : AveragedTiles) (H : FiniteRateTiling F.energy η K) {M : SpinMatrix}
    (hM : M.PosSemidef) (q c : Position) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hscale : δ * K ≤ ℓ) (hgas : F.ssw M q = sswEnergy F.energy η M q)
    (covariance : T.frozenEnergy F M q c = (∫ z, T.cutoffProfile z) *
      scaleAverage (fun t => averagedTile F.energy η M q (t * ℓ) (t * δ))) :
    -T.frozenEnergy F M q c ≤ -F.ssw M q * (∫ z, T.cutoffProfile z) +
      (∫ z, T.cutoffProfile z) * (K * lowerRateError M.trace.re q ℓ δ) := by
  have h := mul_le_mul_of_nonneg_left (H.lower_rate hM q hℓ hδ hscale) (cutoffMass_nonneg T)
  rw [covariance, hgas]
  linarith only [h]

/-- Shared comparison scales for one frozen matrix and wavevector. The
finite tiling inequalities are uniform over all matrices and wavevectors. -/
structure FrozenRateScales (F : GasEnergies) (M : SpinMatrix) (q : Position) where
  kernel : Mollifier
  coefficient : ℝ
  length : ℝ
  width : ℝ
  tiling : FiniteRateTiling F.energy kernel coefficient
  length_pos : 0 < length
  width_pos : 0 < width
  width_le : width * coefficient ≤ length
  gas : F.ssw M q = sswEnergy F.energy kernel M q

/-- Finite covariance identities and scalar errors for the two signs. At
positive sign the dilation may either have been fixed or averaged. -/
inductive FrozenSizeRate (F : GasEnergies) (T : AveragedTiles) (M : SpinMatrix)
    (q c : Position) (error : ℝ) : ℝ → Prop where
  | upper (s : FrozenRateScales F M q)
      (covariance : T.frozenEnergy F M q c = (∫ z, T.cutoffProfile z) *
        averagedTile F.energy s.kernel M q s.length s.width)
      (bound : (∫ z, T.cutoffProfile z) * ((s.coefficient ^ 2 + s.coefficient) *
        upperRateError M.trace.re q s.length s.width) ≤ error) : FrozenSizeRate F T M q c error 1
  | upperAverage (s : FrozenRateScales F M q)
      (covariance : T.frozenEnergy F M q c = (∫ z, T.cutoffProfile z) *
        scaleAverage (fun t => averagedTile F.energy s.kernel M q (t*s.length) (t*s.width)))
      (bound : (∫ z, T.cutoffProfile z) * ((s.coefficient ^ 2 + s.coefficient) *
        (4 * upperRateError M.trace.re q s.length s.width)) ≤ error) : FrozenSizeRate F T M q c error 1
  | lower (s : FrozenRateScales F M q)
      (covariance : T.frozenEnergy F M q c = (∫ z, T.cutoffProfile z) *
        scaleAverage (fun t => averagedTile F.energy s.kernel M q (t*s.length) (t*s.width)))
      (bound : (∫ z, T.cutoffProfile z) * (s.coefficient *
        lowerRateError M.trace.re q s.length s.width) ≤ error) : FrozenSizeRate F T M q c error (-1)

theorem FrozenSizeRate.estimate {F : GasEnergies} {T : AveragedTiles} {M : SpinMatrix}
    {q c : Position} {error σ : ℝ} (H : FrozenSizeRate F T M q c error σ) (hM : M.PosSemidef) :
    σ * T.frozenEnergy F M q c ≤ (σ * F.ssw M q) * (∫ z, T.cutoffProfile z) + error := by
  cases H with
  | upper s covariance bound =>
    simp only [one_mul]
    exact (T.frozen_upper_rate s.tiling hM q c s.length_pos s.width_pos s.width_le s.gas covariance).trans
      (add_le_add_right bound _)
  | upperAverage s covariance bound =>
    simp only [one_mul]
    exact (T.frozen_upper_averaged_rate s.tiling hM q c s.length_pos s.width_pos s.width_le s.gas covariance).trans
      (add_le_add_right bound _)
  | lower s covariance bound =>
    simp only [neg_one_mul]
    exact (T.frozen_lower_rate s.tiling hM q c s.length_pos s.width_pos s.width_le s.gas covariance).trans
      (add_le_add_right bound _)

end TSGA.Localization
