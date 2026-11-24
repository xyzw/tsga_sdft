import TSGA.CoulombTheorem
import TSGA.GradientForm
import TSGA.RescaledSpiralEstimate

/-! # LSDA, gradient form and particle-number scaling for the Coulomb model -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}

/-- Zero-phase estimates, including the refinement for a positive minority fraction. -/
theorem CoulombModelInputs.lsda (P : CoulombModelInputs μ ι η) {p θ : ℝ}
    (hp : 3 < p) (hθ : 2/p ≤ θ) (hθ' : θ < 1) :
    let F := referenceEnergies energy η
    (∃ C > 0, LSDAEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∀ ν : ℝ, 0 < ν → ν ≤ 1/2 → ∃ C > 0,
      LSDAEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C) :=
  mainLSDA_of_mainTSGA P.tsgaFinite hp hθ hθ'

/-- Corollary 3.5 at arbitrary polarization, obtained by setting the phase to zero. -/
theorem CoulombModelInputs.noncollinearLSDA (P : CoulombModelInputs μ ι η) {p θ : ℝ}
    (hp : 3 < p) (hθ : 2 / p ≤ θ) (hθ' : θ < 1) :
    ∃ C > 0, LSDAEstimate (referenceEnergies energy η) (fun _ => True) p θ (bulkExponent p θ) C :=
  (P.lsda hp hθ hθ').1

/-- Azimuthal-frame estimates, including the refinement for a positive minority fraction. -/
theorem CoulombModelInputs.gradientForm (P : CoulombModelInputs μ ι η) {p : ℝ} (hp : 3 < p) :
    let F := referenceEnergies energy η
    (∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p*θ →
      ∃ C > 0, GradientFormEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∀ θ ν : ℝ, 0 < θ → θ < 1 → 2 ≤ p*θ → 0 < ν → ν ≤ 1/2 →
      ∃ C > 0, GradientFormEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C) ∧
    (∃ C > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p*θ → SharpGradientFormEstimate F p θ C) :=
  gradientForm_of_mainTSGA P.tsga (axialGasInvariant_coulomb η) hp

/-- The reference integral and both error bounds of Corollary 3.4 in the physical spin frame.
The extended right-hand sides are finite under the phase integrability assumptions of Theorem 3.3. -/
theorem CoulombModelInputs.azimuthalTSGA (P : CoulombModelInputs μ ι η) {p : ℝ} (hp : 3 < p) :
    let F := referenceEnergies energy η
    (∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ →
      ∃ C > 0, GradientFormEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∃ C > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ → SharpGradientFormEstimate F p θ C) :=
  ⟨(P.gradientForm hp).1, (P.gradientForm hp).2.2⟩

/-- LSDA particle-number scaling, with the scale chosen separately for the two polarization regimes. -/
theorem CoulombModelInputs.rescaledLSDA (P : CoulombModelInputs μ ι η) {p θ : ℝ}
    (hp : 3 < p) (hθ : 2/p ≤ θ) (hθ' : θ < 1) :
    let F := referenceEnergies energy η
    (∃ C > 0, RescaledLSDAEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∀ ν : ℝ, 0 < ν → ν ≤ 1/2 → ∃ C > 0,
      RescaledLSDAEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C) :=
  rescaledLSDA_of_mainTSGA P.tsgaFinite hp hθ hθ'

open Asymptotics Filter in
/-- The optimized LSDA rate in the introduction, for arbitrary polarization.
The implicit constant may depend on the fixed density profile. -/
theorem CoulombModelInputs.rescaledNoncollinearLSDA (P : CoulombModelInputs μ ι η) {p θ : ℝ}
    (hp : 3 < p) (hθ : 2 / p ≤ θ) (hθ' : θ < 1) (D : Density) (S T : MatrixGradient)
    (reg : DensityRegular D p θ S T) :
    (fun N : ℝ => energy (D.particleScale N).matrix - N * ∫ x, (referenceEnergies energy η).ueg (D.matrix x))
      =O[atTop] (fun N : ℝ => N ^ (max (5 / 6) (1 - 1 / (3 + 9 * θ)))) := by
  obtain ⟨C, hC, bound⟩ := (P.rescaledLSDA hp hθ hθ').1
  have hp₀ : 0 < p := by linarith
  have hθ₀ : 0 < θ := (div_pos (by norm_num : (0 : ℝ) < 2) hp₀).trans_le hθ
  let s := scalingExponent p (bulkExponent p θ)
  let r := max (5 / 6 : ℝ) (1 - 1 / (3 + 9 * θ))
  have hs : s = min (1 / 6) (1 / (3 + 9 * θ)) := scalingExponent_bulk hp₀ hθ₀
  have hkin : 1 / 3 + s ≤ r := by
    have h := hs.le.trans (min_le_left ..)
    have hr : (5 / 6 : ℝ) ≤ r := le_max_left ..
    linarith
  have hbulk : 1 - s ≤ r := by
    rw [hs]
    rcases le_total (1 / 6 : ℝ) (1 / (3 + 9 * θ)) with h | h
    · rw [min_eq_left h, show (1 - 1 / 6 : ℝ) = 5 / 6 by norm_num]
      exact le_max_left ..
    · rw [min_eq_right h]
      exact le_max_right ..
  let kinetic := (2 * C) * ∫ x, matrixGradNorm S x ^ 2
  let bulk := (∫ x, D.charge x + D.charge x ^ 2) + C * ∫ x, matrixGradNorm T x ^ p
  have hk : 0 ≤ kinetic := mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _)
  have hb : 0 ≤ bulk := add_nonneg (integral_nonneg fun x => add_nonneg (D.charge_nonneg x) (sq_nonneg _))
    (mul_nonneg hC.le (integral_nonneg fun x => Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  apply isBigO_iff.mpr
  refine ⟨kinetic + bulk, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ N) _)]
  have hkN := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hkin) hk
  have hbN := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hbulk) hb
  calc
    _ ≤ _ := bound D S T trivial reg N hN
    _ = kinetic * N ^ (1 / 3 + s) + bulk * N ^ (1 - s) := by
      dsimp only [kinetic, bulk, s]
      ring
    _ ≤ (kinetic + bulk) * N ^ r := by simpa only [add_mul] using add_le_add hkN hbN

open Asymptotics Filter in
/-- For θ < 1 the LSDA error grows strictly more slowly than the LLS scale N^(11/12). -/
theorem CoulombModelInputs.rescaledNoncollinearLSDA_improvesLLS (P : CoulombModelInputs μ ι η) {p θ : ℝ}
    (hp : 3 < p) (hθ : 2 / p ≤ θ) (hθ' : θ < 1) (D : Density) (S T : MatrixGradient)
    (reg : DensityRegular D p θ S T) :
    (fun N : ℝ => energy (D.particleScale N).matrix - N * ∫ x, (referenceEnergies energy η).ueg (D.matrix x))
      =o[atTop] (fun N : ℝ => N ^ (11 / 12 : ℝ)) := by
  have hθ₀ : 0 < θ := (div_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < p)).trans_le hθ
  let r := max (5 / 6 : ℝ) (1 - 1 / (3 + 9 * θ))
  have hfrac : (1 / 12 : ℝ) < 1 / (3 + 9 * θ) := (lt_div_iff₀ (by linarith)).2 (by linarith)
  have hr : r < 11 / 12 := max_lt (by norm_num) (by linarith)
  apply (P.rescaledNoncollinearLSDA hp hθ hθ' D S T reg).trans_isLittleO
  apply (isLittleO_iff_tendsto' ?_).2
  · apply (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    exact (congrArg (N ^ ·) (neg_sub (11 / 12) r)).trans (Real.rpow_sub hN _ _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN hzero
    exact ((Real.rpow_pos_of_pos hN _).ne' hzero).elim

open Asymptotics Filter in
/-- The LSDA remainder is of order N^(5/6) in either sharp-exponent regime. -/
theorem CoulombModelInputs.sharp_rescaledLSDA (P : CoulombModelInputs μ ι η) {p θ : ℝ}
    (hp : 3 < p) (hθ : 2/p ≤ θ) (hθ' : θ < 1) (D : Density) (S T : MatrixGradient)
    (reg : DensityRegular D p θ S T)
    (sharp : θ ≤ 1/3 ∨ ∃ ν : ℝ, 0 < ν ∧ ν ≤ 1/2 ∧ MinorityBound ν D ∧ θ*p ≤ 1+p/3) :
    (fun N : ℝ => energy (D.particleScale N).matrix - N*∫ x, (referenceEnergies energy η).ueg (D.matrix x))
      =O[atTop] (fun N : ℝ => N^(5/6:ℝ)) :=
  sharp_rescaledLSDA_of_mainTSGA P.tsgaFinite hp hθ hθ' D S T reg sharp

/-- Particle scaling for a slowly varying local wavevector following Theorem 3.3. The first
estimate uses the global root, and the second needs only its weighted
gradient on the active set. -/
theorem CoulombModelInputs.rescaledSpiral (P : CoulombModelInputs μ ι η) {p : ℝ} (hp : 3 < p) :
    let F := referenceEnergies energy η
    (∃ A > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p*θ →
      ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
        IsMatrixGradientOn Set.univ (D.power (1/p)) G → MemLp (matrixGradNorm G) (ENNReal.ofReal p) →
        PhaseAdmissible D p φ G → ParticleSpiralEstimate F D φ S T G p A (∫ x, PhaseLocalization.rootPower G p x)) ∧
    (∀ θ : ℝ, 0 < θ → θ ≤ 1/3 → 2 ≤ p*θ → ∃ A > 0,
      ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
        PhaseAdmissible D p φ G → ParticleSpiralEstimate F D φ S T G p A 0) :=
  ⟨P.tsgaFinite.particle_spiral_sharp hp, fun _ hθ hle hpθ => P.tsgaFinite.particle_spiral_general hp hθ hle hpθ⟩

/-- Corollary 4.7 with the Lieb–Oxford coefficient of the model. -/
theorem FiniteEnergyInputs.fisher_lower_bound (H : FiniteEnergyInputs)
    (chain : RankOneRootChain) (convex : CountableFisherConvexity) (marg : OneBodyMarginals)
    {D : Density} {S : MatrixGradient} (hD : SqrtRegular D S) :
    sqrtKinetic S / 2 - H.loCoeff * chargeMoment D (4/3) ≤ energy D.matrix := by
  have lower := H.lower_bound (cLT := 0) (fun γ _ _ => by simpa using γ.kinetic_nonneg)
    chain convex marg hD
  exact (sub_le_sub_right (le_max_right ..) _).trans lower

/-- An additional finite-system bound with a Lieb–Thirring term and any
Lieb–Oxford coefficient at most 1.64. -/
theorem FiniteEnergyInputs.lower_bound_164 (H : FiniteEnergyInputs) {cLT : ℝ}
    (lo : H.loCoeff ≤ 1.64)
    (ltBound : ∀ (γ : OneBody) (D : Density), γ.matrixDensity =ᵐ[volume] D.matrix →
      (2:ℝ)^(-(2/3:ℝ))*cLT*chargeMoment D (5/3) ≤ γ.kinetic)
    (chain : RankOneRootChain) (convex : CountableFisherConvexity) (marg : OneBodyMarginals)
    {D : Density} {S : MatrixGradient} (hD : SqrtRegular D S) :
    max ((2:ℝ)^(-(2/3:ℝ))*cLT*chargeMoment D (5/3)) (sqrtKinetic S/2) -
      1.64*chargeMoment D (4/3) ≤ energy D.matrix := by
  apply le_trans _ (H.lower_bound ltBound chain convex marg hD)
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right lo
    (integral_nonneg fun x => Real.rpow_nonneg (D.charge_nonneg x) _)) _

end TSGA.ManyBody
