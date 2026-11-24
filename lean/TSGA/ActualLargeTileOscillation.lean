import TSGA.ActualLargeTileBall
import TSGA.PhaseTile

/-! # The bulk and spiral terms of an actual large-oscillation tile -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization PhaseLocalization Set Metric

/-- Young's inequality on the large branch, integrated against the actual
charge throughout the comparison ball. The gradient on the right of the
Morrey inequality is normalized per unit volume. -/
private theorem large_ball_bulk (mode : BulkRegime) {D : Density} {p θ ε r ω κ g : ℝ}
    {Ω : Set Position} (hΩ : volume Ω ≠ ⊤)
    (hp : 3 < p) (hpθ : 2 ≤ p*θ) (he : 0 < ε) (hω : 0 ≤ ω) (hκ : 0 < κ) (hg : 0 ≤ g)
    (charge : ∀ x ∈ Ω, D.charge x ≤ r) (large : κ*r^(mode.densityPower p θ) ≤ ω)
    (morrey : ω^p ≤ ε^(-p)*g) (meas : MeasurableSet Ω)
    (hi : Integrable (fun x => D.charge x^(4/3:ℝ) + D.charge x^(5/3:ℝ)))
    (hm : Integrable (fun x => D.charge x + D.charge x^2)) :
    (∫ x in Ω, D.charge x^(4/3:ℝ) + D.charge x^(5/3:ℝ)) ≤
      2*(ε*(∫ x in Ω, D.charge x + D.charge x^2) + volume.real Ω*(g/ε^(mode.exponent p θ))) /
        κ^(mode.holderPower p θ) := by
  let b := g/ε^(mode.exponent p θ)
  let a := κ^(mode.holderPower p θ)
  have ib : IntegrableOn (fun _ : Position => b) Ω := integrableOn_const hΩ
  have pt (x : Position) (hx : x ∈ Ω) : (D.charge x^(4/3:ℝ)+D.charge x^(5/3:ℝ))*a ≤ 2*(ε*(D.charge x+D.charge x^2)+b) := by
    simpa only [one_mul,mul_one,a,b] using
      (mode.largeOscillation_bound (V := 1) hp hpθ he zero_lt_one (D.charge_nonneg x) (charge x hx)
        hω hg hκ large (by simpa only [one_mul] using morrey))
  have h := setIntegral_mono_on (hi.mul_const a).integrableOn (((hm.integrableOn.const_mul ε).add ib).const_mul 2) meas pt
  change (∫ x in Ω, (D.charge x^(4/3:ℝ)+D.charge x^(5/3:ℝ))*a) ≤ ∫ x in Ω, 2*(ε*(D.charge x+D.charge x^2)+b) at h
  rw [integral_mul_const,integral_const_mul,integral_add (hm.integrableOn.const_mul ε) ib,
    integral_const_mul,setIntegral_const,smul_eq_mul] at h
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hκ _)).2 h

/-- The rough density integrated on the comparison ball, before applying
either of the two physical cutoffs. -/
theorem roughTileDensity_ball_of_oscillation (mode : BulkRegime) {ε p θ κ ω b L : ℝ}
    (he : 0 < ε) (hle : ε < 1) {D : Density} {φ : Phase} {S T G : MatrixGradient}
    (reg : DensityRegular D p θ S T) (hφ : PhaseAdmissible D p φ G)
    (hp : 3 < p) (hpθ : 2 ≤ p*θ) (hκ : 0 < κ) (hω : 0 ≤ ω) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (c : Position) (data : LargeOscillationData (closedBall c (3*ε⁻¹)) D φ G p ε L)
    (large : κ*data.radiusDensity^(mode.densityPower p θ) ≤ ω)
    (morrey : ω^p ≤ ε^(-p)*(b*ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c)) :
    let Ω := closedBall c (3*ε⁻¹)
    let g := b*ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c
    let bulk := 2*(ε*(∫ x in Ω, D.charge x + D.charge x^2) + volume.real Ω*(g/ε^(mode.exponent p θ))) /
      κ^(mode.holderPower p θ)
    let phase := (2:ℝ)^p * (ε*(∫ x in Ω, D.charge x) + (2:ℝ)^p*L^2/ε^(2*p-1)*
      ((∫ x in Ω, weightedRoot φ G p x) + ∫ x in Ω, D.charge x * φ.hessianNorm x^p))
    (∫ x in Ω, roughTileDensity D φ x) ≤ bulk + phase := by
  intro Ω g bulk phase
  have sr : SqrtRegular D S := ⟨reg.charge_L1,reg.sqrt_gradient,reg.sqrt_L2⟩
  have dom := tileDensityDomain_of_regular sr reg.aemeasurable_matrix reg.charge_L2.integrable_sq
  have hi : Integrable (fun x => D.charge x^(4/3:ℝ) + D.charge x^(5/3:ℝ)) := dom.lo.add dom.tf
  have h := large_ball_bulk mode (D := D) (Ω := Ω) (isCompact_closedBall c (3*ε⁻¹)).measure_lt_top.ne hp hpθ he hω hκ
    (mul_nonneg hb (ballAverage_nonnegative _ (bulkDensity_nonneg mode T G p) c)) data.charge_le large
    morrey measurableSet_closedBall hi (reg.charge_L1.add reg.charge_L2.integrable_sq)
  have ph := largeOscillation_kinetic (isCompact_closedBall c (3*ε⁻¹)) (by linarith : 1 ≤ p) he hle.le hL
    reg.charge_L1 hφ data
  change (∫ x in Ω, (D.charge x^(4/3:ℝ) + D.charge x^(5/3:ℝ)) + D.charge x*‖φ.grad x‖^2) ≤ _
  rw [integral_add hi.integrableOn hφ.kinetic.integrableOn]
  exact add_le_add h ph

/-- On a large-oscillation ball the rough feasible-state bound uses the
density-power Morrey estimate and the truncated phase-gradient product
estimate. The remaining kinetic cost is the explicit averaged taper cost. -/
theorem FiniteEnergyInputs.actual_large_oscillation (H : FiniteEnergyInputs)
    (product : WeakScalarMatrixProduct) (chain : WeakPhaseProduct) (borel : LevyLiebBorel)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100)) (sob : SobolevDifferenceQuotients)
    (mode : BulkRegime) (side : CutoffSide) {ε K p θ κ ω b L : ℝ} (he : 0 < ε) (hle : ε < 1)
    (rate : FiniteRateTiling energy η K) {D : Density} {φ : Phase} {S T G : MatrixGradient}
    (reg : DensityRegular D p θ S T) (hφ : PhaseAdmissible D p φ G)
    (hp : 3 < p) (hpθ : 2 ≤ p*θ) (hκ : 0 < κ) (hω : 0 ≤ ω) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (P : TileProfile) (profile : P.cutoff = (actualTiles O frames η side he hle).cutoffProfile)
    (c : Position) (data : LargeOscillationData (closedBall c (3*ε⁻¹)) D φ G p ε L)
    (large : κ*data.radiusDensity^(mode.densityPower p θ) ≤ ω)
    (morrey : ω^p ≤ ε^(-p)*(b*ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c)) :
    let Ω := closedBall c (3*ε⁻¹)
    let F := referenceEnergies energy η
    let tiles := actualTiles O frames η side he hle
    let g := b*ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c
    let bulk := 2*(ε*(∫ x in Ω, D.charge x + D.charge x^2) + volume.real Ω*(g/ε^(mode.exponent p θ))) /
      κ^(mode.holderPower p θ)
    let phase := (2:ℝ)^p * (ε*(∫ x in Ω, D.charge x) + (2:ℝ)^p*L^2/ε^(2*p-1)*
      ((∫ x in Ω, weightedRoot φ G p x) + ∫ x in Ω, D.charge x * φ.hessianNorm x^p))
    |tiles.energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c| ≤
      2*(roughTrialCoeff H K*(192*ε^3*(bulk+phase))) + actualLargeKinetic H O frames η side he hle D S c := by
  intro Ω F tiles g bulk phase
  have total := roughTileDensity_ball_of_oscillation mode he hle reg hφ hp hpθ hκ hω hb hL c data large morrey
  have coeff : 0 ≤ roughTrialCoeff H K := add_nonneg
    (add_nonneg (zero_le_one.trans rate.one_le) H.lo_nonneg) (mul_nonneg (by norm_num) H.interiorConstant_nonneg)
  apply (H.actual_large_difference_ball product chain borel O frames η support sob side he hle rate reg hφ.regular
    hφ.kinetic P profile c).trans
  exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left total (by positivity : 0 ≤ 192*ε^3)) coeff) (by norm_num : (0:ℝ) ≤ 2)) le_rfl

end TSGA.ManyBody
