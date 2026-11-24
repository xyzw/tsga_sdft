import TSGA.ActualLargeTileOscillation
import TSGA.BallOscillationThreshold
import TSGA.BallDensityTransfer
import TSGA.BallTruncatedGradient

/-! # Large-oscillation tiles for a Sobolev spin density

The essential oscillation is tested on the input density. A continuous
representative supplies the extremal values and weak-gradient estimates on
the closed comparison ball. All terms in the resulting Coulomb estimate
are evaluated on the input density.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Metric Set

/-- The factor from the three-dimensional ball of radius three in tile units. -/
def tileMorreyCoefficient (p C : ℝ) : ℝ := ballVolume 1 * (3 : ℝ)^p * C

/-- A common constant for the scalar Morrey estimate, the truncated product
and the active-ball estimate. It is independent of the density and the tile. -/
def largeBallConstant (mode : BulkRegime) (p θ κ C : ℝ) : ℝ :=
  let B := tileMorreyCoefficient p C
  max 1 (max B (max ((4*p)^p) ((mode.densityPower p θ*p/κ)^p * B)))

private theorem continuous_charge {N : Density} (hc : Continuous N.matrix) :
    Continuous N.charge := by
  unfold Density.charge Matrix.trace
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).comp ((continuous_apply i).comp hc)

private theorem continuous_truncation {N : Density} {φ : Phase} {p ε : ℝ}
    (hp : 0 < p) (hc : Continuous N.charge) (hφ : φ.Regular p) :
    Continuous (truncatedDensity N φ p ε) := by
  unfold truncatedDensity truncatedSpeed
  exact ((Real.continuous_rpow_const (by positivity)).comp hc).mul
    (continuous_const.max (((Real.continuous_rpow_const (by positivity)).comp hφ.continuous_grad.norm).sub continuous_const))

private theorem mode_morrey_pair {p θ C ν : ℝ} (M : MatrixSobolevMorrey p C)
    (mode : BulkRegime) (hp : 3 < p) (hpθ : 2 ≤ p*θ) (hC : 0 ≤ C)
    {N : Density} {S T G : MatrixGradient} (reg : DensityRegular N p θ S T)
    (hr : RegimeHyp mode ν N G p) (continuous : ∀ a : ℝ, 0 < a → Continuous (N.power a))
    {c : Position} {R : ℝ} (hR : 0 < R) {x y : Position}
    (hx : x ∈ closedBall c R) (hy : y ∈ closedBall c R) :
    hilbertSchmidt (N.power (mode.densityPower p θ) x - N.power (mode.densityPower p θ) y)^p ≤
      C * R^(p-3) * ∫ z in closedBall c R, bulkDensity mode T G p z := by
  have hp₀ : 0 < p := by linarith
  have hθ : 0 < θ := pos_of_mul_pos_right (by linarith : 0 < p*θ) hp₀.le
  cases mode with
  | general | minority => exact M.theta_pair hp reg (continuous θ hθ) hR x hx y hy
  | globalRoot =>
    apply (M.global_pair hp hr.1 hr.2 (continuous (1/p) (one_div_pos.mpr hp₀)) hR x hx y hy).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg hR.le _))
    have hT := rootPower_integrable hp₀ reg.theta_Lp
    have hG := rootPower_integrable hp₀ hr.2
    apply setIntegral_mono hG.integrableOn (hT.add hG).integrableOn
    exact fun z => le_add_of_nonneg_left (rootPower_nonneg T p z)

/-- Failure of the essential small-oscillation condition produces all inputs
to the bulk and phase estimates on the continuous representative. -/
theorem regular_large_ball {p θ κ C ν ε : ℝ} (M : MatrixSobolevMorrey p C)
    (calcRules : TruncationSobolevCalculus) (mode : BulkRegime)
    (hp : 3 < p) (hpθ : 2 ≤ p*θ) (hκ : 0 < κ) (hC : 0 ≤ C) (he : 0 < ε)
    {D N : Density} {φ : Phase} {S T G : MatrixGradient}
    (e : N.matrix =ᵐ[volume] D.matrix) (hc : Continuous N.matrix)
    (powers : ∀ a : ℝ, 0 < a → Continuous (N.power a))
    (reg : DensityRegular N p θ S T) (hφ : PhaseAdmissible N p φ G)
    (hr : RegimeHyp mode ν N G p) (c : Position)
    (large : ¬ SmallPowerOscillation D (mode.densityPower p θ) κ (3*ε⁻¹) c) :
    let B := tileMorreyCoefficient p C
    let L := largeBallConstant mode p θ κ C
    ∃ ω : ℝ, ∃ data : LargeOscillationData (closedBall c (3*ε⁻¹)) N φ G p ε L,
      0 ≤ ω ∧ κ * data.radiusDensity^(mode.densityPower p θ) ≤ ω ∧
      ω^p ≤ ε^(-p) * (B * ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c) := by
  classical
  intro B L
  let R := 3*ε⁻¹
  let Ω := closedBall c R
  let u := mode.densityPower p θ
  have hp₀ : 0 < p := by linarith
  have hu := mode.root_le_densityPower hp₀ hpθ
  have hR : 0 < R := mul_pos (by norm_num) (inv_pos.mpr he)
  have hK : IsCompact Ω := isCompact_closedBall c R
  have hcharge := continuous_charge hc
  obtain ⟨z, hz, hmax, charge⟩ := exists_charge_max_on_ball (c := c) e hc hR
  have failed := (smallPowerOscillation_iff_closedBall e hc (powers u ((one_div_pos.mpr hp₀).trans_le hu)) hR).not.mp large
  push Not at failed
  obtain ⟨x, hx, y, hy, hxy⟩ := failed
  let ω := hilbertSchmidt (N.power u x - N.power u y)
  have witness : κ * N.charge z^u ≤ ω := by simpa only [hmax] using hxy.le
  have osc := mode_morrey_pair M mode hp hpθ hC reg hr powers hR hx hy
  have normOsc := tile_ball_morrey_average he c (tile_ball_morrey_scale he c osc)
  have ctr := continuous_truncation (ε := ε) hp₀ hcharge hφ.regular
  obtain ⟨m, hm, maximal⟩ := hK.exists_isMaxOn ⟨z, hz⟩ ctr.continuousOn
  obtain ⟨Z, weak, lp, cost⟩ := truncatedDensity_gradient (ε := ε) calcRules hp he hφ hcharge
  have scale_le : B ≤ L := (le_max_left ..).trans (le_max_right ..)
  have product_le : (4*p)^p ≤ L :=
    (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have active_le : (u*p/κ)^p * B ≤ L :=
    (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  have relax {a I : ℝ} (ha : a ≤ L) (hi : 0 ≤ I) :
      a*ε^(-p)*I ≤ L*ε^(-p)*I :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg he.le _)) hi
  refine ⟨ω, {
    radiusDensity := N.charge z
    charge_le := charge
    peakAt := m
    peak_mem := hm
    peak_max := fun _ ht => maximal ht
    gradient := Z
    weak_gradient := weak _ isOpen_interior
    morrey := ?_
    product_rule := ?_
    active_morrey := ?_ }, Real.sqrt_nonneg _, witness, normOsc⟩
  · intro v hv w hw
    have q := M.scalar_pair hp _ Z ctr c R hR (weak _ isOpen_ball) (lp.restrict _) v hv w hw
    exact (tile_ball_morrey_scale he c q).trans
      (relax scale_le (integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg (Z t)) _))
  · exact (cost Ω).trans (mul_le_mul_of_nonneg_right product_le
      (add_nonneg (integral_nonneg (weightedRoot_nonneg φ G p))
        (mul_nonneg (Real.rpow_nonneg he.le _)
          (integral_nonneg fun t => mul_nonneg (N.charge_nonneg t) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)))))
  · intro active
    have ha := large_oscillation_active_morrey hp₀ hu hκ hφ hK active charge
      ⟨x, hx, y, hy, witness⟩ (fun v hv w hw => tile_ball_morrey_scale he c
        (M.root_pair hp hφ.regular.isOpen_active hφ.root_regular (powers _ (one_div_pos.mpr hp₀))
          hR active v hv w hw))
    exact ⟨ha.1, ha.2.trans (relax active_le (integral_nonneg (rootPower_nonneg G p)))⟩

/-- Convert the manuscript's threshold for the θ power to the power used in
the bulk interpolation. Only the global-root estimate changes the threshold. -/
def bulkOscillationThreshold (mode : BulkRegime) (p θ κ : ℝ) : ℝ :=
  match mode with
  | .general | .minority => κ
  | .globalRoot => κ/(p*θ)

/-- The rough bulk and phase costs after evaluating the two Morrey estimates.
The separate kinetic term accounts for differentiating the actual taper. -/
def largeTileBallCost (mode : BulkRegime) (p θ κ ε C : ℝ) (c : Position)
    (D : Density) (φ : Phase) (T G : MatrixGradient) : ℝ :=
  let Ω := closedBall c (3*ε⁻¹)
  let g := tileMorreyCoefficient p C * ballAverage (3*ε⁻¹) (bulkDensity mode T G p) c
  let k := bulkOscillationThreshold mode p θ κ
  let L := largeBallConstant mode p θ k C
  let bulk := 2*(ε*(∫ x in Ω, D.charge x + D.charge x^2) + volume.real Ω*(g/ε^(mode.exponent p θ))) /
    k^(mode.holderPower p θ)
  let phase := (2:ℝ)^p * (ε*(∫ x in Ω, D.charge x) + (2:ℝ)^p*L^2/ε^(2*p-1)*
    ((∫ x in Ω, weightedRoot φ G p x) + ∫ x in Ω, D.charge x * φ.hessianNorm x^p))
  bulk + phase

private theorem largeTileBallCost_of_ae (mode : BulkRegime) (p θ κ ε C : ℝ) (c : Position)
    {N D : Density} (e : N.matrix =ᵐ[volume] D.matrix) (φ : Phase) (T G : MatrixGradient) :
    largeTileBallCost mode p θ κ ε C c N φ T G = largeTileBallCost mode p θ κ ε C c D φ T G := by
  let Ω := closedBall c (3*ε⁻¹)
  have fc : N.charge =ᵐ[volume.restrict Ω] D.charge := ae_restrict_of_ae (densityCharge_ae_congr e)
  have fm := integral_congr_ae (fc.mono fun x hx => congrArg (fun r : ℝ => r + r^2) hx)
  have fh := integral_congr_ae (fc.mono fun x hx => congrArg (· * φ.hessianNorm x^p) hx)
  dsimp only [largeTileBallCost]
  rw [fm, integral_congr_ae fc, fh]

/-- On a large ball for the manuscript's θ-power test, the rough density
of the original field is controlled by its bulk and phase error integrals. -/
theorem roughTileDensity_ball_of_regular {ε p θ κ C ν : ℝ} (M : MatrixSobolevMorrey p C)
    (calcRules : TruncationSobolevCalculus) (mode : BulkRegime) (hp : 3 < p)
    (hpθ : 2 ≤ p*θ) (hκ : 0 < κ) (hC : 0 ≤ C) (he : 0 < ε) (hle : ε < 1)
    {D : Density} {φ : Phase} {S T G : MatrixGradient} (reg : DensityRegular D p θ S T)
    (hφ : PhaseAdmissible D p φ G) (hr : RegimeHyp mode ν D G p) (c : Position)
    (large : ¬ SmallPowerOscillation D θ κ (3*ε⁻¹) c) :
    (∫ x in closedBall c (3*ε⁻¹), roughTileDensity D φ x) ≤
      largeTileBallCost mode p θ κ ε C c D φ T G := by
  let k := bulkOscillationThreshold mode p θ κ
  have hp₀ : 0 < p := by linarith
  have hθ : 0 < θ := pos_of_mul_pos_right (by linarith : 0 < p*θ) hp₀.le
  obtain ⟨N, e, cont, powers⟩ := M.density_representative hp hθ reg
  have regN := densityRegular_of_ae e.symm reg
  have phaseN := phaseAdmissible_of_ae e.symm hφ
  have hk : 0 < k := by
    cases mode <;> first | exact hκ | exact div_pos hκ (mul_pos hp₀ hθ)
  have threshold : ¬ SmallPowerOscillation D (mode.densityPower p θ) k (3*ε⁻¹) c := by
    cases mode with
    | general | minority => exact large
    | globalRoot =>
      exact fun small => large (smallPowerOscillation_of_root hp₀
        (BulkRegime.general.root_le_densityPower hp₀ hpθ) hκ e cont powers (by positivity) small)
  obtain ⟨ω, data, hω, witness, osc⟩ := regular_large_ball M calcRules mode hp hpθ hk hC he e cont
    powers regN phaseN (regimeHyp_of_ae e.symm hr) c threshold
  have hB : 0 ≤ tileMorreyCoefficient p C :=
    mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le (Real.rpow_nonneg (by norm_num) _)) hC
  have hL : 1 ≤ largeBallConstant mode p θ k C := le_max_left ..
  have bound := roughTileDensity_ball_of_oscillation mode he hle regN phaseN hp hpθ hk hω hB hL c data witness osc
  change (∫ x in closedBall c (3*ε⁻¹), roughTileDensity N φ x) ≤ largeTileBallCost mode p θ κ ε C c N φ T G at bound
  have eq : roughTileDensity N φ =ᵐ[volume] roughTileDensity D φ :=
    (densityCharge_ae_congr e).mono fun x hx =>
      congrArg (fun r : ℝ => r^(4/3:ℝ)+r^(5/3:ℝ)+r*‖φ.grad x‖^2) hx
  rwa [integral_congr_ae (ae_restrict_of_ae eq), largeTileBallCost_of_ae mode p θ κ ε C c e] at bound

/-- The actual Coulomb trial and its two-sided energy estimate on any ball
failing the θ-power oscillation test. Both tapers and all three bulk regimes
use the same classification. -/
theorem FiniteEnergyInputs.actual_large_oscillation_of_regular (H : FiniteEnergyInputs)
    (product : WeakScalarMatrixProduct) (chain : WeakPhaseProduct) (borel : LevyLiebBorel)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100)) (sob : SobolevDifferenceQuotients)
    (mode : BulkRegime) (side : CutoffSide) {ε K p θ κ C ν : ℝ} (he : 0 < ε) (hle : ε < 1)
    (rate : FiniteRateTiling energy η K) (M : MatrixSobolevMorrey p C) (hC : 0 ≤ C)
    (calcRules : TruncationSobolevCalculus) {D : Density} {φ : Phase} {S T G : MatrixGradient}
    (reg : DensityRegular D p θ S T) (hφ : PhaseAdmissible D p φ G) (hr : RegimeHyp mode ν D G p)
    (hp : 3 < p) (hpθ : 2 ≤ p*θ) (hκ : 0 < κ) (P : TileProfile)
    (profile : P.cutoff = (actualTiles O frames η side he hle).cutoffProfile) (c : Position)
    (large : ¬ SmallPowerOscillation D θ κ (3*ε⁻¹) c) :
    let tiles := actualTiles O frames η side he hle
    let F := referenceEnergies energy η
    let cost := fun z => 2*(roughTrialCoeff H K*(192*ε^3*largeTileBallCost mode p θ κ ε C z D φ T G)) +
      actualLargeKinetic H O frames η side he hle D S z
    Nonempty (LargeCoulombTrials H rate D φ tiles P (fun z => cost z - P.directCost z) c) ∧
      |tiles.energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c| ≤ cost c := by
  intro tiles F cost
  have hball := roughTileDensity_ball_of_regular M calcRules mode hp hpθ hκ hC he hle reg hφ hr c large
  have sr : SqrtRegular D S := ⟨reg.charge_L1, reg.sqrt_gradient, reg.sqrt_L2⟩
  have dom := tileDensityDomain_of_regular sr reg.aemeasurable_matrix reg.charge_L2.integrable_sq
  have hi : Integrable (roughTileDensity D φ) := (dom.lo.add dom.tf).add hφ.kinetic
  have hn (x : Position) : 0 ≤ roughTileDensity D φ x := by
    unfold roughTileDensity
    positivity [D.charge_nonneg x]
  have cut := (actual_cutoff_average_ball O frames η support side he hle hi (ae_of_all _ hn) c).2
  rw [← profile] at cut
  have hcut := cut.trans (mul_le_mul_of_nonneg_left hball (by positivity : 0 ≤ 192*ε^3))
  have coeff : 0 ≤ roughTrialCoeff H K := add_nonneg
    (add_nonneg (zero_le_one.trans rate.one_le) H.lo_nonneg) (mul_nonneg (by norm_num) H.interiorConstant_nonneg)
  have hcost : 2*(roughTrialCoeff H K*cutoffAverage P.cutoff (roughTileDensity D φ) c) +
      actualLargeKinetic H O frames η side he hle D S c ≤ cost c :=
    add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcut coeff) (by norm_num : (0:ℝ) ≤ 2)) le_rfl
  have trial := H.actual_large_trials product chain borel O frames η sob side he hle rate reg hφ.regular
    hφ.kinetic P profile (fun z => cost z-P.directCost z) c (by linarith only [hcost])
  obtain ⟨t⟩ := trial
  have rough := t.toRough
  refine ⟨⟨t⟩, (abs_sub _ _).trans ?_⟩
  have bound := rough.error_bound
  change _ ≤ P.directCost c + (cost c - P.directCost c) at bound
  linarith only [rough.finite, rough.gas, bound]

end TSGA.ManyBody
