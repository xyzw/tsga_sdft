import TSGA.ActualLargeTileTrials
import TSGA.ActualTileBall

/-! # Rough Coulomb comparison on the physical comparison ball -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization Metric

/-- The bulk part of the rough tile estimate samples only the ball of radius
three cell lengths. This bound works for both cutoffs at every center. -/
theorem FiniteEnergyInputs.actual_large_difference_ball (H : FiniteEnergyInputs)
    (product : WeakScalarMatrixProduct) (chain : WeakPhaseProduct) (borel : LevyLiebBorel)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100)) (sob : SobolevDifferenceQuotients)
    (side : CutoffSide) {ε K p θ : ℝ} (he : 0 < ε) (he' : ε < 1) (rate : FiniteRateTiling energy η K)
    {D : Density} {φ : Phase} {S T : MatrixGradient} (reg : DensityRegular D p θ S T) (hφ : φ.Regular p)
    (phase : Integrable fun x => D.charge x*‖φ.grad x‖^2)
    (P : TileProfile) (profile : P.cutoff = (actualTiles O frames η side he he').cutoffProfile) (c : Position) :
    let tiles := actualTiles O frames η side he he'
    let F := referenceEnergies energy η
    |tiles.energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c| ≤
      2*(roughTrialCoeff H K*(192*ε^3*∫ x in closedBall c (3*ε⁻¹), roughTileDensity D φ x)) +
        actualLargeKinetic H O frames η side he he' D S c := by
  intro tiles F
  have sr : SqrtRegular D S := ⟨reg.charge_L1,reg.sqrt_gradient,reg.sqrt_L2⟩
  have base := tileDensityDomain_of_regular sr reg.aemeasurable_matrix reg.charge_L2.integrable_sq
  have integ : Integrable (roughTileDensity D φ) := (base.lo.add base.tf).add phase
  have pos (x) : 0 ≤ roughTileDensity D φ x := add_nonneg
    (add_nonneg (Real.rpow_nonneg (D.charge_nonneg x) _) (Real.rpow_nonneg (D.charge_nonneg x) _))
    (mul_nonneg (D.charge_nonneg x) (sq_nonneg _))
  have ball := (actual_cutoff_average_ball O frames η support side he he' integ (ae_of_all _ pos) c).2
  rw [← profile] at ball
  have coeff : 0 ≤ roughTrialCoeff H K := add_nonneg
    (add_nonneg (zero_le_one.trans rate.one_le) H.lo_nonneg) (mul_nonneg (by norm_num) H.interiorConstant_nonneg)
  exact (H.actual_large_difference product chain borel O frames η sob side he he' rate reg hφ phase P profile c).trans
    (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ball coeff) (by norm_num : (0:ℝ) ≤ 2)) le_rfl)

end TSGA.ManyBody
