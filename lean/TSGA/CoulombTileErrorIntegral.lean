import TSGA.IntegratedScaleCost
import TSGA.SmallBallIntegratedError
import TSGA.ActualLargeTileTrials

/-! # Integrated error for the two physical tile families -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW PhaseLocalization

/-- The same coefficient controls both sides after integration in the center. -/
def tileErrorCoefficient (H : FiniteEnergyInputs) (p C a A : ℝ) : ℝ :=
  A*(1+tileMorreyCoefficient p C) + 4*H.interiorConstant + 8*H.interiorConstant*a

theorem integral_actual_tile_error (H : FiniteEnergyInputs) (O : TileOrientationLaw)
    (frames : TileFrameMeasurable O) (η : Mollifier) (sob : SobolevDifferenceQuotients)
    {a C A ε p θ ν : ℝ} (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hp : 0 < p) (he : 0 < ε) (hle : ε < 1) (side : CutoffSide)
    {D : Density} {φ : Phase} {S T G : MatrixGradient} {mode : BulkRegime}
    (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G) (hr : RegimeHyp mode ν D G p) :
    let E := integratedScaleCost mode D φ S T G p θ ε
    let err := fun c => A*smallBallErrorDensity mode D φ S T G p θ ε C c +
      actualLargeKinetic H O frames η side he hle D S c
    Integrable err ∧ (∫ c, err c) ≤ tileErrorCoefficient H p C a A*E := by
  intro E err
  let m := ∫ x, massDensity D φ x
  let k := ∫ x, kineticDensity S x
  let u := ∫ x, bulkDensity mode T G p x
  let v := ∫ x, phaseDensity D φ G p x
  let b := mode.exponent p θ
  let h := 2*p-1
  let B := tileMorreyCoefficient p C
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (ballVolume_pos zero_lt_one).le
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)) hC
  have hU : 0 ≤ H.interiorConstant := H.interiorConstant_nonneg
  have hm : 0 ≤ m := integral_nonneg (massDensity_nonneg D φ)
  have hk : 0 ≤ k := integral_nonneg fun x => sq_nonneg (matrixGradNorm S x)
  have hu : 0 ≤ u/ε^b := div_nonneg (integral_nonneg (bulkDensity_nonneg mode T G p)) (Real.rpow_nonneg he.le _)
  have hv : 0 ≤ v/ε^h := div_nonneg (integral_nonneg (phaseDensity_nonneg D φ G p)) (Real.rpow_nonneg he.le _)
  have hmass := mul_nonneg he.le hm
  have hkin := div_nonneg hk he.le
  have total : E = ε*m + k/ε + u/ε^b + v/ε^h := rfl
  have mass_le : ε*m ≤ E := by rw [total]; linarith
  have kin_le : k/ε ≤ E := by rw [total]; linarith
  have bulk_le : u/ε^b ≤ E := by rw [total]; linarith
  have sm : ε*m + k/ε + B*u/ε^b + v/ε^h ≤ (1+B)*E := by
    rw [mul_div_assoc B u,add_mul,one_mul]
    linarith only [mul_le_mul_of_nonneg_left bulk_le hB,total,hu]
  have charge : (∫ x, D.charge x) ≤ m := by
    apply integral_mono reg.charge_L1 (massDensity_integrable reg phase)
    intro x
    unfold massDensity
    linarith only [sq_nonneg (D.charge x),mul_nonneg (D.charge_nonneg x) (sq_nonneg ‖φ.grad x‖)]
  have kc : side.mass ε*k ≤ E := by
    have side_le : side.mass ε ≤ 1 := by
      cases side with
      | lower => exact le_rfl
      | upper => exact pow_le_one₀ (sub_nonneg.mpr hle.le) (by linarith)
    have kk : k ≤ k/ε := (le_div_iff₀ he).2 (mul_le_of_le_one_right hk hle.le)
    exact (mul_le_of_le_one_left hk side_le).trans (kk.trans kin_le)
  have mc := (mul_le_mul_of_nonneg_left charge he.le).trans mass_le
  obtain ⟨si,se⟩ := integral_smallBallErrorDensity C hp he reg phase hr
  obtain ⟨ki,ke⟩ := integral_actualLargeKinetic H O frames η sob ha area side he hle
    (show SqrtRegular D S from ⟨reg.charge_L1,reg.sqrt_gradient,reg.sqrt_L2⟩)
  refine ⟨(si.const_mul A).add ki,?_⟩
  dsimp only [err]
  rw [integral_add (si.const_mul A) ki,integral_const_mul,se]
  apply (add_le_add (mul_le_mul_of_nonneg_left sm hA) ke).trans
  unfold tileErrorCoefficient
  change A*((1+B)*E)+(4*H.interiorConstant*(side.mass ε*k)+
    2*H.interiorConstant*((4*a*ε)*(∫ x, D.charge x))) ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left kc (by positivity : 0 ≤ 4*H.interiorConstant),
    mul_le_mul_of_nonneg_left mc (by positivity : 0 ≤ 8*H.interiorConstant*a)]

end TSGA.ManyBody
