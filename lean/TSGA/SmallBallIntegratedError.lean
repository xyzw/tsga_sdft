import TSGA.SmallBallErrorDensity

/-! # Integrating the small-ball error over all tile centers -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization

/-- Each normalized comparison-ball average has spatial integral equal to the
integral of its density. The four coefficients are preserved in the center
integration, in all three bulk regimes. -/
theorem integral_smallBallErrorDensity {D : Density} {φ : Phase} {S T G : MatrixGradient}
    {mode : BulkRegime} {p θ ν ε : ℝ} (C : ℝ) (hp : 0 < p) (he : 0 < ε)
    (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G)
    (hr : RegimeHyp mode ν D G p) :
    Integrable (smallBallErrorDensity mode D φ S T G p θ ε C) ∧
    (∫ c, smallBallErrorDensity mode D φ S T G p θ ε C c) =
      ε*(∫ x, massDensity D φ x) + (∫ x, kineticDensity S x)/ε +
      tileMorreyCoefficient p C*(∫ x, bulkDensity mode T G p x)/ε^(mode.exponent p θ) +
      (∫ x, phaseDensity D φ G p x)/ε^(2*p-1) := by
  let R := 3*ε⁻¹
  have hR : 0 < R := mul_pos (by norm_num) (inv_pos.mpr he)
  have hm := massDensity_integrable reg phase
  have hk := kineticDensity_integrable reg
  have hb := bulkDensity_integrable hp reg hr
  have hf := phaseDensity_integrable phase
  have m := (ballAverage_integrable R hm).const_mul ε
  have k := (ballAverage_integrable R hk).div_const ε
  have b := ((ballAverage_integrable R hb).const_mul (tileMorreyCoefficient p C)).div_const (ε^(mode.exponent p θ))
  have f := (ballAverage_integrable R hf).div_const (ε^(2*p-1))
  have mk : Integrable (fun c => ε*ballAverage R (massDensity D φ) c + ballAverage R (kineticDensity S) c/ε) := m.add k
  have mkb : Integrable (fun c => ε*ballAverage R (massDensity D φ) c + ballAverage R (kineticDensity S) c/ε +
      tileMorreyCoefficient p C*ballAverage R (bulkDensity mode T G p) c/ε^(mode.exponent p θ)) := mk.add b
  refine ⟨mkb.add f, ?_⟩
  change (∫ c, ε*ballAverage R (massDensity D φ) c + ballAverage R (kineticDensity S) c/ε +
    tileMorreyCoefficient p C*ballAverage R (bulkDensity mode T G p) c/ε^(mode.exponent p θ) +
    ballAverage R (phaseDensity D φ G p) c/ε^(2*p-1)) = _
  rw [integral_add mkb f, integral_add mk b, integral_add m k,
    integral_const_mul, integral_div, integral_div, integral_div, integral_const_mul,
    integral_ballAverage hR hm, integral_ballAverage hR hk, integral_ballAverage hR hb,
    integral_ballAverage hR hf]

end TSGA.ManyBody
