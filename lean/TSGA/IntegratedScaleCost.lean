import TSGA.LocalErrorTerms

/-! # Integrated mass and gradient errors at the physical tile scale -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization

/-- The four terms left by the small- and large-oscillation comparisons
after integration over tile centers. -/
def integratedScaleCost (mode : BulkRegime) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) (p θ ε : ℝ) : ℝ :=
  ε*(∫ x, massDensity D φ x) + (∫ x, kineticDensity S x)/ε +
    (∫ x, bulkDensity mode T G p x)/ε^(mode.exponent p θ) +
    (∫ x, phaseDensity D φ G p x)/ε^(2*p-1)

theorem mass_kinetic_le_integratedScaleCost (mode : BulkRegime) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) (p θ : ℝ) {ε : ℝ} (he : 0 < ε) :
    ε*(∫ x, massDensity D φ x) + (∫ x, kineticDensity S x)/ε ≤
      integratedScaleCost mode D φ S T G p θ ε := by
  apply (le_add_of_nonneg_right (div_nonneg (integral_nonneg (bulkDensity_nonneg mode T G p))
    (Real.rpow_nonneg he.le _))).trans
  exact le_add_of_nonneg_right (div_nonneg (integral_nonneg (phaseDensity_nonneg D φ G p))
    (Real.rpow_nonneg he.le _))

theorem integratedScaleCost_nonneg (mode : BulkRegime) (D : Density) (φ : Phase)
    (S T G : MatrixGradient) (p θ : ℝ) {ε : ℝ} (he : 0 < ε) :
    0 ≤ integratedScaleCost mode D φ S T G p θ ε :=
  (add_nonneg (mul_nonneg he.le (integral_nonneg (massDensity_nonneg D φ)))
    (div_nonneg (integral_nonneg fun _ => sq_nonneg _) he.le)).trans
      (mass_kinetic_le_integratedScaleCost mode D φ S T G p θ he)

end TSGA.ManyBody
