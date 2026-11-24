import TSGA.IslandTrialAssembly
import TSGA.LevyLiebAttainment

/-! # Levy–Lieb minimizers in the Poisson island construction -/

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization

universe u

/-- Supply the minimizing background state for the island proof by Theorem 2.2.
The other operators and measurable-selection assumptions are those used to
construct and average the island trial states. -/
def IslandFockInputs.of_compactness {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (oneBody : FiniteEnergyInputs)
    (compact : FixedChargeCompactness) (tensor : DisjointFockTensorization)
    (barycenter : FockBarycenterRealization μ) (selection : FockEnergySelection μ)
    (fisher : FisherSobolevCalculus.{u})
    (restriction : ∀ (Γ : MixedState) (B : Density), SpatialFockRestriction Γ B)
    (coulomb_pos : ∀ f, Integrable (directKernel f f) pairVolume → 0 ≤ hartree f) :
    IslandFockInputs μ where
  tensor := tensor
  barycenter := barycenter
  selection := selection
  oneBody := oneBody
  fisher := fisher
  minimizer := fun _ _ regular _ => levyLieb_attained oneBody.construction oneBody.quasiFree compact regular
  restriction := restriction
  coulomb_pos := coulomb_pos

end TSGA.ManyBody
