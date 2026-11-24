import TSGA.CoulombTilingModel
import TSGA.CoulombDilationMeasure
import TSGA.CoulombUpperComparison

/-! # The SSW limit and finite tetrahedron rate from Coulomb localization

One state-level Graf–Schenker inequality supplies the three lower estimates.
One upper trial construction supplies the general-domain and finite-dilation
bounds. The same physical constrained search is used on both sides.
-/

noncomputable section
namespace TSGA.ManyBody

open SSW
open scoped ComplexOrder

/-- A single size threshold suffices simultaneously for all seven tiling
obligations, independently of the spin density and the wavevector. -/
theorem coulomb_finite_tiling_comparisons {η : Mollifier}
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (borel : LevyLiebBorel) (lower : CoulombLowerLocalization η) (upper : CoulombUpperLocalization η) :
    ∃ K₀ ≥ H.roughThreshold sob quant η, ∀ K ≥ K₀, CoulombTilingComparisons η K := by
  obtain ⟨L, _, hlo⟩ := lower.comparisons H sob
  have hi := coulomb_tileDilationIntegrable borel η H sob quant
  obtain ⟨U, _, hup⟩ := upper.dilation_comparison H sob quant (hi 0)
  let K₀ := max (H.roughThreshold sob quant η) (max L U)
  refine ⟨K₀,le_max_left _ _,?_⟩
  intro K hK
  have hL : L ≤ K := (le_max_left L U).trans ((le_max_right _ _).trans hK)
  have hU : U ≤ K := (le_max_right L U).trans ((le_max_right _ _).trans hK)
  obtain ⟨ht, hd, hI⟩ := hlo K hL
  exact {
    twoScale := fun M hM _ q => ht M hM q
    measurable := fun M _ _ q => coulomb_tetrahedronDilationMeasurable borel η M q
    lower := fun M hM _ q => hd M hM q
    upper := fun _ hM _ q => upper.domain_upper H sob quant (hi 0) hM q
    interior := hI
    dilation_integrable := hi K
    dilation := hup K hU }

/-- The Coulomb SSW theorem and its quantitative finite-size comparisons
at the same reference kernel, with the tiling constant chosen internally. -/
theorem coulomb_sswGas_and_rate {η : Mollifier} (H : FiniteEnergyInputs)
    (sob : SobolevDifferenceQuotients) (strong : SobolevDirectionalLimits)
    (borel : LevyLiebBorel) (lower : CoulombLowerLocalization η) (upper : CoulombUpperLocalization η) :
    SSWGasTheorem (referenceEnergies energy η) ∧ ∃ K, FiniteRateTiling energy η K := by
  obtain ⟨K,hK,h⟩ := coulomb_finite_tiling_comparisons H sob strong.toDifferenceBounds borel lower upper
  exact ⟨coulomb_sswGas_of_finite_tilings H sob strong hK (h K le_rfl),
    K, (h K le_rfl).rate H sob strong.toDifferenceBounds hK⟩

end TSGA.ManyBody
