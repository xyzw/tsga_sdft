import TSGA.CoulombCutoffArea
import TSGA.CoulombTransportModel
import TSGA.SobolevDirectionalLimits

/-! # Coulomb gas and TSGA from finite tilings

The uniform Coulomb trial bound gives the rough estimates for both
thermodynamic localization and the convergence rate. The remaining gas
inputs compare finite tiles or domains. The local TSGA trials enter only
after the homogeneous gas and its moduli have been constructed.
-/

noncomputable section
namespace TSGA.SSW

open scoped ComplexOrder

/-- At fixed charge and wavevector the two rough rate inequalities give
uniform constants for the energy and its cutoff error at every tile size. -/
theorem FiniteRateTiling.tileBounds {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (rate : FiniteRateTiling E η K) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    TileBounds (averagedTile E η M q) := by
  let ρ := M.trace.re
  let A := K * (ρ * ρ^(1/3 : ℝ))
  let B := max (K * (ρ * rateGrowth ρ q)) (K*ρ)
  have hK : 0 ≤ K := zero_le_one.trans rate.one_le
  have hρ : 0 ≤ ρ := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hA : 0 ≤ A := mul_nonneg hK (mul_nonneg hρ (Real.rpow_nonneg hρ _))
  have hB : 0 ≤ B := (mul_nonneg hK hρ).trans (le_max_right _ _)
  refine ⟨A,B,hA,hB,?_⟩
  intro ℓ δ hℓ hδ
  obtain ⟨hl,hu⟩ := rate.rough M hM q ℓ δ hℓ hδ
  refine ⟨by simpa only [A,ρ,neg_mul] using hl, ?_⟩
  calc
    averagedTile E η M q ℓ δ ≤ averagedTile E η M q ℓ δ + A := le_add_of_nonneg_right hA
    _ ≤ K * (ρ * rateGrowth ρ q + ρ/(ℓ*δ)) := hu
    _ = K * (ρ * rateGrowth ρ q) + (K*ρ)/(ℓ*δ) := by ring
    _ ≤ B + B/(ℓ*δ) := add_le_add (le_max_left _ _)
      (div_le_div_of_nonneg_right (le_max_right _ _) (mul_pos hℓ hδ).le)

end TSGA.SSW
namespace TSGA.ManyBody

open SSW TSGA.Localization
open scoped ComplexOrder

/-- Finite-energy comparisons used for the Coulomb thermodynamic limit and
its rate. Each field is evaluated on the original constrained search. -/
structure CoulombTilingComparisons (η : Mollifier) (K : ℝ) : Prop where
  twoScale : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position,
    TetrahedronTwoScale energy η M q
  measurable : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position,
    TetrahedronDilationMeasurable energy η M q
  lower : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position,
    DomainLowerTiling energy η M q
  upper : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position,
    DomainUpperTiling energy η M q
  interior : TileInteriorComparison energy η K
  dilation_integrable : TileDilationIntegrable energy η K
  dilation : TileDilationComparison energy η K

/-- A threshold beyond which the same constant controls the uniform
rough Coulomb estimates and the geometric comparisons. -/
def FiniteEnergyInputs.roughThreshold (H : FiniteEnergyInputs) (diff : SobolevDifferenceQuotients)
    (quant : SobolevDifferenceBounds) (η : Mollifier) : ℝ :=
  (H.exists_rough_constant diff quant η).choose

theorem FiniteEnergyInputs.one_le_roughThreshold (H : FiniteEnergyInputs) (diff : SobolevDifferenceQuotients)
    (quant : SobolevDifferenceBounds) (η : Mollifier) : 1 ≤ H.roughThreshold diff quant η :=
  (H.exists_rough_constant diff quant η).choose_spec.1

variable {η : Mollifier} {K : ℝ}

theorem CoulombTilingComparisons.rate (C : CoulombTilingComparisons η K)
    (H : FiniteEnergyInputs) (diff : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (hK : H.roughThreshold diff quant η ≤ K) : FiniteRateTiling energy η K where
  one_le := (H.one_le_roughThreshold diff quant η).trans hK
  rough := (H.exists_rough_constant diff quant η).choose_spec.2 K hK
  interior := C.interior
  dilation_integrable := C.dilation_integrable
  dilation := C.dilation

theorem CoulombTilingComparisons.localization (C : CoulombTilingComparisons η K)
    (rate : FiniteRateTiling energy η K) (M : SpinMatrix) (hM : M.PosSemidef)
    (hr : 0 < M.trace.re) (q : Position) : FiniteLocalization energy η M q where
  bounds := rate.tileBounds hM q
  twoScale := C.twoScale M hM hr q
  measurable := C.measurable M hM hr q
  lower := C.lower M hM hr q
  upper := C.upper M hM hr q

/-- The SSW gas for the Coulomb energy, including the limit on every
admissible sequence and the sharp full-polarization identity. -/
theorem coulomb_sswGas_of_finite_tilings (H : FiniteEnergyInputs) (diff : SobolevDifferenceQuotients)
    (strong : SobolevDirectionalLimits) (hK : H.roughThreshold diff strong.toDifferenceBounds η ≤ K)
    (C : CoulombTilingComparisons η K) : SSWGasTheorem (referenceEnergies energy η) :=
  coulomb_sswGas_of_localization η (C.localization (C.rate H diff strong.toDifferenceBounds hK)) H diff

def CoulombTilingComparisons.gasInputs (C : CoulombTilingComparisons η K)
    (H : FiniteEnergyInputs) (diff : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (hK : H.roughThreshold diff quant η ≤ K) (red : FockSpinCurrentTraces) : CoulombGasInputs η K :=
  let rate := C.rate H diff quant hK
  CoulombGasInputs.of_reduced (C.localization rate) rate red

/-- The Coulomb bounds of Theorem 3.3 and the positive-minority strengthening
use gas moduli derived from the same finite tilings as the trial comparisons. -/
theorem levyLieb_tsga_of_finite_tilings (H : FiniteEnergyInputs) (chain : WeakPhaseProduct)
    (sob : SobolevLipschitzComposition) (diff : SobolevDifferenceQuotients)
    (strong : SobolevDirectionalLimits) (hK : H.roughThreshold diff strong.toDifferenceBounds η ≤ K)
    (C : CoulombTilingComparisons η K) (red : FockSpinCurrentTraces)
    (tiles : (C.gasInputs H diff strong.toDifferenceBounds hK red).TileTrials H diff) :
    MainExtendedTSGAEstimate (referenceEnergies energy η) :=
  levyLieb_tsga_of_reduced_traces H chain sob diff (C.localization (C.rate H diff strong.toDifferenceBounds hK))
    (C.rate H diff strong.toDifferenceBounds hK) red tiles

end TSGA.ManyBody
