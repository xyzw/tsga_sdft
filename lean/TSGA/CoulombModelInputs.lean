import TSGA.CoulombPhysicalTiling
import TSGA.FockPartialTrace
import TSGA.RegularSmallTile

/-! # Analytic and operator inputs for the Coulomb specialization -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization PhaseLocalization Metric Set

/-- The one-body, Fock-space, geometric and Sobolev facts used by the
Coulomb proof. The marked process uses probability law μ and intensity
measure ι before scaling. All data here precede the choice of density. -/
structure CoulombModelInputs {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ι : Measure Z) [SFinite ι] (η : Mollifier) where
  fock : IslandFockInputs μ
  fourierTransform : SectorFourierTransform
  partialTrace : FockPartialTraceSpectralTheorem fourierTransform
  plancherel : SectorPlancherelMoments fourierTransform
  lowerSemicontinuity : LowerSemicontinuous extendedL1ConstrainedSearch
  support : tsupport η.kernel ⊆ closedBall 0 (1/100)
  orientations : TileOrientationLaw
  frames : TileFrameMeasurable orientations
  haar : CubeFrameInvariant orientations
  skeleton : SkeletonFisherAverages η
  grafConstant : ℝ
  graf_nonneg : 0 ≤ grafConstant
  graf : SmearedGrafSchenker η orientations grafConstant
  poissonConstant : ℝ
  poisson_nonneg : 0 ≤ poissonConstant
  poisson : TetraPoissonLaws μ ι η ((subset_tsupport _).trans support) poissonConstant
  transportConstant : ℝ
  transport_nonneg : 0 ≤ transportConstant
  transport : PeriodicTransportInequality transportConstant
  fourierConstant : ℝ
  fourier_nonneg : 0 ≤ fourierConstant
  fourier : CoulombFourierAveraging orientations fourierConstant
  product : WeakScalarMatrixProduct
  phaseProduct : WeakPhaseProduct
  leibniz : LocalSectorLeibniz
  window : WindowSobolevRules
  difference : SobolevDifferenceQuotients
  directional : SobolevDirectionalLimits
  composition : SobolevLipschitzComposition
  ballComposition : ∀ (c : Position) (R : ℝ), 0 < R → SobolevCompositionOn (closedBall c R)
  truncation : TruncationSobolevCalculus
  matrixMorrey : ∀ p : ℝ, 3 < p → ∃ C ≥ 0, MatrixSobolevMorrey p C
  vectorMorrey : ∀ p : ℝ, 3 < p → ∃ C ≥ 0, VectorMorreyOnBalls p C

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}

/-- The thermodynamic limit, rate and finite spin comparisons all refer to
the same constrained search and the same reference mollifier. -/
theorem CoulombModelInputs.gas (P : CoulombModelInputs μ ι η) :
    SSWGasTheorem (referenceEnergies energy η) ∧ ∃ K, Nonempty (CoulombGasInputs η K) := by
  obtain ⟨gas,⟨K,_,comparisons,rate⟩,_⟩ := coulomb_sswGas_and_rate_of_fock_localization
    P.fock.oneBody P.window P.difference P.directional P.orientations P.frames P.haar P.graf_nonneg
    P.graf P.fock.tensor P.lowerSemicontinuity P.support P.skeleton P.transport_nonneg P.fourier_nonneg
    P.transport P.fourier
  exact ⟨gas,K,⟨CoulombGasInputs.of_reduced (comparisons.localization rate) rate
    (FockPartialTraceSpectralTheorem.spinCurrentTraces (F := P.fourierTransform) P.partialTrace P.plancherel)⟩⟩

end TSGA.ManyBody
