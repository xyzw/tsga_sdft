import TSGA.CoulombCubicVariance
import TSGA.CoulombUpperRegularity
import TSGA.CoulombPeriodicKernel
import TSGA.TetrahedronConeMeasure

/-! # The SSW thermodynamic limit and its finite tetrahedron rate

The reference mollifier has the small support used in the disjoint upper
trial. The domain sequence in the gas theorem has its own arbitrary mollifier.
-/

noncomputable section
namespace TSGA.ManyBody
open SSW MeasureTheory Set Metric
open scoped ComplexOrder

/-- The physical Coulomb limit and Proposition D.1 from the state-level
Graf–Schenker inequality, disjoint Fock tensorization, the scalar skeleton
Fisher estimate, and general analytic facts. All seven finite tiling
comparisons are constructed using the same constant. -/
theorem coulomb_sswGas_and_rate_of_fock_localization {η : Mollifier}
    (H : FiniteEnergyInputs) (W : WindowSobolevRules) (sob : SobolevDifferenceQuotients)
    (strong : SobolevDirectionalLimits) (O : TileOrientationLaw)
    (action : MeasurableFrameAction O) (haar : CubeFrameInvariant O)
    {G : ℝ} (hG : 0 ≤ G) (graf : SmearedGrafSchenker η O G)
    (tensor : DisjointFockTensorization) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (hk : tsupport η.kernel ⊆ closedBall 0 (1/100)) (fisher : SkeletonFisherAverages η)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B) :
    SSWGasTheorem (referenceEnergies energy η) ∧
      (∃ L ≥ H.roughThreshold sob strong.toDifferenceBounds η, CoulombTilingComparisons η L ∧
        FiniteRateTiling energy η L) ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ M : SpinMatrix, M.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ),
        0 < ℓ → 0 < δ → δ ≤ ℓ/C →
        averagedTile energy η M q ℓ δ ≤ sswEnergy energy η M q + C*upperRateError M.trace.re q ℓ δ ∧
        sswEnergy energy η M q - C*lowerRateError M.trace.re q ℓ δ ≤
          scaleAverage (fun t => averagedTile energy η M q (t*ℓ) (t*δ)) := by
  suffices base : SSWGasTheorem (referenceEnergies energy η) ∧
      ∃ L ≥ H.roughThreshold sob strong.toDifferenceBounds η, CoulombTilingComparisons η L ∧
        FiniteRateTiling energy η L by
    obtain ⟨gas,L,hL,comparisons,rate⟩ := base
    exact ⟨gas,⟨L,hL,comparisons,rate⟩,rate.tetrahedron_rate⟩
  let lower : CoulombLowerLocalization η := ⟨O,G,hG,graf⟩
  apply coulomb_sswGas_of_lattice_products H W sob strong lower O haar tensor lsc hk fisher
    tetrahedronCone η.periodicKernelCalculus hA hB transport fourier
  intro Ω hop hb _ χ d hd M hM q ℓ δ hδ hsc
  exact coulomb_lattice_integrals O action haar (levyLiebBorel_of_lowerSemicontinuous lsc) H W sob
    fisher ((subset_tsupport _).trans hk) hop hb χ hd hM q hδ hsc

end TSGA.ManyBody
