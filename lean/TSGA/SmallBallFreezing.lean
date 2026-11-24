import TSGA.ActualFrozenScale
import TSGA.SmallBallTrialAverage
import TSGA.SmallBallGasChoice

/-! # Freezing both actual tile families at the center of a comparison ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW PhaseLocalization Set Metric
open scoped ComplexOrder MatrixOrder

/-- The integrated pointwise gas comparison for one phase. This form also
allows a stronger zero-wavevector modulus when the endpoint law holds. -/
def PhaseGasComparison (η : Mollifier) (mode : BulkRegime) (p θ ν K J : ℝ) (φ : Phase)
    (a : ℝ := mode.holderPower p θ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {D N : Density} {G : MatrixGradient} {c : Position},
    ∀ (s : SmallBallScale N (3*ε⁻¹) c) (m : SmallBallMatrices s),
    N.matrix =ᵐ[volume] D.matrix → Continuous N.matrix →
    (∀ z : ℝ, 0 < z → Continuous (N.power z)) → φ.Regular p → RegimeHyp mode ν N G p →
    s.omega θ ≤ s.r^θ → ∀ {F : SpinMatrix}, F.PosSemidef → F=m.low ∨ F=m.high →
    ∀ (P : TileProfile), (∀ x, P.cutoff (c-x) ≠ 0 → x ∈ closedBall c (3*ε⁻¹)) → ∀ σ : ℝ,
    let E := referenceEnergies energy η
    let r := s.r
    let d := s.omega (1/p)/r^(1/p)
    let phase := smallBallPhaseCost r d ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c)
    let b := mode.densityPower p θ
    ∃ f : Position → ℝ,
      Integrable (fun x => (σ*localEnergy E D φ x)*P.cutoff (c-x)) ∧
      Integrable (fun x => f x*P.cutoff (c-x)) ∧
      (∀ᵐ x, P.cutoff (c-x) ≠ 0 → |E.ssw F (φ.grad c)-localEnergy E D φ x| ≤ f x) ∧
      cutoffAverage P.cutoff f c ≤ smallGasConstant J K*(smallGasBulk r (s.omega b) b a+phase)

theorem SmallGasChoice.at_phase {η : Mollifier} {M : PhysicalTileModulus η} {mode : BulkRegime}
    {p θ ν K J : ℝ} (choice : SmallGasChoice M mode p θ ν K J) (φ : Phase) :
    PhaseGasComparison η mode p θ ν K J φ := by
  intro ε he hle D N G c s m e cn cp phase regime small F hF sel P support σ
  obtain ⟨dom,ir,im,h⟩ := choice he hle s m e cn cp phase regime small hF sel P support σ
  refine ⟨_,ir,im,?_,h⟩
  filter_upwards [dom] with x hx
  exact fun _ => M.bound hF (D.positive x) hx (φ.grad c) (φ.grad x)

/-- Combine the signed Coulomb replacement, the finite SSW rate and the
pointwise gas modulus at the same matrix and center wavevector. -/
theorem SmallBallMatrices.freeze_at_phase {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι]
    {ε K C a p θ ν J : ℝ} {η : Mollifier} (L : CoulombGasInputs η K)
    (F : IslandFockInputs μ) (radii : CoulombIslandRadii μ ι ε C)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (prod : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (comp : SobolevLipschitzComposition) (W : WindowSobolevRules)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100)) (sob : SobolevDifferenceQuotients)
    (mode : BulkRegime) (side : CutoffSide) (he : 0 < ε) (hle : ε ≤ 1/2)
    (admissible : ε*(K+1) ≤ 1)
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) (hE : exteriorFormConstant F.oneBody ≤ C)
    (hI : F.oneBody.interiorConstant ≤ C) {N D : Density} {φ : Phase} {S T G : MatrixGradient}
    (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G)
    (regime : RegimeHyp mode ν D G p) (eqND : N.matrix =ᵐ[volume] D.matrix)
    (cont : Continuous N.matrix) (powers : ∀ a : ℝ, 0 < a → Continuous (N.power a))
    (hp : 3 < p) {c : Position} {s : SmallBallScale N (3*ε⁻¹) c} (m : SmallBallMatrices s)
    (small : s.omega θ ≤ s.r^θ) (localComp : SobolevCompositionOn (closedBall c (3*ε⁻¹)))
    {gasPower : ℝ} (gas : PhaseGasComparison η mode p θ ν K J φ gasPower)
    (P : TileProfile) (profile : P.cutoff = (actualTiles O frames η side he (by linarith)).cutoffProfile)
    (raw : Position → ℝ) :
    let tiles := actualTiles O frames η side he (by linarith)
    let σ := tileSign side
    let B := if σ=1 then m.low else m.high
    let q := φ.grad c
    let d := s.omega (1/p)/s.r^(1/p)
    let v := tilePhaseOscillation φ c ε⁻¹
    let k := ∫ x in closedBall c (3*ε⁻¹), kineticDensity S x
    let b := mode.densityPower p θ
    let replacement := 192*ε^3*smallReplacementCost F.oneBody C ε (ε⁻¹^3) (a*ε⁻¹^2) k ‖q‖
      s.r (3*s.omega 1) d p v
    let size := smallFrozenSizeCost K ε B.trace.re q
    let gasError := smallGasConstant J K*(smallGasBulk s.r (s.omega b) b gasPower +
      smallBallPhaseCost s.r d ε v q)
    replacement + size + gasError ≤ P.directCost c + raw c →
    ∃ X : FrozenSmallTile (referenceEnergies energy η) D φ tiles P σ raw c,
      X.matrix = B ∧ X.wavevector = q := by
  classical
  intro tiles σ B q d v k b replacement size gasError scalar
  have sel : B=m.low ∨ B=m.high := by dsimp only [B]; split <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hB : B.PosSemidef := sel.elim (fun h => h ▸ m.low_pos) (fun h => h ▸ m.high_pos)
  have sign : σ=1 ∨ σ=-1 := by cases side <;> first | exact Or.inl rfl | exact Or.inr rfl
  obtain ⟨cr,replace⟩ := m.actual_replacement F radii leibniz chain prod borel comp W O frames η support sob
    side he (by linarith) L.rate ha area hE hI reg phase eqND cont (powers 1 zero_lt_one) hp localComp P profile
  obtain ⟨fint,fin,hsize⟩ := actual_frozen_scale F.oneBody sob borel O frames η side he hle admissible
    L.rate ha area hB q c
  have supported (x : Position) (hx : P.cutoff (c-x) ≠ 0) : x ∈ closedBall c (3*ε⁻¹) := by
    by_contra outside
    apply hx
    rw [profile]
    change (∫ i : ℝ × O.Frames, tiles.weight i * tiles.shape i (c-x) ∂tileDilationLaw.prod O.law) = 0
    simp only [show ∀ i : ℝ × O.Frames, tiles.shape i (c-x) = 0 from
      fun i => actualTiles_supported O frames η support side he (by linarith) c i x outside,mul_zero,integral_zero]
  obtain ⟨f,refInt,modInt,compare,gasBound⟩ := gas he (by linarith) s m eqND cont powers phase.regular
    (regimeHyp_of_ae eqND.symm regime) small hB sel P supported σ
  refine ⟨⟨B,hB,q,fint,replacement,fin.error,mul_nonneg (by positivity) cr,fin.nonneg,
    f,replace,fin.toRate sign,refInt,modInt,compare,?_⟩,rfl,rfl⟩
  rw [hsize]
  exact (add_le_add (le_refl (replacement+size)) gasBound).trans scalar

/-- Combine the signed Coulomb replacement, the finite SSW rate and the
pointwise gas modulus at the same matrix and center wavevector. -/
theorem SmallBallMatrices.freeze {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι]
    {ε K C a p θ ν J : ℝ} {η : Mollifier} (L : CoulombGasInputs η K)
    (F : IslandFockInputs μ) (radii : CoulombIslandRadii μ ι ε C)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (prod : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (comp : SobolevLipschitzComposition) (W : WindowSobolevRules)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100)) (sob : SobolevDifferenceQuotients)
    (mode : BulkRegime) (side : CutoffSide) (he : 0 < ε) (hle : ε ≤ 1/2)
    (admissible : ε*(K+1) ≤ 1)
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) (hE : exteriorFormConstant F.oneBody ≤ C)
    (hI : F.oneBody.interiorConstant ≤ C) {N D : Density} {φ : Phase} {S T G : MatrixGradient}
    (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G)
    (regime : RegimeHyp mode ν D G p) (eqND : N.matrix =ᵐ[volume] D.matrix)
    (cont : Continuous N.matrix) (powers : ∀ a : ℝ, 0 < a → Continuous (N.power a))
    (hp : 3 < p) {c : Position} {s : SmallBallScale N (3*ε⁻¹) c} (m : SmallBallMatrices s)
    (small : s.omega θ ≤ s.r^θ) (localComp : SobolevCompositionOn (closedBall c (3*ε⁻¹)))
    {mod : PhysicalTileModulus η} (gas : SmallGasChoice mod mode p θ ν K J)
    (P : TileProfile) (profile : P.cutoff = (actualTiles O frames η side he (by linarith)).cutoffProfile)
    (raw : Position → ℝ) :
    let tiles := actualTiles O frames η side he (by linarith)
    let σ := tileSign side
    let B := if σ=1 then m.low else m.high
    let q := φ.grad c
    let d := s.omega (1/p)/s.r^(1/p)
    let v := tilePhaseOscillation φ c ε⁻¹
    let k := ∫ x in closedBall c (3*ε⁻¹), kineticDensity S x
    let b := mode.densityPower p θ
    let replacement := 192*ε^3*smallReplacementCost F.oneBody C ε (ε⁻¹^3) (a*ε⁻¹^2) k ‖q‖
      s.r (3*s.omega 1) d p v
    let size := smallFrozenSizeCost K ε B.trace.re q
    let gasError := smallGasConstant J K*(smallGasBulk s.r (s.omega b) b (mode.holderPower p θ) +
      smallBallPhaseCost s.r d ε v q)
    replacement + size + gasError ≤ P.directCost c + raw c →
    ∃ X : FrozenSmallTile (referenceEnergies energy η) D φ tiles P σ raw c,
      X.matrix = B ∧ X.wavevector = q := by
  exact m.freeze_at_phase L F radii leibniz chain prod borel comp W O frames support sob mode side he hle
    admissible ha area hE hI reg phase regime eqND cont powers hp small localComp (gas.at_phase φ) P profile raw

end TSGA.ManyBody
