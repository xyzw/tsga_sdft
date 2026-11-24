import TSGA.SmallBallFreezing
import TSGA.SmallBallScalarCost
import TSGA.SmallBallErrorDensity
import TSGA.IslandPoissonConstruction

/-! # The Coulomb comparison on a small-oscillation ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW PhaseLocalization Set Metric
open scoped ComplexOrder MatrixOrder

/-- For each bulk regime a single coefficient works for both physical taper
families, every center, and every admissible scale. The only local test is
the essential oscillation of the original density. -/
theorem actual_small_oscillation_for_phases {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι]
    {K a p θ ν Cmat Cvec g : ℝ} {η : Mollifier} (L : CoulombGasInputs η K) (F : IslandFockInputs μ)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (laws : TetraPoissonLaws μ ι η support g) (hg : 0 ≤ g)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (prod : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (comp : SobolevLipschitzComposition) (W : WindowSobolevRules)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (localComp : ∀ (c : Position) (R : ℝ), 0 < R → SobolevCompositionOn (closedBall c R))
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) (mode : BulkRegime)
    (M : MatrixSobolevMorrey p Cmat) (V : VectorMorreyOnBalls p Cvec)
    (hM : 0 ≤ Cmat) (hV : 0 ≤ Cvec) (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1)
    (hpθ : 2 ≤ p*θ) (root : mode = .globalRoot → θ*p = 2) (allowed : Phase → Prop)
    {J : ℝ} (hJ : 0 < J) (choice : ∀ φ, allowed φ → PhaseGasComparison η mode p θ ν K J φ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {D : Density} {φ : Phase} {S T G : MatrixGradient},
      DensityRegular D p θ S T → PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → allowed φ →
      ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), ε*(K+1) ≤ 1 →
      ∀ (side : CutoffSide) (P : TileProfile),
      P.cutoff = (actualTiles O frames η side he (by linarith)).cutoffProfile →
      ∀ c, SmallPowerOscillation D θ (θ/64) (3*ε⁻¹) c →
      let tiles := actualTiles O frames η side he (by linarith)
      let gas := referenceEnergies energy η
      let σ := tileSign side
      let err := fun z => A * smallBallErrorDensity mode D φ S T G p θ ε Cmat z
      (∃ X : FrozenSmallTile gas D φ tiles P σ (fun z => err z-P.directCost z) c,
        X.wavevector = φ.grad c) ∧
      σ*(tiles.energy gas D φ c - cutoffAverage P.cutoff (localEnergy gas D φ) c) ≤ err c := by
  classical
  obtain ⟨C,hC,hE,hI,radii⟩ := laws.radii hg sob quant F
  let U := smallBallScalarCoefficient F.oneBody C a K p
  let Vg := smallGasConstant J K
  have hK := zero_le_one.trans L.rate.one_le
  have hU : 0 ≤ U := smallBallScalarCoefficient_nonneg F.oneBody hC ha hK (by linarith)
  have hVg : 0 ≤ Vg := by dsimp only [Vg,smallGasConstant]; positivity
  let A := smallBallErrorConstant p θ Cmat Cvec U Vg
  refine ⟨max 1 A,le_max_left ..,?_⟩
  intro D φ S T G reg phase regime hφ ε he hle admissible side P profile c test tiles gas σ err
  have hR : 0 < 3*ε⁻¹ := by positivity
  obtain ⟨N,e,hN,powers,s,hω,⟨m⟩⟩ := smallBallMatrices_of_regular M hp hθ hθ' reg hR le_rfl c test
  have small : s.omega θ ≤ s.r^θ := hω.trans (mul_le_of_le_one_left (Real.rpow_nonneg s.r_nonneg _) (by linarith))
  let B := if σ=1 then m.low else m.high
  have sel : B=m.low ∨ B=m.high := by dsimp only [B]; split <;> first | exact Or.inl rfl | exact Or.inr rfl
  have range := m.trace_range sel
  let q := φ.grad c
  let v := tilePhaseOscillation φ c ε⁻¹
  let k := ∫ x in closedBall c (3*ε⁻¹), kineticDensity S x
  have hk : 0 ≤ k := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨z,_,hv,_⟩ := tilePhaseOscillation_attained phase.regular c (inv_pos.mpr he)
  have v0 : 0 ≤ v := (norm_nonneg _).trans_eq hv.symm
  have sum := smallBallScalarCost s q F.oneBody (by linarith : 1 ≤ p) he (by linarith) hC ha hK
    v0 hk ((div_nonneg s.r_nonneg (by norm_num : (0:ℝ) ≤ 2)).trans range.1) range.2
  let raw := fun z => err z - P.directCost z
  obtain ⟨X,_,qeq⟩ := m.freeze_at_phase L F (radii he (by linarith)) leibniz chain prod borel comp W O frames
    support sob mode side he hle admissible ha area hE hI reg phase regime e hN powers hp small
    (localComp c _ hR) (choice φ hφ) P profile raw (by
      have est := s.error_density_bound mode e reg phase regime M V hp hpθ hθ hθ' he (by linarith) hM hV
        powers small root hU hVg
      let b := mode.densityPower p θ
      let ge := Vg*(smallGasBulk s.r (s.omega b) b (mode.holderPower p θ) +
        smallBallPhaseCost s.r (s.omega (1/p)/s.r^(1/p)) ε v q)
      have normed := (add_le_add sum (le_refl ge)).trans (by
        simpa only [ge,b,v,q,k,U,smallGasBulk,show 2*(3*s.omega 1)=6*s.omega 1 by ring] using est)
      have nonneg := smallBallErrorDensity_nonneg mode D φ S T G p θ he hM c
      have relaxed := normed.trans (mul_le_mul_of_nonneg_right (le_max_right 1 A) nonneg)
      exact relaxed.trans_eq (by dsimp only [raw,err]; ring))
  refine ⟨⟨X,qeq⟩,?_⟩
  have sign : σ=1 ∨ σ=-1 := by cases side <;> first | exact Or.inl rfl | exact Or.inr rfl
  have signed := X.estimate sign profile
  have sc : cutoffAverage P.cutoff (fun x => σ*localEnergy gas D φ x) c =
      σ*cutoffAverage P.cutoff (localEnergy gas D φ) c := by
    change (∫ x, (σ*localEnergy gas D φ x)*P.cutoff (c-x)) = σ*∫ x, localEnergy gas D φ x*P.cutoff (c-x)
    simp_rw [mul_assoc,integral_const_mul]
  dsimp only [TileProfile.localBase,raw,TileProfile.directCost] at signed
  rw [sc] at signed
  linarith only [signed]

/-- For each bulk regime a single coefficient works for both physical taper
families, every center, and every admissible scale. The only local test is
the essential oscillation of the original density. -/
theorem actual_small_oscillation_of_regular {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι]
    {K a p θ ν Cmat Cvec g : ℝ} {η : Mollifier} (L : CoulombGasInputs η K) (F : IslandFockInputs μ)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (laws : TetraPoissonLaws μ ι η support g) (hg : 0 ≤ g)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (prod : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (comp : SobolevLipschitzComposition) (W : WindowSobolevRules)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (localComp : ∀ (c : Position) (R : ℝ), 0 < R → SobolevCompositionOn (closedBall c R))
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) (mode : BulkRegime)
    (M : MatrixSobolevMorrey p Cmat) (V : VectorMorreyOnBalls p Cvec)
    (hM : 0 ≤ Cmat) (hV : 0 ≤ Cvec) (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1)
    (hpθ : 2 ≤ p*θ) (minority : mode = .minority → 0 < ν ∧ ν ≤ 1/2)
    (root : mode = .globalRoot → θ*p = 2) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {D : Density} {φ : Phase} {S T G : MatrixGradient},
      DensityRegular D p θ S T → PhaseAdmissible D p φ G → RegimeHyp mode ν D G p →
      ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), ε*(K+1) ≤ 1 →
      ∀ (side : CutoffSide) (P : TileProfile),
      P.cutoff = (actualTiles O frames η side he (by linarith)).cutoffProfile →
      ∀ c, SmallPowerOscillation D θ (θ/64) (3*ε⁻¹) c →
      let tiles := actualTiles O frames η side he (by linarith)
      let gas := referenceEnergies energy η
      let σ := tileSign side
      let err := fun z => A * smallBallErrorDensity mode D φ S T G p θ ε Cmat z
      (∃ X : FrozenSmallTile gas D φ tiles P σ (fun z => err z-P.directCost z) c,
        X.wavevector = φ.grad c) ∧
      σ*(tiles.energy gas D φ c - cutoffAverage P.cutoff (localEnergy gas D φ) c) ≤ err c := by
  obtain ⟨J,hJ,gas⟩ := L.freezeGas F.oneBody sob mode hp hθ hθ' hpθ minority
  obtain ⟨A,hA,estimate⟩ := actual_small_oscillation_for_phases L F support laws hg leibniz chain prod
    borel comp W O frames sob quant localComp ha area mode M V hM hV hp hθ hθ' hpθ root
    (fun _ => True) hJ (fun φ _ => gas.at_phase φ)
  exact ⟨A,hA,fun reg phase regime => estimate reg phase regime trivial⟩

end TSGA.ManyBody
