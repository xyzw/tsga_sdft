import TSGA.CoulombModelInputs
import TSGA.CoulombTileErrorIntegral
import TSGA.IntegratedLargeTile
import TSGA.IntegratedActualTiles
import TSGA.CoulombEstimateFromBounds

/-! # Integration of the Coulomb comparison on all centers -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Set Metric

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}

/-- A signed small-ball bound with the same constant on both physical tile
families. The phase restriction allows the zero-wavevector endpoint comparison to use the same large-ball proof and scale choice. -/
def SmallBallBoundWithError (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (mode : BulkRegime) (ν p θ C K A : ℝ) (allow : Phase → MatrixGradient → Prop)
    (extra : Density → MatrixGradient → ℝ → Position → ℝ) : Prop :=
  ∀ {D : Density} {φ : Phase} {S T G : MatrixGradient},
    DensityRegular D p θ S T → PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → allow φ G →
    ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), ε*(K+1) ≤ 1 → ∀ (side : CutoffSide) (P : TileProfile),
    let tiles := actualTiles O frames η side he (by linarith)
    let F := referenceEnergies energy η
    P.cutoff = tiles.cutoffProfile → ∀ c, SmallPowerOscillation D θ (θ/64) (3*ε⁻¹) c →
      tileSign side*(tiles.energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c) ≤
        A*smallBallErrorDensity mode D φ S T G p θ ε C c + extra D T ε c

def SmallBallBoundFor (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (mode : BulkRegime) (ν p θ C K A : ℝ) (allow : Phase → MatrixGradient → Prop) : Prop :=
  ∀ {D : Density} {φ : Phase} {S T G : MatrixGradient},
    DensityRegular D p θ S T → PhaseAdmissible D p φ G → RegimeHyp mode ν D G p → allow φ G →
    ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), ε*(K+1) ≤ 1 → ∀ (side : CutoffSide) (P : TileProfile),
    let tiles := actualTiles O frames η side he (by linarith)
    let F := referenceEnergies energy η
    P.cutoff = tiles.cutoffProfile → ∀ c, SmallPowerOscillation D θ (θ/64) (3*ε⁻¹) c →
      tileSign side*(tiles.energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c) ≤
        A*smallBallErrorDensity mode D φ S T G p θ ε C c

/-- The error dominating both oscillation cases is integrable without any
measurable selection of comparison matrices or trial states. -/
theorem CoulombModelInputs.integrate_balls_with_error (P : CoulombModelInputs μ ι η) {K : ℝ}
    (gas : CoulombGasInputs η K) (mode : BulkRegime) {p θ ν C a A : ℝ}
    (hp : 3 < p) (hθ : 0 < θ) (hpθ : 2 ≤ p*θ)
    (M : MatrixSobolevMorrey p C) (hC : 0 ≤ C) (ha : 0 ≤ a) (area : TileCutoffAreaBound η a)
    (hA : 1 ≤ A) {allow : Phase → MatrixGradient → Prop}
    (extra : Density → MatrixGradient → ℝ → Position → ℝ)
    (total : Density → Phase → MatrixGradient → MatrixGradient → MatrixGradient → ℝ → ℝ) {V : ℝ}
    (majorant : ∀ {D φ S T G ε}, DensityRegular D p θ S T → PhaseAdmissible D p φ G →
      RegimeHyp mode ν D G p → allow φ G → 0 < ε → ε ≤ 1/2 →
      Integrable (extra D T ε) ∧ (∀ c, 0 ≤ extra D T ε c) ∧
      integratedScaleCost mode D φ S T G p θ ε ≤ total D φ S T G ε ∧
      (∫ c, extra D T ε c) ≤ V*total D φ S T G ε)
    (small : SmallBallBoundWithError P.orientations P.frames η mode ν p θ C K A allow extra) :
    ∃ J ≥ 1, ∃ τ > 0, ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient),
      DensityRegular D p θ S T → PhaseAdmissible D p φ G → RegimeHyp mode ν D G p →
      allow φ G → ∀ ε, 0 < ε → ε ≤ τ →
      let F := referenceEnergies energy η
      |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤ J*total D φ S T G ε := by
  let H := P.fock.oneBody
  let O := P.orientations
  let κ := θ/64
  have hk : 0 < κ := div_pos hθ (by norm_num)
  have hK := zero_le_one.trans gas.rate.one_le
  have hp₀ : 0 < p := by linarith
  let Q := 2*roughTrialCoeff H K*192
  let U := max A (Q*largeTileBallCoefficient mode p θ κ C)
  let J := tileErrorCoefficient H p C a U
  have hU : 0 ≤ U := (zero_le_one.trans hA).trans (le_max_left ..)
  have q₀ : 0 ≤ Q := by
    dsimp only [Q,roughTrialCoeff]
    positivity [H.interiorConstant_nonneg,H.lo_nonneg]
  obtain ⟨A₀,hA₀,rough⟩ := gas.aPriori H P.phaseProduct P.difference
  obtain ⟨B,hB,global⟩ := actual_signed_global_bound_at_cost H P.product P.phaseProduct P.window P.difference
    P.directional.toDifferenceBounds P.fock.tensor P.lowerSemicontinuity O P.frames P.haar
    P.support P.skeleton P.transport_nonneg P.fourier_nonneg P.graf_nonneg P.graf P.transport P.fourier rough hA₀
  let τ := min (1/2 : ℝ) (min (1/(K+1)) ((1/2)/(P.grafConstant+1)))
  have hτ : 0 < τ := lt_min (by norm_num) (lt_min (by positivity) (by positivity [P.graf_nonneg]))
  refine ⟨max 1 (B+(J+V)),le_max_left ..,τ,hτ,?_⟩
  intro D φ S T G reg phase hr allowed ε he hε F
  have hle : ε ≤ 1/2 := hε.trans (min_le_left ..)
  have hle' : ε < 1 := by linarith
  have hbound := hε.trans (min_le_right ..)
  have had : ε*(K+1) ≤ 1 := (le_div_iff₀ (by positivity)).mp (hbound.trans (min_le_left ..))
  have hg : P.grafConstant*ε ≤ 1/2 := by
    have h := (le_div_iff₀ (by positivity [P.graf_nonneg] : 0 < P.grafConstant+1)).mp (hbound.trans (min_le_right ..))
    linarith only [h,he]
  obtain ⟨ei,en,cover,extraBound⟩ := majorant reg phase hr allowed he hle
  apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right 1 (B+(J+V)))
    ((integratedScaleCost_nonneg mode D φ S T G p θ he).trans cover))
  apply global mode hp hθ reg phase he hle hg (J+V) (total D φ S T G ε) cover
  intro side profile cut
  let σ := tileSign side
  let tiles := actualTiles O P.frames η side he hle'
  let err := fun c => U*smallBallErrorDensity mode D φ S T G p θ ε C c +
    actualLargeKinetic H O P.frames η side he hle' D S c
  obtain ⟨hi,hint⟩ := integral_actual_tile_error H O P.frames η P.difference ha area hC hU hp₀
    he hle' side reg phase hr
  have hJ : 0 ≤ J := by
    dsimp only [J,tileErrorCoefficient,tileMorreyCoefficient]
    positivity [H.interiorConstant_nonneg,(ballVolume_pos zero_lt_one).le]
  refine ⟨fun c => err c+extra D T ε c,hi.add ei,ae_of_all _ fun c => ?_,?_⟩
  swap
  · rw [integral_add hi ei,add_mul]
    exact add_le_add (hint.trans (mul_le_mul_of_nonneg_left cover hJ)) extraBound
  let w := smallBallErrorDensity mode D φ S T G p θ ε C c
  have hw : 0 ≤ w := smallBallErrorDensity_nonneg mode D φ S T G p θ he hC c
  by_cases test : SmallPowerOscillation D θ κ (3*ε⁻¹) c
  · have hs := small reg phase hr allowed he hle had side profile cut c test
    exact hs.trans (add_le_add ((mul_le_mul_of_nonneg_right (le_max_left ..) hw).trans
      (le_add_of_nonneg_right (actualLargeKinetic_nonneg H O P.frames η side he hle' D S c))) le_rfl)
  · have large := (H.actual_large_oscillation_of_regular P.product P.phaseProduct
      (levyLiebBorel_of_lowerSemicontinuous P.lowerSemicontinuity) O P.frames η ((subset_tsupport _).trans P.support)
      P.difference mode side he hle' gas.rate M hC P.truncation reg phase hr hp hpθ hk profile cut c test).2
    have signed (x : ℝ) : σ*x ≤ |x| := by cases side <;> simp [σ,tileSign,le_abs_self,neg_le_abs]
    apply le_trans _ (le_add_of_nonneg_right (en c))
    apply (signed _).trans (large.trans _)
    apply add_le_add _ le_rfl
    calc
      _ = Q*(ε^3*largeTileBallCost mode p θ κ ε C c D φ T G) := by dsimp only [Q]; ring
      _ ≤ Q*(largeTileBallCoefficient mode p θ κ C*w) :=
        mul_le_mul_of_nonneg_left (largeTileBallCost_bound mode hp₀ hθ hk hC he reg phase c) q₀
      _ = (Q*largeTileBallCoefficient mode p θ κ C)*w := (mul_assoc ..).symm
      _ ≤ U*w := mul_le_mul_of_nonneg_right (le_max_right ..) hw

/-- Integrate the physical tile bounds for each bulk estimate. -/
theorem CoulombModelInputs.integrate_balls (P : CoulombModelInputs μ ι η) {K : ℝ}
    (gas : CoulombGasInputs η K) (mode : BulkRegime) {p θ ν C a A : ℝ}
    (hp : 3 < p) (hθ : 0 < θ) (hpθ : 2 ≤ p*θ)
    (M : MatrixSobolevMorrey p C) (hC : 0 ≤ C) (ha : 0 ≤ a) (area : TileCutoffAreaBound η a)
    (hA : 1 ≤ A) {allow : Phase → MatrixGradient → Prop}
    (small : SmallBallBoundFor P.orientations P.frames η mode ν p θ C K A allow) :
    ∃ J ≥ 1, ∃ τ > 0, ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient),
      DensityRegular D p θ S T → PhaseAdmissible D p φ G → RegimeHyp mode ν D G p →
      allow φ G → ∀ ε, 0 < ε → ε ≤ τ →
      let F := referenceEnergies energy η
      |rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| ≤ J*integratedScaleCost mode D φ S T G p θ ε := by
  let extra := fun (_ : Density) (_ : MatrixGradient) (_ : ℝ) (_ : Position) => (0 : ℝ)
  obtain ⟨J,hJ,τ,hτ,bound⟩ := P.integrate_balls_with_error gas mode hp hθ hpθ M hC ha area hA
    extra (fun D φ S T G ε => integratedScaleCost mode D φ S T G p θ ε) (V := 0) (allow := allow)
    (fun _ _ _ _ _ _ => ⟨integrable_zero _ _ _,fun _ => le_rfl,le_rfl,by simp [extra]⟩) (by
      intro D φ S T G reg phase hr ok ε he he' had side profile tiles F cut c test
      simpa only [extra,add_zero] using small reg phase hr ok he he' had side profile cut c test)
  exact ⟨J,hJ,τ,hτ,bound⟩

/-- The integrated bound at small scales in each regime uses the power
and the positive minority fraction exactly where the gas modulus needs them. -/
theorem CoulombModelInputs.smallScale (P : CoulombModelInputs μ ι η) {K : ℝ}
    (gas : CoulombGasInputs η K) (mode : BulkRegime) {ν p θ : ℝ}
    (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hpθ : 2 ≤ p*θ)
    (minority : mode = .minority → 0 < ν ∧ ν ≤ 1/2) (root : mode = .globalRoot → θ*p=2) :
    ∃ A ≥ 1, ∃ τ > 0, CoulombSmallScaleBound η mode ν p θ A τ := by
  obtain ⟨C,hC,M⟩ := P.matrixMorrey p hp
  obtain ⟨V,hV,vec⟩ := P.vectorMorrey p hp
  obtain ⟨a,ha,area⟩ := tileCutoffAreaBound_of_sobolev P.difference P.directional.toDifferenceBounds η
  obtain ⟨A,hA,small⟩ := actual_small_oscillation_of_regular gas P.fock ((subset_tsupport _).trans P.support)
    P.poisson P.poisson_nonneg P.leibniz P.phaseProduct P.product (levyLiebBorel_of_lowerSemicontinuous P.lowerSemicontinuity)
    P.composition P.window P.orientations P.frames P.difference P.directional.toDifferenceBounds P.ballComposition
    ha area mode M vec hC hV hp hθ hθ' hpθ minority root
  have localBound : SmallBallBoundFor P.orientations P.frames η mode ν p θ C K A (fun _ _ => True) := by
    intro D φ S T G reg phase hr _ ε he hle had side profile tiles F cut c test
    exact (small reg phase hr he hle had side profile cut c test).2
  obtain ⟨J,hJ,τ,hτ,bound⟩ := P.integrate_balls gas mode hp hθ hpθ M hC ha area hA localBound
  exact ⟨J,hJ,τ,hτ,fun D φ S T G reg phase hr => bound D φ S T G reg phase hr trivial⟩

end TSGA.ManyBody
