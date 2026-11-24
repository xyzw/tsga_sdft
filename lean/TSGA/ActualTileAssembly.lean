import TSGA.CoulombActualTiles
import TSGA.TSGATiles
import TSGA.ActualTileBall

/-! # Signed physical profiles for the integrated TSGA comparison -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Metric Set

def tileSign : CutoffSide → ℝ
  | .upper => 1
  | .lower => -1

private def exteriorCoefficient : CutoffSide → ℝ → ℝ → ℝ
  | .upper, U, _ => U
  | .lower, _, L => L

private theorem mass_le_one (s : CutoffSide) {ε : ℝ} (he : 0 < ε) (hle : ε < 1) :
    s.mass ε ≤ 1 := by
  cases s with
  | lower => exact le_rfl
  | upper => exact pow_le_one₀ (sub_nonneg.mpr hle.le) (by linarith)

private def physicalProfile {T : AveragedTiles} {side : CutoffSide} {ε k : ℝ}
    (H : TetrahedralCutoffs T side ε k) (F : GasEnergies) (D : Density) (φ : Phase)
    (S : MatrixGradient) (W V B : ℝ) (hW : 0 ≤ W) (he : 0 < ε) (hle : ε < 1)
    (hi : Integrable (T.energy F D φ)) (hc : Integrable D.charge)
    (hm : Integrable (massDensity D φ)) (hk : Integrable (kineticDensity S)) : TileProfile := by
  let := T.space
  let := T.probability
  have hf : Integrable H.kineticProfile volume := H.gradient_product.integral_prod_left
  exact {
    cutoff := T.cutoffProfile
    kineticKernel := fun x => W*H.kineticProfile x
    radius := 3*ε⁻¹
    radius_pos := by positivity
    tileEnergy := fun c => tileSign side*T.energy F D φ c
    volumeCost := fun x => V*(ε*massDensity D φ x + kineticDensity S x/ε)
    charge := D.charge
    ballCost := fun _ => 0
    exterior := tilingExterior D φ S ε B
    cutoff_integrable := H.shape_product.integral_prod_left
    cutoff_nonneg := ae_of_all _ fun _ => integral_nonneg fun i => mul_nonneg (T.weight_nonneg i) (T.shape_mem i _).1
    cutoff_mass_le_one := (H.cutoff_mass he).trans_le (mass_le_one side he hle)
    kinetic_integrable := hf.const_mul W
    kinetic_nonneg := ae_of_all _ fun _ => mul_nonneg hW (integral_nonneg fun i => mul_nonneg (T.weight_nonneg i) (sq_nonneg _))
    tile_integrable := hi.const_mul _
    volumeCost_integrable := ((hm.const_mul ε).add (hk.div_const ε)).const_mul V
    charge_integrable := hc
    ballCost_integrable := integrable_zero _ _ _
    exterior_integrable := (hm.add hk).const_mul (B*ε) }

/-- An integrated signed localization and the physical cutoff estimates leave
only the centerwise comparison and its ball error to the local argument. -/
theorem actualProfile_tileSide {F : GasEnergies} {D : Density} {φ : Phase} {S : MatrixGradient}
    {ε σ A A₀ : ℝ} (P : TileProfile) (raw ballCost : Position → ℝ)
    (cutoff : CutoffControl P D φ S ε A) (rough : APriori F A₀)
    (he : 0 < ε) (hA : 0 ≤ A) (hA₀ : 0 ≤ A₀) (hσ : σ = 1 ∨ σ = -1)
    (global : σ*rotatedEnergy F D φ ≤ (∫ c, P.tileEnergy c) + ∫ x, P.exterior x)
    (localBound : ∀ᵐ c, P.tileEnergy c ≤ P.localBase (fun x => σ*localEnergy F D φ x) c + raw c)
    (hi : Integrable ballCost) (bound : ∀ᵐ c, raw c ≤ ballAverage P.radius ballCost c) :
    TileSide (σ*rotatedEnergy F D φ) (fun x => σ*localEnergy F D φ x)
      (fun x => (3*A+A*A₀)*(ε*massDensity D φ x + kineticDensity S x/ε) + ballCost x) := by
  let Q : TileProfile := { P with ballCost := ballCost, ballCost_integrable := hi }
  refine TileSide.of_local_domination Q raw global localBound bound ?_
  filter_upwards [cutoff.bound rough he hA hA₀ hσ] with x hx
  simp only [Q,TileProfile.densityCost]
  linarith only [hx]

/-- The exterior and cutoff constants can be fixed before choosing the density,
phase or localization length. The signed localization inequalities and the two
profiles can enter `actualProfile_tileSide` with the remaining local comparisons. -/
theorem coulomb_actual_signed_profiles (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (chain : WeakPhaseProduct) (W : WindowSobolevRules)
    (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (tensor : DisjointFockTensorization) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (haar : CubeFrameInvariant O)
    {η : Mollifier} (hs : tsupport η.kernel ⊆ closedBall 0 (1/100)) (sk : SkeletonFisherAverages η)
    {A B C : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (hc : 0 ≤ C) (graf : SmearedGrafSchenker η O C)
    (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B)
    (V J : ℝ) (hJ : 0 ≤ J) :
    ∃ M₀ ≥ 3, ∀ M ≥ M₀, ∀ {D : Density} {φ : Phase} {p θ : ℝ} {S T : MatrixGradient},
      DensityRegular D p θ S T → φ.Regular p → (Integrable fun x => D.charge x * ‖φ.grad x‖^2) →
      ∀ {ε : ℝ} (he : 0 < ε) (hle : ε ≤ 1/2), C*ε ≤ 1/2 → ∀ side : CutoffSide,
        let F := referenceEnergies energy η
        let tiles := actualTiles O frames η side he (lt_of_le_of_lt hle (by norm_num))
        ∃ P : TileProfile, P.radius = 3*ε⁻¹ ∧ P.cutoff = tiles.cutoffProfile ∧
          P.tileEnergy = (fun c => tileSign side*tiles.energy F D φ c) ∧
          P.kineticKernel = (fun z => J*(∫ i : ℝ × O.Frames, actualTileWeight ε⁻¹ i.1 *
            ‖actualTileGradient O η side ε⁻¹ i z‖^2 ∂tileDilationLaw.prod O.law)) ∧
          P.volumeCost = (fun x => V*(ε*massDensity D φ x + kineticDensity S x/ε)) ∧
          tiles.EnergyIntegrable F D φ ∧ CutoffControl P D φ S ε M ∧
          tileSign side*rotatedEnergy F D φ ≤ (∫ c, P.tileEnergy c) + ∫ x, P.exterior x := by
  obtain ⟨U,hU,L,hL,glob⟩ := coulomb_actual_tile_localization H product chain W sob quant tensor lsc
    O frames haar hs sk ha hb hc graf transport fourier
  obtain ⟨K,hK,area⟩ := tileCutoffAreaBound_of_sobolev sob quant η
  let M₀ := max (max 3 V) (max (J*(96*(K/24))) (max U L))
  have init : 3 ≤ M₀ := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨M₀,init,?_⟩
  intro M hM
  have m₃ : 3 ≤ M := init.trans hM
  have mV : V ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans hM)
  have mJ : J*(96*(K/24)) ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have mE : max U L ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  intro D φ p θ S T reg phase iq ε he hle hsmall side
  let s := actualTiles O frames η side he (lt_of_le_of_lt hle (by norm_num))
  let F := referenceEnergies energy η
  let G := actualTetrahedralCutoffs O frames η sob hK area side he (lt_of_le_of_lt hle (by norm_num))
  have hm : Integrable (massDensity D φ) := (reg.charge_L1.add reg.charge_L2.integrable_sq).add iq
  have hk := kineticDensity_integrable reg
  obtain ⟨Z,dom,_⟩ := rotated_tileDensityDomain chain reg phase iq
  let borel := levyLiebBorel_of_lowerSemicontinuous lsc
  obtain ⟨N,hN⟩ := actual_center_bound H product W borel O hK area dom side he (lt_of_le_of_lt hle (by norm_num))
  have joint := actual_energy_joint O frames η side he borel dom.entries hN
  have hi : Integrable (s.energy F D φ) := joint.integral_prod_right
  have hei : s.EnergyIntegrable F D φ := joint.prod_left_ae
  let e := exteriorCoefficient side U L
  have epos : 0 ≤ e := by cases side <;> first | exact hU | exact hL
  have eM : e ≤ M := by cases side <;> first | exact (le_max_left _ _).trans mE | exact (le_max_right _ _).trans mE
  let P := physicalProfile G F D φ S J V e hJ he (lt_of_le_of_lt hle (by norm_num)) hi reg.charge_L1 hm hk
  refine ⟨P,rfl,rfl,rfl,rfl,rfl,hei,?_,?_⟩
  · exact G.toControl P D φ S he (by linarith) (by positivity) m₃ hJ mJ epos eM mV rfl rfl rfl rfl rfl
  · obtain ⟨up,lo⟩ := glob reg phase iq he hle hsmall
    cases side with
    | upper => simpa only [P,physicalProfile,tileSign,one_mul,e,exteriorCoefficient] using up
    | lower => simpa only [P,physicalProfile,tileSign,neg_one_mul,e,exteriorCoefficient] using lo

end TSGA.ManyBody
