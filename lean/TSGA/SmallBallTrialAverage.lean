import TSGA.SmallBallCostDefinitions
import TSGA.SmallBallTileBounds
import TSGA.SmallBallGaugeCost
import TSGA.SmallBallReplacement
import TSGA.SmallBallAlignment
import TSGA.ActualLargeTileTrials
import TSGA.BallDensityTransfer
import TSGA.PhaseOscillation

/-! # Signed replacement on the physical family at one center -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW Set Metric
open scoped ComplexOrder MatrixOrder

private theorem cost_nonneg (H : FiniteEnergyInputs) {C ε V J k Q r dist d p v : ℝ}
    (hC : 0 ≤ C) (he : 0 < ε) (hV : 0 ≤ V) (hJ : 0 ≤ J) (hk : 0 ≤ k)
    (hr : 0 ≤ r) (hd : 0 ≤ dist) : 0 ≤ smallReplacementCost H C ε V J k Q r dist d p v := by
  unfold smallReplacementCost smallAdditionCost smallAffineCost
  positivity [H.interiorConstant_nonneg,H.lo_nonneg]

private theorem actual_original_integrable (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (chain : WeakPhaseProduct) (borel : LevyLiebBorel) (O : TileOrientationLaw)
    (frames : TileFrameMeasurable O) (η : Mollifier) (sob : SobolevDifferenceQuotients) (side : CutoffSide)
    {ε K p θ : ℝ} (he : 0 < ε) (hle : ε < 1) (rate : FiniteRateTiling energy η K)
    {D : Density} {φ : Phase} {S T G : MatrixGradient} (reg : DensityRegular D p θ S T)
    (phase : PhaseAdmissible D p φ G) (P : TileProfile)
    (profile : P.cutoff = (actualTiles O frames η side he hle).cutoffProfile) (c : Position) :
    let tiles := actualTiles O frames η side he hle
    Integrable (fun i : ℝ × O.Frames => tiles.weight i * energy (fun x =>
      (tiles.shape i (c-x) : ℂ) • rotate (φ.value x) (D.matrix x))) (tileDilationLaw.prod O.law) := by
  intro tiles
  let raw := fun z => 2*(roughTrialCoeff H K*cutoffAverage P.cutoff (roughTileDensity D φ) z) +
    actualLargeKinetic H O frames η side he hle D S z - P.directCost z
  obtain ⟨w⟩ := H.actual_large_trials product chain borel O frames η sob side he hle rate reg
    phase.regular phase.kinetic P profile raw c (by dsimp only [raw]; linarith)
  exact w.energy_integrable.congr (ae_of_all _ fun i =>
    congrArg (fun A => tiles.weight i*energy A) (funext (w.local_eq i)))

/-- The replacement inequality uses one pair of matrices for every
orientation and dilation. A common upper bound on the trial costs avoids
any measurable choice of Poisson realizations in these two parameters. -/
theorem SmallBallMatrices.actual_replacement {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι]
    {ε K C a p θ : ℝ} (F : IslandFockInputs μ) (radii : CoulombIslandRadii μ ι ε C)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct) (prod : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (comp : SobolevLipschitzComposition) (W : WindowSobolevRules)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (support : Function.support η.kernel ⊆ closedBall 0 (1/100)) (sob : SobolevDifferenceQuotients)
    (side : CutoffSide) (he : 0 < ε) (hle : ε < 1) (rate : FiniteRateTiling energy η K)
    (ha : 0 ≤ a) (area : TileCutoffAreaBound η a) (hE : exteriorFormConstant F.oneBody ≤ C)
    (hI : F.oneBody.interiorConstant ≤ C) {N D : Density} {φ : Phase} {S T G : MatrixGradient}
    (reg : DensityRegular D p θ S T) (phase : PhaseAdmissible D p φ G)
    (eqND : N.matrix =ᵐ[volume] D.matrix) (cont : Continuous N.matrix)
    (power : Continuous (N.power 1)) (hp : 3 < p) {c : Position}
    {s : SmallBallScale N (3*ε⁻¹) c} (m : SmallBallMatrices s)
    (localComp : SobolevCompositionOn (closedBall c (3*ε⁻¹)))
    (P : TileProfile) (profile : P.cutoff = (actualTiles O frames η side he hle).cutoffProfile) :
    let tiles := actualTiles O frames η side he hle
    let k := ∫ x in closedBall c (3*ε⁻¹), kineticDensity S x
    let σ := tileSign side
    let q := φ.grad c
    let cost := smallReplacementCost F.oneBody C ε (ε⁻¹^3) (a*ε⁻¹^2) k ‖q‖ s.r (3*s.omega 1)
      (s.omega (1/p)/s.r^(1/p)) p (tilePhaseOscillation φ c ε⁻¹)
    0 ≤ cost ∧ tiles.ReplacementAt (referenceEnergies energy η) D φ
      (if σ=1 then m.low else m.high) q c σ (192*ε^3*cost) := by
  classical
  intro tiles k σ q cost
  let V := ε⁻¹^3
  let J := a*ε⁻¹^2
  let r := s.r
  let dist := 3*s.omega 1
  let d := s.omega (1/p)/r^(1/p)
  let v := tilePhaseOscillation φ c ε⁻¹
  let ball := closedBall c (3*ε⁻¹)
  let H := F.oneBody
  have hC := H.interiorConstant_nonneg.trans hI
  have hr := s.r_nonneg
  have hd : 0 ≤ dist := mul_nonneg (by norm_num) (s.omega_nonneg 1 zero_lt_one)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hk : 0 ≤ k := integral_nonneg fun _ => sq_nonneg _
  have cost0 : 0 ≤ cost := cost_nonneg H hC he hV hJ hk hr hd
  have regN := densityRegular_of_ae eqND.symm reg
  have sqr : SqrtRegular N S := ⟨regN.charge_L1,regN.sqrt_gradient,regN.sqrt_L2⟩
  have Rpos : 0 < 3*ε⁻¹ := by positivity
  have sign : σ=1 ∨ σ=-1 := by cases side <;> first | exact Or.inl rfl | exact Or.inr rfl
  have major (i : ℝ × O.Frames) :
      σ*energy (fun x => (tiles.shape i (c-x) : ℂ) • rotate (φ.value x) (D.matrix x)) ≤
        σ*energy (cutoffSpiral (fun x => tiles.shape i (c-x)) (if σ=1 then m.low else m.high) q) + cost := by
    let t := actualSmallTaper O frames η support side he hle q c i
    obtain ⟨lip,cs,fi,vm,g,w,fg,jg⟩ := actualSmallTaper_bounds O frames η support side he hle q c i W sob ha area
    let tr : FrozenTaperRegular t := ⟨g,cs,fi,lip,w,fg⟩
    have hkin := t.kinetic_le_ball measurableSet_closedBall (kineticDensity_integrable reg) cs
    have mom (α b : ℝ) (hα : 0 ≤ α) (hb : 0 ≤ b) :
        affineSpiralKinetic t S tr.grad α b ≤ smallAffineCost V J k ‖q‖ α b := by
      unfold affineSpiralKinetic smallAffineCost
      change 8*(α*_+b*_)+2*‖q‖^2*b*_ ≤ _
      gcongr
    have bg := mom 1 (2*r) zero_le_one (by positivity)
    have mi := mom ε⁻¹ (2*dist+ε*(2*r)) (inv_nonneg.mpr he.le) (by positivity)
    have I : frozenAdditionCost t S tr.grad ε C dist r ≤ smallAdditionCost C ε V J k ‖q‖ r dist := by
      unfold frozenAdditionCost smallAdditionCost
      dsimp only
      gcongr
    have axes := m.axes t fi regN (by linarith : 1 ≤ p) Rpos localComp
    obtain ⟨_,_,_,osc⟩ := tilePhaseOscillation_attained phase.regular c (inv_pos.mpr he)
    obtain ⟨A,_,bgA,low,high,g1,g2,p1,p2⟩ := small_ball_replacement F radii leibniz chain comp tr sqr cont
      power axes m.low_pos m.high_pos phase.regular m.ordered
      (fun x hx => ⟨(m.trace_range (Or.inl rfl)).2,(s.cap x hx).trans (by linarith)⟩) osc he hle.le hd hE hI
    let Wb := 2*192^2*k + (2*r*‖q‖^2*((96/(1/p))*d)^2)*V
    let Pb := v^2/4*(r*V)
    have W0 : 0 ≤ Wb := by dsimp [Wb]; positivity
    have P0 : 0 ≤ Pb := by dsimp [Pb]; positivity
    have axis : m.axisCost t S p ≤ Wb := by
      unfold SmallBallMatrices.axisCost
      split
      · exact W0
      · unfold alignmentCost
        change 2*192^2*_ + (2*r*‖q‖^2*((96/(1/p))*d)^2)*_ ≤ _
        dsimp only [Wb]
        gcongr
    have cap : ∀ x, t.shape x*N.charge x ≤ t.shape x*r := by
      intro x; by_cases hx : x ∈ ball
      · exact mul_le_mul_of_nonneg_left (s.cap x hx) (t.range x).1
      · simp [t.outside _ hx]
    have mass : (∫ x, t.shape x*N.charge x) ≤ r*V := by
      have h := integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (t.range x).1 (N.charge_nonneg x))
        (fi.mul_const r) (ae_of_all _ cap)
      rw [integral_mul_const] at h
      exact h.trans ((mul_le_mul_of_nonneg_right vm hr).trans_eq (mul_comm _ _))
    have pw : v^2/4*(∫ x, t.shape x*N.charge x) ≤ Pb := mul_le_mul_of_nonneg_left mass (by positivity)
    have isl : (if σ=1 then A.lower.cost else A.upper.cost) ≤ smallAdditionCost C ε V J k ‖q‖ r dist := by
      split
      · exact low.trans I
      · exact high.trans I
    have scalar := small_replacement_error H A he hle.le hr s.cap fi σ sign isl (bgA.trans bg) W0 P0
      (g1.le.trans axis) (g2.le.trans axis) (p1.le.trans pw) (p2.le.trans pw)
    have bound : A.error σ ≤ cost := by
      apply scalar.trans
      dsimp only [cost,smallReplacementCost]
      gcongr
      exact add_nonneg H.interiorConstant_nonneg H.lo_nonneg
    have same := energy_congr (eqND.mono fun x hx => congrArg
      (fun B => (tiles.shape i (c-x) : ℂ) • rotate (φ.value x) B) hx)
    have step := A.signed he hle.le hd hC sign
    change σ*energy (fun x => (tiles.shape i (c-x) : ℂ) • rotate (φ.value x) (N.matrix x)) ≤ _ at step
    rw [same] at step
    exact step.trans (add_le_add le_rfl bound)
  have wbound (i : ℝ × O.Frames) : tiles.weight i*cost ≤ (192*ε^3)*cost := by
    have w := actualTileWeight_bound (inv_pos.mpr he) i.1
    simp only [div_eq_mul_inv, ← inv_pow, inv_inv] at w
    exact mul_le_mul_of_nonneg_right w cost0
  have wm : Measurable (fun i : ℝ × O.Frames => actualTileWeight ε⁻¹ i.1 * cost) :=
    ((measurable_actualTileWeight ε⁻¹).comp measurable_fst).mul_const cost
  have wi : Integrable (fun i : ℝ × O.Frames => tiles.weight i*cost) (tileDilationLaw.prod O.law) :=
    (integrable_const ((192*ε^3)*cost)).mono' wm.aestronglyMeasurable (ae_of_all _ fun i =>
      (Real.norm_of_nonneg (mul_nonneg (tiles.weight_nonneg _) cost0)).le.trans (wbound i))
  refine ⟨cost0,fun _ => cost, actual_original_integrable H prod chain borel O frames η sob side he hle rate reg phase P profile c,
    wi,ae_of_all _ major,?_⟩
  change (∫ i : ℝ × O.Frames, tiles.weight i * cost ∂tileDilationLaw.prod O.law) ≤ 192*ε^3*cost
  exact (integral_mono wi (integrable_const _) wbound).trans_eq (by simp)

end TSGA.ManyBody
