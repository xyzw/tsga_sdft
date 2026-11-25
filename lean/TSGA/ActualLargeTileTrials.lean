import TSGA.LargeTileTrials
import TSGA.ActualTileEnergy
import TSGA.ActualTileFisher

/-! # Averaging the actual large-oscillation Coulomb trials -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization

private theorem cutoffAverage_eq_integral (k u : Position → ℝ) (c : Position) :
    cutoffAverage k u c = ∫ x, u x*k (c-x) := rfl

private theorem measurable_centered_section {I : Type*} [MeasurableSpace I]
    {k : I → Position → ℝ} (km : Measurable (Function.uncurry k)) (i : I) (c : Position) :
    Measurable (fun x => k i (c-x)) :=
  km.comp (measurable_const.prodMk (measurable_const.sub measurable_id) :
    Measurable (fun x : Position => (i,c-x)))

private theorem weighted_window_mean {I : Type*} [MeasurableSpace I] (μ : Measure I) [IsFiniteMeasure μ]
    {w : I → ℝ} (wm : Measurable w) {B : ℝ} (wb : ∀ i, ‖w i‖ ≤ B)
    {k : I → Position → ℝ} (km : Measurable (Function.uncurry k)) {A : ℝ} (kb : ∀ i z, ‖k i z‖ ≤ A)
    {u : Position → ℝ} (hu : Integrable u) (c : Position) :
    Integrable (fun i => w i*cutoffAverage (k i) u c) μ ∧
    (∫ i, w i*cutoffAverage (k i) u c ∂μ) = cutoffAverage (fun z => ∫ i, w i*k i z ∂μ) u c := by
  have hm : Measurable (fun p : I × Position => w p.1*k p.1 p.2) := (wm.comp measurable_fst).mul km
  have hb (i z) : ‖w i * k i z‖ ≤ B*A := by
    rw [norm_mul]
    exact mul_le_mul (wb i) (kb i z) (norm_nonneg _) ((norm_nonneg _).trans (wb i))
  have h := tileKernel_convolution μ (k := fun i z => w i*k i z) hm hb hu c
  have eq (i : I) : (∫ x, u x*(w i*k i (c-x))) = w i*cutoffAverage (k i) u c := by
    change _ = w i*∫ x, u x*k i (c-x)
    simp_rw [mul_left_comm (u _) (w i),integral_const_mul]
  simpa only [eq] using h

/-- The two kinetic terms left by the taper after the phase contribution is
included in the rough bulk density. -/
def actualLargeKinetic (H : FiniteEnergyInputs) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (side : CutoffSide) {ε : ℝ} (he : 0 < ε) (he' : ε < 1)
    (D : Density) (S : MatrixGradient) (c : Position) : ℝ :=
  4*H.interiorConstant*cutoffAverage (actualTiles O frames η side he he').cutoffProfile (kineticDensity S) c +
  2*H.interiorConstant*cutoffAverage (fun z => ∫ i : ℝ × O.Frames,
    actualTileWeight ε⁻¹ i.1*‖actualTileGradient O η side ε⁻¹ i z‖^2 ∂tileDilationLaw.prod O.law) D.charge c

/-- In the spatial integral the first kinetic term carries the actual mass
of the upper or lower taper. The Fisher remainder is of order ε. -/
theorem integral_actualLargeKinetic (H : FiniteEnergyInputs)
    (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (η : Mollifier)
    (sob : SobolevDifferenceQuotients) {C : ℝ} (hC : 0 ≤ C) (area : TileCutoffAreaBound η C)
    (side : CutoffSide) {ε : ℝ} (he : 0 < ε) (he' : ε < 1) {D : Density}
    {S : MatrixGradient} (reg : SqrtRegular D S) :
    Integrable (actualLargeKinetic H O frames η side he he' D S) ∧
    (∫ c, actualLargeKinetic H O frames η side he he' D S c) ≤
      4*H.interiorConstant*(side.mass ε*sqrtKinetic S) +
      2*H.interiorConstant*((4*C*ε)*(∫ x, D.charge x)) := by
  let T := actualTiles O frames η side he he'
  let A := actualTetrahedralCutoffs O frames η sob hC area side he he'
  let := T.space
  let := T.probability
  have cut : Integrable T.cutoffProfile := A.shape_product.integral_prod_left
  have fish : Integrable A.kineticProfile := A.gradient_product.integral_prod_left
  have ki : Integrable (kineticDensity S) := reg.grad.integrable_sq
  have f := (cutoffAverage_integrable cut ki).const_mul (4*H.interiorConstant)
  have g := (cutoffAverage_integrable fish reg.charge).const_mul (2*H.interiorConstant)
  refine ⟨f.add g,?_⟩
  change (∫ c, 4*H.interiorConstant*cutoffAverage T.cutoffProfile (kineticDensity S) c +
    2*H.interiorConstant*cutoffAverage A.kineticProfile D.charge c) ≤ _
  rw [integral_add f g,integral_const_mul,integral_const_mul,
    integral_cutoffAverage cut ki,integral_cutoffAverage fish reg.charge,A.cutoff_mass he]
  have ha : (∫ z, A.kineticProfile z) ≤ 4*C*ε :=
    (A.kinetic_mass he (by positivity)).trans_eq (by ring)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right ha (integral_nonneg D.charge_nonneg)) (by positivity [H.interiorConstant_nonneg]))

set_option maxHeartbeats 1800000 in
/-- For either physical cutoff family, construct every trial at this center
and integrate its cost in dilation and orientation. The scalar inequality
allows the caller to choose the local error used in the oscillation argument. -/
theorem FiniteEnergyInputs.actual_large_trials (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (chain : WeakPhaseProduct) (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (sob : SobolevDifferenceQuotients) (side : CutoffSide) {ε K p θ : ℝ}
    (he : 0 < ε) (he' : ε < 1) (rate : FiniteRateTiling energy η K)
    {D : Density} {φ : Phase} {S T : MatrixGradient} (reg : DensityRegular D p θ S T) (hφ : φ.Regular p)
    (phase : Integrable fun x => D.charge x*‖φ.grad x‖^2)
    (P : TileProfile) (profile : P.cutoff = (actualTiles O frames η side he he').cutoffProfile)
    (raw : Position → ℝ) (c : Position)
    (scalar : 2*(roughTrialCoeff H K*cutoffAverage P.cutoff (roughTileDensity D φ) c) +
      actualLargeKinetic H O frames η side he he' D S c ≤ P.directCost c + raw c) :
    Nonempty (LargeCoulombTrials H rate D φ (actualTiles O frames η side he he') P raw c) := by
  classical
  let tiles := actualTiles O frames η side he he'
  let μ := tileDilationLaw.prod O.law
  let w := fun i : ℝ × O.Frames => actualTileWeight ε⁻¹ i.1
  let k := actualTileShape O η side ε⁻¹
  let g := actualTileGradient O η side ε⁻¹
  let j := fun i z => ‖g i z‖^2
  have wn (i) : 0 ≤ w i := tiles.weight_nonneg i
  have wm : Measurable w := (measurable_actualTileWeight _).comp measurable_fst
  have wb (i) : ‖w i‖ ≤ 192/(ε⁻¹)^3 := (Real.norm_of_nonneg (wn i)).le.trans (actualTileWeight_bound (inv_pos.mpr he) _)
  have km : Measurable (Function.uncurry k) := measurable_actualTileShape O frames η side ε⁻¹
  have kb (i z) : k i z ∈ Set.Icc 0 1 := tiles.shape_mem i z
  have km' := fun i z => (Real.norm_of_nonneg (kb i z).1).le.trans (kb i z).2
  have jm : Measurable (Function.uncurry j) := measurable_actualTileFisher O frames η side ε⁻¹
  obtain ⟨A,_,grad⟩ := actualTileGradient_bound O η sob side ε⁻¹
  have jb (i z) : j i z ∈ Set.Icc 0 (A^2) := ⟨sq_nonneg _,pow_le_pow_left₀ (norm_nonneg _) (grad i z) 2⟩
  have jb' := fun i z => (Real.norm_of_nonneg (jb i z).1).le.trans (jb i z).2
  let f := fun i x => k i (c-x)
  let d := fun i x => -(g i (c-x))
  let N := fun i => windowDensity (rotatedDensity D φ) (f i) (fun x => (kb i (c-x)).1)
  have sr : SqrtRegular D S := ⟨reg.charge_L1,reg.sqrt_gradient,reg.sqrt_L2⟩
  have base := tileDensityDomain_of_regular sr reg.aemeasurable_matrix reg.charge_L2.integrable_sq
  obtain ⟨_,rot,_⟩ := rotated_tileDensityDomain chain reg hφ phase
  have p₄ := base.lo
  have p₅ := base.tf
  have ki : Integrable (kineticDensity S) := reg.sqrt_L2.integrable_sq
  have ri : Integrable (roughTileDensity D φ) := (p₄.add p₅).add phase
  let coeff := roughTrialCoeff H K
  let cost := fun i => coeff*cutoffAverage (k i) (roughTileDensity D φ) c +
    4*H.interiorConstant*cutoffAverage (k i) (kineticDensity S) c +
    2*H.interiorConstant*cutoffAverage (j i) D.charge c
  have localM (i x) : (N i).matrix x = (f i x : ℂ) • rotate (φ.value x) (D.matrix x) := by
    ext a b
    exact Complex.real_smul
  have trials (i) : ∃ Γ, feasible (N i).matrix Γ ∧ Γ.kinetic+Γ.interaction-hartree (N i).charge ≤ cost i ∧
      H.loCoeff*chargeMoment (N i) (4/3) ≤ cost i ∧ |energy (N i).matrix| ≤ cost i := by
    have fj := measurable_centered_section (k := j) jm i c
    have fi := window_product_integrable (f := fun x => j i (c-x)) (u := D.charge)
      (b := A^2) (fun x => jb i (c-x)) fj.aemeasurable reg.charge_L1
    have fish : Integrable (fun x => D.charge x*‖d i x‖^2) := by
      simpa only [d,norm_neg,j,mul_comm (D.charge _)] using fi
    have weak (a) : WeakPartialOn Set.univ a (fun x => √(f i x)) (fun x => d i x a) :=
      actualTileGradient_reflected O η sob side ε⁻¹ i c a
    have t := H.large_window_trial (K := K) (f := f i) (g := d i) product chain sr hφ (zero_le_one.trans rate.one_le)
      p₄ p₅ phase (fun x => kb i (c-x)) weak fish
    simpa only [N,cost,coeff,cutoffAverage_eq_integral,d,norm_neg,f,j] using t
  choose trial rep up lo abs using trials
  have ra := weighted_window_mean μ (k := k) wm wb km km' ri c
  have sa := weighted_window_mean μ (k := k) wm wb km km' ki c
  have da := weighted_window_mean μ (k := j) wm wb jm jb' reg.charge_L1 c
  let r := fun i => w i*cutoffAverage (k i) (roughTileDensity D φ) c
  let s := fun i => w i*cutoffAverage (k i) (kineticDensity S) c
  let a := fun i => w i*cutoffAverage (j i) D.charge c
  have ar : Integrable r μ := ra.1
  have as' : Integrable s μ := sa.1
  have aa : Integrable a μ := da.1
  have eq (i) : w i*cost i = coeff*r i+4*H.interiorConstant*s i+2*H.interiorConstant*a i := by
    dsimp only [cost,r,s,a]; ring
  have ci : Integrable (fun i => w i*cost i) μ := by
    simp_rw [eq]
    exact ((ar.const_mul _).add (as'.const_mul _)).add (aa.const_mul _)
  have em := (actualWindowEnergy_measurable O frames η side ε⁻¹ borel
    (D := rotatedDensity D φ) rot.entries).comp
    (measurable_id.prodMk (measurable_const (a := c)))
  have en : Measurable (fun i => w i*energy (N i).matrix) := by
    have id (i) := funext (localM i)
    simp_rw [id]
    exact wm.mul em
  have ei := ci.mono' en.aestronglyMeasurable (ae_of_all μ fun i => by
    change ‖w i*energy (N i).matrix‖ ≤ w i*cost i
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (wn i)]
    exact mul_le_mul_of_nonneg_left (abs i) (wn i))
  have pm : Measurable tiles.cutoffProfile :=
    (((wm.comp measurable_fst).mul km).stronglyMeasurable.integral_prod_left' (μ := μ)).measurable
  have pc z : tiles.cutoffProfile z ∈ Set.Icc 0 (192/(ε⁻¹)^3) := by
    let := tiles.space
    let := tiles.probability
    refine ⟨integral_nonneg fun i => mul_nonneg (wn i) (kb i z).1,?_⟩
    have hh := integral_mono_ae (tiles.profile_integrable z) (integrable_const (μ := μ) (192/(ε⁻¹)^3))
      (ae_of_all μ fun i => (mul_le_of_le_one_right (wn i) (kb i z).2).trans (actualTileWeight_bound (inv_pos.mpr he) _))
    change (∫ i, tiles.weight i*tiles.shape i z ∂tiles.measure) ≤ _
    simpa only [integral_const,probReal_univ,one_smul] using hh
  refine ⟨{ coefficient := coeff, covers_gas := by
              dsimp only [coeff,roughTrialCoeff]; linarith [H.lo_nonneg,H.interiorConstant_nonneg]
            kinetic := actualLargeKinetic H O frames η side he he' D S c
            localDensity := N, local_eq := localM, trial := trial, feasible_trial := rep, cost := cost,
            trial_cost := up, indirect_cost := lo, energy_integrable := ei, cost_integrable := ci,
            trial_average := ?_, rough_integrable := ?_, scalar := scalar }⟩
  · change (∫ i, w i*cost i ∂μ) ≤ _
    simp_rw [eq]
    have first : Integrable (fun i => coeff*r i+4*H.interiorConstant*s i) μ :=
      (ar.const_mul _).add (as'.const_mul _)
    rw [integral_add first (aa.const_mul _),
      integral_add (ar.const_mul _) (as'.const_mul _)]
    simp only [integral_const_mul,r,s,a,ra.2,sa.2,da.2,profile,actualLargeKinetic]
    rw [show (actualTiles O frames η side he he').cutoffProfile = (fun z => ∫ i, w i*k i z ∂μ) from rfl]
    exact (add_assoc _ _ _).le
  · rw [profile]
    simpa only [mul_comm (roughTileDensity D φ _)] using
      window_product_integrable (fun x => pc (c-x)) (pm.comp (measurable_const.sub measurable_id)).aemeasurable ri

/-- Before absorbing the charge and phase costs by oscillation, the rough
comparison already holds at every center, with the explicit taper cost. -/
theorem FiniteEnergyInputs.actual_large_difference (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (chain : WeakPhaseProduct) (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (sob : SobolevDifferenceQuotients) (side : CutoffSide) {ε K p θ : ℝ}
    (he : 0 < ε) (he' : ε < 1) (rate : FiniteRateTiling energy η K)
    {D : Density} {φ : Phase} {S T : MatrixGradient} (reg : DensityRegular D p θ S T) (hφ : φ.Regular p)
    (phase : Integrable fun x => D.charge x*‖φ.grad x‖^2)
    (P : TileProfile) (profile : P.cutoff = (actualTiles O frames η side he he').cutoffProfile) (c : Position) :
    let tiles := actualTiles O frames η side he he'
    let F := referenceEnergies energy η
    |tiles.energy F D φ c - cutoffAverage P.cutoff (localEnergy F D φ) c| ≤
      2*(roughTrialCoeff H K*cutoffAverage P.cutoff (roughTileDensity D φ) c) +
        actualLargeKinetic H O frames η side he he' D S c := by
  intro tiles F
  let u := fun z => 2*(roughTrialCoeff H K*cutoffAverage P.cutoff (roughTileDensity D φ) z) +
    actualLargeKinetic H O frames η side he he' D S z
  let raw := fun z => u z-P.directCost z
  obtain ⟨trial⟩ := H.actual_large_trials product chain borel O frames η sob side he he' rate reg hφ
    phase P profile raw c (by change u c ≤ P.directCost c + (u c - P.directCost c); linarith)
  let rough := trial.toRough
  have h := rough.error_bound
  change _ ≤ P.directCost c + (u c-P.directCost c) at h
  apply (abs_sub _ _).trans
  change _ ≤ u c
  linarith only [rough.finite,rough.gas,h]

end TSGA.ManyBody
