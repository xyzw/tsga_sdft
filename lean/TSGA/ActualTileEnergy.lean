import TSGA.ActualTileCutoffs
import TSGA.VariableCenterEnergy
import TSGA.IslandChargeL2

/-! # The center, frame and dilation integrals of the variable Coulomb density -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Set

/-- Analytic data of the source before localization. -/
structure TileDensityDomain (D : Density) (S : MatrixGradient) : Prop where
  regular : SqrtRegular D S
  entries : ∀ i j, Integrable (fun x => D.matrix x i j)
  square : Integrable fun x => D.charge x^2
  tf : Integrable fun x => D.charge x^(5/3:ℝ)
  lo : Integrable fun x => D.charge x^(4/3:ℝ)
  direct : Integrable (directKernel D.charge D.charge) pairVolume

theorem tileDensityDomain_of_regular {D : Density} {S : MatrixGradient}
    (reg : SqrtRegular D S) (sm : AEMeasurable D.matrix volume) (sq : Integrable fun x => D.charge x^2) :
    TileDensityDomain D S := by
  let m := reg.charge.aestronglyMeasurable
  let r := fun x => |m.mk _ x|
  have rm : Measurable r := continuous_abs.measurable.comp m.stronglyMeasurable_mk.measurable
  have eq : D.charge =ᵐ[volume] r := m.ae_eq_mk.mono fun x hx => by
    dsimp only [r]
    rw [← hx,abs_of_nonneg (D.charge_nonneg x)]
  have e₂ := sq.congr (eq.mono fun x hx => congrArg (·^2) hx)
  have moment (p : ℝ) (hp : 1 ≤ p) (hp' : p ≤ 2) : Integrable (fun x => D.charge x^p) :=
    (island_moment_integrable rm (fun _ => abs_nonneg _) (reg.charge.congr eq) e₂ hp hp').congr
      (eq.symm.mono fun x hx => congrArg (·^p) hx)
  refine ⟨reg,integrable_spin_entries sm reg.charge,sq,moment _ (by norm_num) (by norm_num),
    moment _ (by norm_num) (by norm_num),?_⟩
  apply (island_direct_integrable rm (fun _ => abs_nonneg _) (reg.charge.congr eq) e₂).congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp eq.symm,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp eq.symm] with z hz hz'
  change r z.1 = D.charge z.1 at hz
  change r z.2 = D.charge z.2 at hz'
  simp only [directKernel,hz,hz']

/-- A regular spin density and admissible phase provide the source of both
localizations. The kinetic estimate retains the original phase dependence. -/
theorem rotated_tileDensityDomain (chain : WeakPhaseProduct) {D : Density} {φ : Phase} {p θ : ℝ}
    {S T : MatrixGradient} (hr : DensityRegular D p θ S T) (hφ : φ.Regular p)
    (phase : Integrable fun x => D.charge x*‖φ.grad x‖^2) :
    ∃ Z, TileDensityDomain (rotatedDensity D φ) Z ∧
      sqrtKinetic Z ≤ 2*sqrtKinetic S+2*(∫ x, D.charge x*‖φ.grad x‖^2) := by
  obtain ⟨Z,weak,grad,cost⟩ := rotated_sqrt_kinetic chain hr hφ phase
  have charge : (rotatedDensity D φ).charge = D.charge := funext (rotated_charge D φ)
  refine ⟨Z,tileDensityDomain_of_regular ⟨charge.symm ▸ hr.charge_L1,weak,grad⟩ ?_
    (by simpa only [rotated_charge] using hr.charge_L2.integrable_sq),cost⟩
  apply aemeasurable_pi_lambda
  intro i
  apply aemeasurable_pi_lambda
  intro j
  change AEMeasurable (fun x => rotate (φ.value x) (D.matrix x) i j) volume
  simp_rw [rotate_by_entry]
  apply AEMeasurable.mul _ ((measurable_pi_apply j).comp_aemeasurable ((measurable_pi_apply i).comp_aemeasurable hr.aemeasurable_matrix))
  exact (show Continuous (fun t : ℝ => phaseFactor (axialWeight i j*t)) by unfold phaseFactor; fun_prop).measurable.comp_aemeasurable
    (locallyIntegrableOn_univ.mp (hφ.weak_grad 0).1).aestronglyMeasurable.aemeasurable

def actualWindowEnergy (O : TileOrientationLaw) (η : Mollifier) (side : CutoffSide)
    (ℓ : ℝ) (D : Density) (p : ℝ × O.Frames) (z : Position) : ℝ :=
  energy (fun x => (actualTileShape O η side ℓ p (z-x) : ℂ) • D.matrix x)

def actualFrameEnergy (O : TileOrientationLaw) (η : Mollifier) (side : CutoffSide)
    (ℓ : ℝ) (D : Density) (t : ℝ) : ℝ :=
  ∫ u, ∫ z, actualTileWeight ℓ t * actualWindowEnergy O η side ℓ D (t,u) z ∂volume ∂O.law

theorem actualWindowEnergy_eq (O : TileOrientationLaw) (η : Mollifier) (side : CutoffSide)
    (ℓ : ℝ) (D : Density) (p : ℝ × O.Frames) (z : Position) :
    actualWindowEnergy O η side ℓ D p z = energy (fun x =>
      (centeredWindow η (tileDilation p.1*tileSideLength side ℓ) (tileDilation p.1) (O.frame p.2) z x : ℂ) •
        D.matrix x) := by simp only [actualWindowEnergy,actualTileShape,centeredWindow,neg_sub]

theorem actualWindowEnergy_measurable (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (side : CutoffSide) (ℓ : ℝ) (borel : LevyLiebBorel)
    {D : Density} (entries : ∀ i j, Integrable (fun x => D.matrix x i j)) :
    Measurable (Function.uncurry (actualWindowEnergy O η side ℓ D)) := by
  let w := fun (p : (ℝ × O.Frames) × Position) x => actualTileShape O η side ℓ p.1 (p.2-x)
  change Measurable (fun p => energy (fun x => (w p x : ℂ) • D.matrix x))
  refine measurable_variableWindowEnergy (F := D.matrix) (B := 1) borel entries w ?_ ?_
  · exact (measurable_actualTileShape O frames η side ℓ).comp
      ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).sub measurable_snd))
  · intro p x
    have b := smoothedIndicator_bounds (tetrahedron (tileDilation p.1.1*tileSideLength side ℓ)) η
      (tileDilation_pos p.1.1) (O.frame p.1.2 (-(p.2-x)))
    exact (abs_of_nonneg b.1).trans_le b.2

theorem variableWindowCost_mono (H : FiniteEnergyInputs) (D : Density) (S : MatrixGradient)
    {b m₁ m₂ s₁ s₂ : ℝ} (hb : 0 ≤ b) (hm : m₁ ≤ m₂) (hs : s₁ ≤ s₂) :
    variableWindowCost H D S b m₁ s₁ ≤ variableWindowCost H D S b m₂ s₂ := by
  have moments (p : ℝ) : 0 ≤ chargeMoment D p := integral_nonneg fun x => Real.rpow_nonneg (D.charge_nonneg x) _
  have kin : 0 ≤ sqrtKinetic S := integral_nonneg fun x => sq_nonneg _
  have rho : 0 ≤ ∫ x, D.charge x := integral_nonneg D.charge_nonneg
  unfold variableWindowCost
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (moments _)) (Real.rpow_nonneg hb _))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm kin) (by norm_num)))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs rho) (by norm_num))) H.interiorConstant_nonneg)
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (moments _)) (mul_nonneg H.lo_nonneg (Real.rpow_nonneg hb _)))

/-- Uniform control of the center integral through the full dilation range
justifies changing the order of all three integrals. -/
theorem actual_center_bound (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (W : WindowSobolevRules) (borel : LevyLiebBorel) (O : TileOrientationLaw)
    {η : Mollifier} {C : ℝ} (c₀ : 0 ≤ C) (area : TileCutoffAreaBound η C)
    {D : Density} {S : MatrixGradient} (hD : TileDensityDomain D S)
    (side : CutoffSide) {ε : ℝ} (he : 0 < ε) (he' : ε < 1) :
    ∃ B : ℝ, ∀ p : ℝ × O.Frames, Integrable (actualWindowEnergy O η side ε⁻¹ D p) ∧
      (∫ z, |actualWindowEnergy O η side ε⁻¹ D p z|) ≤ B := by
  let ℓ := ε⁻¹
  refine ⟨variableWindowCost H D S 1 ((2*ℓ)^3/24) (C*(2*ℓ)^2/12),?_⟩
  intro p
  let t := tileDilation p.1
  let a := t*tileSideLength side ℓ
  have ht : 0 < t := tileDilation_pos _
  have hl : 0 < ℓ := inv_pos.mpr he
  have ha : 0 < a := mul_pos ht (tileSideLength_pos side he he')
  have ha' : a ≤ 2*ℓ := (mul_le_mul_of_nonneg_left (tileSideLength_le side ℓ) ht.le).trans
    (mul_le_mul_of_nonneg_right (by linarith [(tileDilation_mem p.1).2] : t ≤ 2) hl.le)
  have bound := H.variable_centers product W borel hD.regular hD.entries hD.tf hD.lo c₀ area ha ht (O.frame p.2)
  rw [funext (actualWindowEnergy_eq O η side ε⁻¹ D p)]
  refine ⟨bound.2.1,bound.2.2.trans (variableWindowCost_mono H D S zero_le_one ?_ ?_)⟩
  · rw [tetrahedron_volume ha]
    gcongr
  · rw [tetrahedron_volume ha,show C*(a^3/24)/(a*t) = C*a^2/(24*t) by field_simp [ha.ne',ht.ne']]
    apply div_le_div₀ (mul_nonneg c₀ (sq_nonneg _)) (by gcongr) (by norm_num)
    linarith [(tileDilation_mem p.1).1]

private theorem center_integral_prod {P : Type*} [MeasurableSpace P] {μ : Measure P} [IsFiniteMeasure μ]
    {f : P → Position → ℝ} (hm : Measurable (Function.uncurry f)) {B : ℝ}
    (h : ∀ p, Integrable (f p) ∧ (∫ z, |f p z|) ≤ B) :
    Integrable (Function.uncurry f) (μ.prod volume) := by
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨ae_of_all _ fun p => (h p).1, (integrable_const B).mono'
    hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_⟩
  exact ae_of_all _ fun p => by
    simp only [Function.uncurry_apply_pair,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
    exact (h p).2

theorem actualTileWeight_volume {ℓ t : ℝ} (hl : 0 < ℓ) :
    actualTileWeight ℓ t = (regionVolume (tetrahedron (tileDilation t*ℓ)))⁻¹ := by
  rw [tetrahedron_volume (mul_pos (tileDilation_pos t) hl)]
  simp [actualTileWeight,inv_div]

/-- Joint absolute integrability of the physical weight times the
localized energy, in dilation, frame and center. -/
theorem actual_energy_joint (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (side : CutoffSide) {ε : ℝ} (he : 0 < ε)
    (borel : LevyLiebBorel) {D : Density} (entries : ∀ i j, Integrable (fun x => D.matrix x i j))
    {B : ℝ} (hc : ∀ p : ℝ × O.Frames, Integrable (actualWindowEnergy O η side ε⁻¹ D p) ∧
      (∫ z, |actualWindowEnergy O η side ε⁻¹ D p z|) ≤ B) :
    Integrable (fun q : (ℝ × O.Frames) × Position =>
      actualTileWeight ε⁻¹ q.1.1 * actualWindowEnergy O η side ε⁻¹ D q.1 q.2)
      ((tileDilationLaw.prod O.law).prod volume) := by
  have em := actualWindowEnergy_measurable O frames η side ε⁻¹ borel entries
  have ei := center_integral_prod (μ := tileDilationLaw.prod O.law) em hc
  have wm := ((measurable_actualTileWeight ε⁻¹).comp measurable_fst).comp
    (measurable_fst : Measurable (Prod.fst : (ℝ × O.Frames) × Position → _))
  apply (ei.norm.const_mul (192/(ε⁻¹)^3)).mono' (wm.mul em).aestronglyMeasurable
  filter_upwards with q
  change ‖actualTileWeight ε⁻¹ q.1.1 * _‖ ≤ (192/(ε⁻¹)^3) * ‖actualWindowEnergy O η side ε⁻¹ D q.1 q.2‖
  rw [norm_mul,Real.norm_of_nonneg (actualTileWeight_nonneg (inv_nonneg.mpr he.le) _)]
  exact mul_le_mul_of_nonneg_right (actualTileWeight_bound (inv_pos.mpr he) _) (norm_nonneg _)

private theorem weighted_frame_integrals (O : TileOrientationLaw) {ε : ℝ} (he : 0 < ε)
    (E : ℝ × O.Frames → Position → ℝ) (m : Measurable (Function.uncurry E)) {B : ℝ}
    (hc : ∀ p, Integrable (E p) ∧ (∫ z, |E p z|) ≤ B)
    (ki : Integrable (fun q : (ℝ × O.Frames) × Position => actualTileWeight ε⁻¹ q.1.1 * E q.1 q.2)
      ((tileDilationLaw.prod O.law).prod volume)) :
    let F := fun t => ∫ u, ∫ z, actualTileWeight ε⁻¹ t * E (t,u) z ∂volume ∂O.law
    (∀ t, Integrable (fun u => ∫ z, E (t,u) z) O.law) ∧
      IntegrableOn (fun t => F t*scaleWeight t) scaleInterval ∧ Integrable F tileDilationLaw ∧
      (∫ z, ∫ p, actualTileWeight ε⁻¹ p.1 * E p z ∂(tileDilationLaw.prod O.law)) = scaleAverage F := by
  intro F
  let w := actualTileWeight ε⁻¹
  have wm : Measurable w := measurable_actualTileWeight _
  have wp (t) : 0 ≤ w t := actualTileWeight_nonneg (inv_nonneg.mpr he.le) t
  let k := fun (p : ℝ × O.Frames) z => w p.1 * E p z
  have km : Measurable (Function.uncurry k) := ((wm.comp measurable_fst).comp measurable_fst).mul m
  have kn (p : ℝ × O.Frames) : (∫ z, |k p z|) = w p.1*(∫ z, |E p z|) := by
    simp only [k,abs_mul,abs_of_nonneg (wp _),integral_const_mul]
  have kc (p : ℝ × O.Frames) : Integrable (k p) ∧ (∫ z, |k p z|) ≤ 192/(ε⁻¹)^3*B := by
    refine ⟨(hc p).1.const_mul _,?_⟩
    rw [kn]
    exact mul_le_mul (actualTileWeight_bound (inv_pos.mpr he) _) (hc p).2
      (integral_nonneg fun _ => abs_nonneg _) (by positivity)
  have km' := (km.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure Position))).measurable
  have fi := ki.integral_prod_left.integral_prod_left
  have frames_i (t : ℝ) : Integrable (fun u => ∫ z, E (t,u) z) O.law :=
    (center_integral_prod (μ := O.law) (f := fun u z => E (t,u) z) (m.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) (fun u => hc (t,u))).integral_prod_left
  have fm : Measurable F := (km'.stronglyMeasurable.integral_prod_right' (ν := O.law)).measurable
  have FB (t : ℝ) : ‖F t‖ ≤ 192/(ε⁻¹)^3*B := by
    calc
      _ ≤ ∫ u, ‖∫ z, k (t,u) z‖ ∂O.law := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : O.Frames, 192/(ε⁻¹)^3*B ∂O.law := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
        exact ae_of_all _ fun u => (norm_integral_le_integral_norm _).trans (kc (t,u)).2
      _ = _ := by simp
  refine ⟨frames_i,?_,fi,?_⟩
  · apply (scaleWeight_integrableOn.const_mul (192/(ε⁻¹)^3*B)).mono'
      (fm.aestronglyMeasurable.mul scaleWeight_integrableOn.aestronglyMeasurable)
    filter_upwards with t
    change ‖F t*scaleWeight t‖ ≤ _
    rw [norm_mul,Real.norm_of_nonneg (show 0 ≤ scaleWeight t by unfold scaleWeight; positivity)]
    exact mul_le_mul_of_nonneg_right (FB t) (by unfold scaleWeight; positivity)
  · calc
      _ = ∫ p, ∫ z, k p z ∂volume ∂(tileDilationLaw.prod O.law) := (integral_integral_swap ki).symm
      _ = ∫ t, F t ∂tileDilationLaw := integral_prod _ ki.integral_prod_left
      _ = scaleAverage F := integral_tileDilationLaw _

/-- Integration over centers commutes with the frame and dilation averages.
The statement also supplies the integrability used in each fixed-scale
localization, including the endpoint of the dilation average. -/
theorem actual_energy_integrals (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (side : CutoffSide) {ε : ℝ} (he : 0 < ε) (_he' : ε < 1)
    (borel : LevyLiebBorel) {D : Density} (entries : ∀ i j, Integrable (fun x => D.matrix x i j))
    {B : ℝ} (hc : ∀ p : ℝ × O.Frames, Integrable (actualWindowEnergy O η side ε⁻¹ D p) ∧
      (∫ z, |actualWindowEnergy O η side ε⁻¹ D p z|) ≤ B) :
    let E := actualWindowEnergy O η side ε⁻¹ D
    let F := actualFrameEnergy O η side ε⁻¹ D
    (∀ t, Integrable (fun u => ∫ z, E (t,u) z) O.law) ∧
      IntegrableOn (fun t => F t*scaleWeight t) scaleInterval ∧ Integrable F tileDilationLaw ∧
      (∫ z, ∫ p, actualTileWeight ε⁻¹ p.1 * E p z ∂(tileDilationLaw.prod O.law)) = scaleAverage F := by
  exact weighted_frame_integrals O he _ (actualWindowEnergy_measurable O frames η side ε⁻¹ borel entries) hc
    (actual_energy_joint O frames η side he borel entries hc)

end TSGA.ManyBody
