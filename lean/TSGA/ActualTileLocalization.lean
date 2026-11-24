import TSGA.ActualTileEnergy
import TSGA.VariableSkeletonEnergy
import TSGA.VariableTileLocalization
import TSGA.CoulombVarianceIntegrability

/-! # Coulomb localization on the two physical tetrahedral families -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Metric Set

private theorem fixed_frame_energy (O : TileOrientationLaw) (η : Mollifier) (side : CutoffSide)
    {ℓ t : ℝ} (hl : 0 < ℓ) (ht : t ∈ scaleInterval) (D : Density) :
    actualFrameEnergy O η side ℓ D t =
      ∫ u, ∫ z, energy (fun x => (centeredWindow η (t*tileSideLength side ℓ) t (O.frame u) z x : ℂ) •
        D.matrix x) / regionVolume (tetrahedron (t*ℓ)) ∂volume ∂O.law := by
  simp only [actualFrameEnergy,actualWindowEnergy_eq,actualTileWeight_volume hl,tileDilation_of_mem ht,
    div_eq_inv_mul]

private theorem actual_skeleton_avg (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    {η : Mollifier} (sk : SkeletonFisherAverages η) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {D : Density} {S : MatrixGradient} (hD : TileDensityDomain D S)
    {b d : ℝ} (hd : 0 < d) (hsc : d ≤ b/2) :
    let μ := latticeShiftMeasure b
    let e := fun u τ => energy (latticeBlockDensity b d η (O.frame u) D.matrix τ none)
    let cost := variableWindowCost H D S 2 (2*(sk.coefficient*(d/b))) (2*(sk.coefficient/(b*d)))
    Integrable (fun u => ∫ τ, e u τ ∂μ) O.law ∧ (∫ u, ∫ τ, e u τ ∂μ ∂O.law) ≤ cost := by
  intro μ e cost
  have hb : 0 < b := by linarith
  let : IsProbabilityMeasure μ := latticeShiftMeasure_probability hb
  let w := fun (p : O.Frames × Position) x => latticeBlock b d η none (O.frame p.1 x-p.2)
  have wm : Measurable (fun z : (O.Frames × Position) × Position => w z.1 z.2) :=
    (latticeBlock_measurable b hd η none).comp ((frames.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub (measurable_snd.comp measurable_fst))
  have em : Measurable (Function.uncurry e) := measurable_variableWindowEnergy borel hD.entries w wm
    fun p x => let b := latticeBlock_bounds hd hsc hs none (O.frame p.1 x-p.2)
               (abs_of_nonneg b.1).trans_le b.2
  have point (u : O.Frames) : ‖∫ τ, e u τ ∂μ‖ ≤ cost := (norm_integral_le_integral_norm _).trans
    (H.variable_skeleton product borel hD.regular hD.entries hD.tf hD.lo sk hs hd hsc (O.frame u)).2.2
  have int := (integrable_const (μ := O.law) cost).mono'
    (em.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable (ae_of_all _ point)
  refine ⟨int,?_⟩
  exact (integral_mono int (integrable_const cost) (fun u => (le_abs_self _).trans (point u))).trans_eq (by simp)

private theorem skeleton_at_dilation (H : FiniteEnergyInputs) (D : Density) (S : MatrixGradient)
    {ε t c : ℝ} (he : 0 < ε) (ht : t ∈ scaleInterval) (hc : 0 ≤ c) :
    variableWindowCost H D S 2 (2*(c*(t/(t*ε⁻¹)))) (2*(c/(t*ε⁻¹*t))) ≤
      ε*variableWindowCost H D S 2 (2*c) (8*c) := by
  have tl : (1/2:ℝ) ≤ t := ht.1
  have tp : 0 < t := by linarith
  have m : 2*(c*(t/(t*ε⁻¹))) = ε*(2*c) := by field_simp
  have s : 2*(c/(t*ε⁻¹*t)) ≤ ε*(8*c) := by
    have st : 1 ≤ 4*t^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) tl]
    have eq : 2*(c/(t*ε⁻¹*t)) = (2*c*ε)/t^2 := by field_simp
    rw [eq,div_le_iff₀ (sq_pos_of_pos tp)]
    nlinarith only [mul_le_mul_of_nonneg_left st (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hc) he.le)]
  apply (variableWindowCost_mono H D S (by norm_num : (0:ℝ) ≤ 2) m.le s).trans_eq
  unfold variableWindowCost
  ring

/-- Translation covariance of null sets transfers the almost-everywhere
existence of centered states to every lattice label at almost every shift. -/
theorem feasible_lattice_cells {η : Mollifier} {D : Density} {b d : ℝ}
    (R : Position ≃ₗᵢ[ℝ] Position)
    (h : ∀ A : Position ≃ₗᵢ[ℝ] Position, ∀ᵐ z, ∃ Γ, feasible
      (fun x => (centeredWindow η (b-d) d A z x : ℂ) • D.matrix x) Γ) :
    ∀ᵐ τ ∂latticeShiftMeasure b, ∀ p : LatticeTile, ∃ Γ, feasible
      (latticeBlockDensity b d η R D.matrix τ (some p)) Γ := by
  apply Measure.ae_smul_measure
  apply ae_restrict_of_ae
  apply ae_all_iff.2
  intro p
  have mp := R.symm.measurePreserving.comp ((measurePreserving_add_right volume (cubeLabelCenter b p.2)).comp
    (measurePreserving_add_left volume (latticeShift b p.1)))
  filter_upwards [mp.quasiMeasurePreserving.ae (h (R.trans (cubeFrame b p.2)))] with τ hj
  change ∃ Γ, feasible (fun x => (latticeWindow b d η p (R x-τ) : ℂ) • D.matrix x) Γ
  simp_rw [latticeWindow_centered]
  exact hj

/-- Apply both comparisons before dilation to the unchanged three-dimensional
matrix field. The upper error consists of the skeleton and the charge variance. -/
theorem actual_upper_at_scale (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (W : WindowSobolevRules) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (tensor : DisjointFockTensorization) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (haar : CubeFrameInvariant O) {η : Mollifier} {C : ℝ} (c₀ : 0 ≤ C) (area : TileCutoffAreaBound η C)
    (sk : SkeletonFisherAverages η) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {D : Density} {S : MatrixGradient} (hD : TileDensityDomain D S)
    {ε t : ℝ} (he : 0 < ε) (he' : ε ≤ 1/2) (ht : t ∈ scaleInterval) :
    energy D.matrix ≤ actualFrameEnergy O η .upper ε⁻¹ D t +
      ε*variableWindowCost H D S 2 (2*sk.coefficient) (8*sk.coefficient) +
      latticeVariance O η D.charge ε⁻¹ 1 t := by
  have he₁ : ε < 1 := by linarith
  have tp : 0 < t := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) ht.1
  have hl : 0 < ε⁻¹ := inv_pos.mpr he
  have hscale : 1 ≤ ε⁻¹/2 := by rw [le_div_iff₀ (by norm_num),le_inv_comm₀ (by norm_num) he]; linarith
  have sc : t ≤ t*ε⁻¹/2 := by nlinarith [mul_le_mul_of_nonneg_left hscale tp.le]
  have a : 0 < t*ε⁻¹-t := by linarith
  have borel := levyLiebBorel_of_lowerSemicontinuous lsc
  have center := fun R => H.variable_centers product W borel hD.regular hD.entries hD.tf hD.lo c₀ area a tp R
  have skel := fun R => H.variable_skeleton product borel hD.regular hD.entries hD.tf hD.lo sk hs tp sc R
  have avg := actual_skeleton_avg H product borel O frames sk hs hD tp sc
  obtain ⟨B,hB⟩ := actual_center_bound H product W borel O c₀ area hD .upper he he₁
  have ints := actual_energy_integrals O frames η .upper he he₁ borel hD.entries hB
  have fr := ints.1 t
  have len : t*tileSideLength .upper ε⁻¹ = t*ε⁻¹-t := by unfold tileSideLength; ring
  simp only [actualWindowEnergy_eq,tileDilation_of_mem ht,len] at fr
  have var := lattice_variance_integrable_ae O frames hs zero_lt_one hscale
    hD.regular.charge.aemeasurable hD.direct
  have bound := coulomb_variable_upper_localization tensor lsc O haar hs tp sc D.matrix
    hD.entries hD.direct (fun R => (center R).2.1) fr
    (ae_of_all _ fun u => by
      filter_upwards [(skel (O.frame u)).1,feasible_lattice_cells (O.frame u) (fun R => (center R).1)] with τ hsk hc
      rintro (_|p)
      · exact hsk
      · exact hc p) (ae_of_all _ fun u => (skel (O.frame u)).2.1) avg.1
    (by simpa only [mul_one,Density.charge] using var.1 t ht)
  rw [fixed_frame_energy O η .upper hl ht,len]
  simp only [latticeVariance,mul_one]
  apply bound.trans
  exact add_le_add (add_le_add le_rfl (avg.2.trans (skeleton_at_dilation H D S he ht sk.nonneg))) le_rfl

/-- The finite-size upper estimate at the full dilation endpoint. Both
terms on the right are evaluated on the original variable spin density. -/
theorem actual_upper_localization (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (W : WindowSobolevRules) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (tensor : DisjointFockTensorization) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (haar : CubeFrameInvariant O) {η : Mollifier} {C : ℝ} (c₀ : 0 ≤ C) (area : TileCutoffAreaBound η C)
    (sk : SkeletonFisherAverages η) (hs : tsupport η.kernel ⊆ closedBall 0 (1/100))
    (cone : TetrahedronCone) (kernel : PeriodicKernelCalculus η)
    {A B : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (transport : PeriodicTransportInequality A)
    (fourier : CoulombFourierAveraging O B) {D : Density} {S : MatrixGradient}
    (hD : TileDensityDomain D S) {ε : ℝ} (he : 0 < ε) (he' : ε ≤ 1/2) :
    energy D.matrix ≤ (∫ z, ∫ p, actualTileWeight ε⁻¹ p.1 *
        actualWindowEnergy O η .upper ε⁻¹ D p z ∂(tileDilationLaw.prod O.law)) +
      ε*variableWindowCost H D S 2 (2*sk.coefficient) (8*sk.coefficient) +
      (54*A*B*ε)*(∫ x, D.charge x^2) := by
  let borel := levyLiebBorel_of_lowerSemicontinuous lsc
  have support := (subset_tsupport η.kernel).trans hs
  have he₁ : ε < 1 := by linarith
  have hscale : 1 ≤ ε⁻¹/2 := by
    rw [le_div_iff₀ (by norm_num),le_inv_comm₀ (by norm_num) he]
    linarith
  obtain ⟨bound,hbound⟩ := actual_center_bound H product W borel O c₀ area hD .upper he he₁
  have ints := actual_energy_integrals O frames η .upper he he₁ borel hD.entries hbound
  rw [ints.2.2.2]
  have q₀ : 0 ≤ ∫ x, D.charge x^2 := integral_nonneg fun x => sq_nonneg _
  apply finite_upper_at_half_le_one ints.2.1 (by positivity)
  intro α hα hu
  have vi := (lattice_variance_integrable_ae O frames support zero_lt_one hscale
    hD.regular.charge.aemeasurable hD.direct).2
  have coeff := coulomb_variable_cubic_variance O cone kernel hs ha hb transport fourier D.charge
    hD.regular.charge hD.square zero_lt_one hscale hα hu
  have fixed := fun t ht => actual_upper_at_scale H product W lsc tensor O frames haar c₀ area
    sk support hD he he' (t := t) ht
  apply (scale_average_bound hα hu ints.2.1 vi fixed).trans
  apply add_le_add_right
  simpa only [one_pow,one_div,inv_inv] using coeff

/-- The integrated Graf–Schenker correction retains the exact two moments
and the prefactor 1 − Cε on the full-size tetrahedra. -/
theorem actual_lower_localization (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (W : WindowSobolevRules) (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    {η : Mollifier} {A C : ℝ} (a₀ : 0 ≤ A) (area : TileCutoffAreaBound η A)
    (c₀ : 0 ≤ C) (graf : SmearedGrafSchenker η O C) {D : Density} {S : MatrixGradient}
    (hD : TileDensityDomain D S) {ε : ℝ} (he : 0 < ε) (he' : ε < 1) (small : C*ε ≤ 1/2) :
    (1-C*ε)*(∫ z, ∫ p, actualTileWeight ε⁻¹ p.1 *
      actualWindowEnergy O η .lower ε⁻¹ D p z ∂(tileDilationLaw.prod O.law)) -
      (∫ t, lowerTilingError D ε C (tileDilation t) ∂tileDilationLaw) ≤ energy D.matrix := by
  obtain ⟨bound,hbound⟩ := actual_center_bound H product W borel O a₀ area hD .lower he he'
  have ints := actual_energy_integrals O frames η .lower he he' borel hD.entries hbound
  let f := actualFrameEnergy O η .lower ε⁻¹ D
  let err := fun t => lowerTilingError D ε C (tileDilation t)
  have fixed : ∀ᵐ t ∂tileDilationLaw, (1-C*ε)*f t-err t ≤ energy D.matrix := by
    filter_upwards [tileDilationLaw_mem] with t ht
    have tp : 0 < t := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) ht.1
    have hl : 0 < t*ε⁻¹ := mul_pos tp (inv_pos.mpr he)
    have scale : 2*C*t ≤ t*ε⁻¹ := by
      rw [mul_comm (2*C)]
      apply mul_le_mul_of_nonneg_left _ tp.le
      rw [← one_div,le_div_iff₀ he]
      linarith
    have fr := ints.1 t
    have centers := fun R => H.variable_centers product W borel hD.regular hD.entries hD.tf hD.lo a₀ area hl tp R
    simp only [actualWindowEnergy_eq,tileDilation_of_mem ht,tileSideLength] at fr
    have g := coulomb_variable_lower_localization graf D.matrix (H.representable hD.regular) hl tp scale
      (ae_of_all _ fun u => (centers (O.frame u)).2.1.div_const _) (by
        simp_rw [integral_div]
        exact fr.div_const _)
    rw [show f t = _ from fixed_frame_energy O η .lower (inv_pos.mpr he) ht D]
    simp only [err,tileDilation_of_mem ht,lowerTilingError,tileSideLength]
    change (1-C*t/(t*ε⁻¹))*_ - C/(t*ε⁻¹)*((1+t⁻¹)*(∫ x, D.charge x)+t^3*(∫ x, D.charge x^2)) ≤ _ at g
    convert g using 1
    field_simp [tp.ne',he.ne']
  let M := ∫ x, D.charge x
  let Q := ∫ x, D.charge x^2
  have hM : 0 ≤ M := integral_nonneg D.charge_nonneg
  have hQ : 0 ≤ Q := integral_nonneg fun x => sq_nonneg _
  have ei : Integrable err tileDilationLaw := by
    apply (integrable_const (C*ε*(6*M+4*Q))).mono' (by
      dsimp [err,lowerTilingError]; fun_prop)
    filter_upwards with t
    have tp := tileDilation_pos t
    have hr : (tileDilation t)⁻¹ ≤ 2 := (inv_le_comm₀ tp (by norm_num)).mpr (by
      simpa using (tileDilation_mem t).1)
    have sq := pow_le_pow_left₀ (inv_nonneg.mpr tp.le) hr 2
    have ts := pow_le_pow_left₀ tp.le (show tileDilation t ≤ 2 by linarith [(tileDilation_mem t).2]) 2
    change ‖C*ε*((_ + _)*M+_*Q)‖ ≤ _
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr <;> nlinarith
  have av := integral_mono_ae ((ints.2.2.1.const_mul (1-C*ε)).sub ei) (integrable_const (energy D.matrix)) fixed
  change (∫ t, (1-C*ε)*f t-err t ∂tileDilationLaw) ≤ _ at av
  rw [integral_sub (ints.2.2.1.const_mul _) ei,integral_const_mul,integral_const,probReal_univ,one_smul] at av
  rw [ints.2.2.2,← integral_tileDilationLaw]
  exact av

end TSGA.ManyBody
