import TSGA.UpperSkeletonEstimate
import TSGA.RepresentableTileDensity
import TSGA.CoulombPeriodicKernel
import TSGA.TetrahedronConeMeasure

/-! # The variable-density upper localization inequality at every length and width -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Set Metric

/-- The centered tetrahedron energy. Dilation is restricted to [1/2,3/2],
where the clamped parameter agrees with the integration variable. -/
def upperTileAt (O : TileOrientationLaw) (η : Mollifier) (ℓ δ : ℝ) (D : Density)
    (p : ℝ × O.Frames) (z : Position) : ℝ :=
  let t := tileDilation p.1
  energy (fun x => (smoothedIndicator (tetrahedron (ℓ-δ)) η δ (t⁻¹ • O.frame p.2 (x-z)) : ℂ) • D.matrix x)

/-- The physical skeleton, with one contribution per translated cell. -/
def upperSkeletonAt (O : TileOrientationLaw) (η : Mollifier) (ℓ δ : ℝ) (D : Density)
    (p : ℝ × O.Frames) (τ : Position) : ℝ :=
  let t := tileDilation p.1
  energy (fun x => (latticeBlock ℓ δ η none (t⁻¹ • (O.frame p.2 x-τ)) : ℂ) • D.matrix x)

def upperTileMean (O : TileOrientationLaw) (η : Mollifier) (ℓ δ : ℝ) (D : Density) (t : ℝ) : ℝ :=
  ∫ u, ∫ z, actualTileWeight ℓ t * upperTileAt O η ℓ δ D (t,u) z ∂volume ∂O.law

def upperSkeletonMean (O : TileOrientationLaw) (η : Mollifier) (ℓ δ : ℝ) (D : Density) (t : ℝ) : ℝ :=
  ∫ u, ∫ τ, upperSkeletonAt O η ℓ δ D (t,u) τ ∂latticeShiftMeasure (tileDilation t*ℓ) ∂O.law

private theorem upper_tile_eq (O : TileOrientationLaw) (η : Mollifier) (ℓ δ : ℝ) (D : Density)
    (p : ℝ × O.Frames) (z : Position) :
    let t := tileDilation p.1
    upperTileAt O η ℓ δ D p z = energy (fun x =>
      (centeredWindow η (t*ℓ-t*δ) (t*δ) (O.frame p.2) z x : ℂ) • D.matrix x) := by
  intro t
  apply congrArg energy
  funext x
  have eq := smoothed_tetrahedron_dilate (tileDilation_pos p.1) (ℓ-δ) δ η (t⁻¹ • O.frame p.2 (x-z))
  rw [smul_inv_smul₀ (tileDilation_pos p.1).ne',mul_sub] at eq
  change (_ : ℂ) • D.matrix x = (smoothedIndicator _ _ _ _ : ℂ) • D.matrix x
  exact congrArg (fun a : ℝ => (a : ℂ) • D.matrix x) eq.symm

private theorem upper_skeleton_eq (O : TileOrientationLaw) (η : Mollifier) (ℓ δ : ℝ) (D : Density)
    (p : ℝ × O.Frames) (τ : Position) :
    let t := tileDilation p.1
    upperSkeletonAt O η ℓ δ D p τ = energy (latticeBlockDensity (t*ℓ) (t*δ) η (O.frame p.2) D.matrix τ none) := by
  intro t
  have scaled (z : Position) : latticeBlock (t*ℓ) (t*δ) η none (t • z) = latticeBlock ℓ δ η none z := by
    have h := lattice_fluctuation_dilate (t := t) (tileDilation_pos p.1) ℓ δ η z
    have tile : (∑' i, latticeWindow (t*ℓ) (t*δ) η i (t • z)) = ∑' i, latticeWindow ℓ δ η i z := tsum_congr (fun i : LatticeTile => latticeWindow_dilate (t := t) (tileDilation_pos p.1) ℓ δ η i z)
    rw [tile] at h
    exact add_left_cancel (sub_left_inj.mp h)
  apply congrArg energy
  funext x
  have h := scaled (t⁻¹ • (O.frame p.2 x-τ))
  rw [smul_inv_smul₀ (tileDilation_pos p.1).ne'] at h
  exact congrArg (fun a : ℝ => (a : ℂ) • D.matrix x) h.symm

private theorem weighted_scale_integrable {f : ℝ → ℝ} (m : Measurable f) {b : ℝ}
    (h : ∀ t, |f t| ≤ b) : IntegrableOn (fun t => f t*scaleWeight t) scaleInterval := by
  apply (scaleWeight_integrableOn.const_mul b).mono' (m.aestronglyMeasurable.mul scaleWeight_integrableOn.aestronglyMeasurable)
  filter_upwards with t
  change ‖f t*scaleWeight t‖ ≤ b*scaleWeight t
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0 ≤ scaleWeight t by unfold scaleWeight; positivity)]
  exact mul_le_mul_of_nonneg_right (h t) (by unfold scaleWeight; positivity)

private theorem tile_mean_data (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (W : WindowSobolevRules) (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    {η : Mollifier} {C : ℝ} (c₀ : 0 ≤ C) (area : TileCutoffAreaBound η C)
    {D : Density} {S : MatrixGradient} (reg : TileDensityDomain D S)
    {ℓ δ : ℝ} (hd : 0 < δ) (sc : δ ≤ ℓ/2) :
    (∀ t, Integrable (fun u => ∫ z, upperTileAt O η ℓ δ D (t,u) z) O.law) ∧
      IntegrableOn (fun t => upperTileMean O η ℓ δ D t*scaleWeight t) scaleInterval := by
  have hl : 0 < ℓ := by linarith
  let B := variableWindowCost H D S 1 ((2*ℓ)^3/24) (C*(2*ℓ)^2/(12*δ))
  let V := fun (p : ℝ × O.Frames) z => upperTileAt O η ℓ δ D p z
  have centers (p : ℝ × O.Frames) : Integrable (V p) ∧ (∫ z, |V p z|) ≤ B := by
    let t := tileDilation p.1
    have tp : 0 < t := tileDilation_pos _
    let a := t*ℓ-t*δ
    have ap : 0 < a := by dsimp only [a]; nlinarith only [mul_pos tp (show 0 < ℓ-δ by linarith)]
    have cap : a ≤ 2*ℓ := by dsimp only [a]; nlinarith only [mul_nonneg tp.le hd.le,
      mul_le_mul_of_nonneg_right (show t ≤ 2 by linarith [(tileDilation_mem p.1).2]) hl.le]
    have ans := H.variable_centers product W borel reg.regular reg.entries reg.tf reg.lo c₀ area ap (mul_pos tp hd) (O.frame p.2)
    simp_rw [V,upper_tile_eq]
    refine ⟨ans.2.1,ans.2.2.trans (variableWindowCost_mono H D S zero_le_one ?_ ?_)⟩
    · rw [tetrahedron_volume ap]; gcongr
    · rw [tetrahedron_volume ap,show C*(a^3/24)/(a*(t*δ))=C*a^2/(24*(t*δ)) by field_simp [ap.ne',tp.ne',hd.ne']]
      apply div_le_div₀ (mul_nonneg c₀ (sq_nonneg _)) (by gcongr) (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_right (tileDilation_mem p.1).1 hd.le]
  let w := fun (p : (ℝ × O.Frames) × Position) (x : Position) =>
    smoothedIndicator (tetrahedron (ℓ-δ)) η δ ((tileDilation p.1.1)⁻¹ • O.frame p.1.2 (x-p.2))
  have wm : Measurable (fun z : ((ℝ × O.Frames) × Position) × Position => w z.1 z.2) := by
    exact (measurable_smoothedTetrahedron η _ hd).comp
      ((measurable_tileDilation.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).inv.smul
        (frames.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.sub (measurable_snd.comp measurable_fst)))))
  have vm : Measurable (Function.uncurry V) := measurable_variableWindowEnergy borel reg.entries w wm
    (fun p x => let h := smoothedIndicator_bounds (tetrahedron (ℓ-δ)) η hd ((tileDilation p.1.1)⁻¹ • O.frame p.1.2 (x-p.2))
                (abs_of_nonneg h.1).trans_le h.2)
  have fm : Measurable (fun p : ℝ × O.Frames => ∫ z, V p z) := vm.stronglyMeasurable.integral_prod_right'.measurable
  have bound p : ‖∫ z, V p z‖ ≤ B := (norm_integral_le_integral_norm _).trans (centers p).2
  refine ⟨fun t => (integrable_const B).mono' ((fm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun u => bound (t,u)),?_⟩
  let g := fun t => ∫ u, ∫ z, V (t,u) z ∂volume ∂O.law
  have gm : Measurable g := fm.stronglyMeasurable.integral_prod_right'.measurable
  have eq (t : ℝ) : upperTileMean O η ℓ δ D t = actualTileWeight ℓ t*g t := by
    simp only [upperTileMean,g,V,integral_const_mul]
  simp_rw [eq]
  apply weighted_scale_integrable ((measurable_actualTileWeight ℓ).mul gm) (b := 192/ℓ^3*B)
  intro t
  change |actualTileWeight ℓ t*g t| ≤ _
  rw [abs_mul,abs_of_nonneg (actualTileWeight_nonneg hl.le _)]
  have bg : |g t| ≤ B := by simpa only [g,←Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := O.law) (ae_of_all _ fun u => bound (t,u))
  exact mul_le_mul (actualTileWeight_bound hl t) bg (abs_nonneg _) (by positivity)

private theorem skeleton_mean_data (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (borel : LevyLiebBorel) (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    {η : Mollifier} (sk : SkeletonFisherAverages η) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {D : Density} {S : MatrixGradient} (reg : TileDensityDomain D S) {ℓ δ : ℝ} (hd : 0 < δ) (sc : δ ≤ ℓ/2) :
    (∀ t, Integrable (fun u => ∫ τ, upperSkeletonAt O η ℓ δ D (t,u) τ ∂latticeShiftMeasure (tileDilation t*ℓ)) O.law) ∧
    IntegrableOn (fun t => upperSkeletonMean O η ℓ δ D t*scaleWeight t) scaleInterval ∧
      ∀ t, upperSkeletonMean O η ℓ δ D t ≤ variableWindowUpper H D S 2 (2*(sk.coefficient*(δ/ℓ))) (8*sk.coefficient/(ℓ*δ)) := by
  have hl : 0 < ℓ := by linarith
  let w := fun (p : (ℝ × O.Frames) × Position) (x : Position) =>
    latticeBlock ℓ δ η none ((tileDilation p.1.1)⁻¹ • (O.frame p.1.2 x-p.2))
  have wm : Measurable (fun z : ((ℝ × O.Frames) × Position) × Position => w z.1 z.2) :=
    (latticeBlock_measurable ℓ hd η none).comp
      ((measurable_tileDilation.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).inv.smul
        ((frames.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)).sub (measurable_snd.comp measurable_fst)))
  have en : Measurable (Function.uncurry (upperSkeletonAt O η ℓ δ D)) :=
    measurable_variableWindowEnergy borel reg.entries w wm (fun p x =>
      let h := latticeBlock_bounds hd sc hs none ((tileDilation p.1.1)⁻¹ • (O.frame p.1.2 x-p.2))
      (abs_of_nonneg h.1).trans_le h.2)
  let v := fun p : ℝ × O.Frames => ∫ τ, upperSkeletonAt O η ℓ δ D p τ ∂latticeShiftMeasure (tileDilation p.1*ℓ)
  have vm : Measurable v := measurable_shift_average ((measurable_tileDilation.comp measurable_fst).mul_const ℓ) en
  let g := sk.coefficient
  let m := 2*(g*(δ/ℓ))
  let n := 8*g/(ℓ*δ)
  let B := variableWindowCost H D S 2 m n
  let P := variableWindowUpper H D S 2 m n
  have bounds (p : ℝ × O.Frames) : |v p| ≤ B ∧ v p ≤ P := by
    let t := tileDilation p.1
    have tp : 0 < t := tileDilation_pos _
    have td : 0 < t*δ := mul_pos tp hd
    have scale : t*δ ≤ t*ℓ/2 := by nlinarith only [mul_le_mul_of_nonneg_left sc tp.le]
    have scaler : 2*(g*((t*δ)/(t*ℓ))) = m := by dsimp only [m]; field_simp
    have deriv : 2*(g/(t*ℓ*(t*δ))) ≤ n := by
      change 2*(g/(t*ℓ*(t*δ))) ≤ 8*g/(ℓ*δ)
      have t2 : 1 ≤ 4*t^2 := by nlinarith only [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) (tileDilation_mem p.1).1]
      rw [show 2*(g/(t*ℓ*(t*δ)))=(2*g/t^2)/(ℓ*δ) by ring]
      apply div_le_div_of_nonneg_right _ (mul_pos hl hd).le
      rw [div_le_iff₀ (sq_pos_of_pos tp)]
      nlinarith only [mul_le_mul_of_nonneg_left t2 sk.nonneg]
    dsimp only [v]
    simp_rw [upper_skeleton_eq]
    refine ⟨(abs_integral_le_integral_abs).trans ((H.variable_skeleton product borel reg.regular reg.entries reg.tf reg.lo sk hs td scale (O.frame p.2)).2.2.trans
      (variableWindowCost_mono H D S (by norm_num) scaler.le deriv)),?_⟩
    apply (H.variable_skeleton_upper product borel reg.regular reg.entries reg.tf reg.lo sk hs td scale (O.frame p.2)).trans
    rw [show 2*(sk.coefficient*((t*δ)/(t*ℓ))) = m from scaler]
    change H.interiorConstant*(_+2*((2*(g/(t*ℓ*(t*δ))))*(∫ x, D.charge x))) ≤
      H.interiorConstant*(_+2*(n*(∫ x, D.charge x)))
    exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right deriv (integral_nonneg D.charge_nonneg)) (by norm_num : (0:ℝ) ≤ 2)) _) H.interiorConstant_nonneg
  have fi (t : ℝ) : Integrable (fun u => v (t,u)) O.law := (integrable_const B).mono'
    ((vm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) (ae_of_all _ fun u => (bounds (t,u)).1)
  refine ⟨fi,weighted_scale_integrable (b := B) (f := fun t => ∫ u, v (t,u) ∂O.law) vm.stronglyMeasurable.integral_prod_right'.measurable ?_,?_⟩
  · intro t
    have hb : ∀ᵐ u ∂O.law, ‖v (t,u)‖ ≤ B := ae_of_all _ fun u => (bounds (t,u)).1
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb
  · intro t
    change (∫ u, v (t,u) ∂O.law) ≤ P
    exact (integral_mono (fi t) (integrable_const P) (fun u => (bounds (t,u)).2)).trans_eq (by simp)

private theorem scale_average_le_constant {f : ℝ → ℝ} {α c : ℝ} (ha : 0 < α) (hu : α < 1/2)
    (hi : IntegrableOn (fun t => f t*scaleWeight t) scaleInterval) (h : ∀ t, f t ≤ c) :
    scaleAverageAt α f ≤ c := by
  let I := Icc (1-α) (1+α)
  have sub : I ⊆ scaleInterval := fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hw := scaleWeight_integrableOn.mono_set sub
  have hpos : 0 < ∫ t in I, scaleWeight t := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae _ hw).2
    · have inc : I ⊆ Function.support scaleWeight := fun t ht => inv_ne_zero (pow_ne_zero _ (by linarith [(sub ht).1]))
      rw [inter_eq_right.mpr inc,Real.volume_Icc]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    · exact ae_of_all _ fun t => inv_nonneg.mpr (by positivity : 0 ≤ t^4)
  apply (div_le_iff₀ hpos).2
  rw [←integral_const_mul]
  exact integral_mono_ae (hi.mono_set sub) (hw.const_mul c)
    (ae_of_all _ fun t => mul_le_mul_of_nonneg_right (h t) (by unfold scaleWeight; positivity))

/-- Theorem 4.10. The tetrahedra are integrated over their centers and the
skeleton over one translated cell. The width δ, length ℓ and half-width α
of the dilation window are independent. -/
theorem coulomb_variable_upper_all_scales (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (W : WindowSobolevRules) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (tensor : DisjointFockTensorization) (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (haar : CubeFrameInvariant O)
    {η : Mollifier} {C : ℝ} (c₀ : 0 ≤ C) (area : TileCutoffAreaBound η C)
    (sk : SkeletonFisherAverages η) (support : tsupport η.kernel ⊆ closedBall 0 (1/100))
    {A B : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B)
    {D : Density} {S : MatrixGradient} (reg : TileDensityDomain D S)
    {ℓ δ α : ℝ} (hd : 0 < δ) (sc : δ ≤ ℓ/2) (hp : 0 < α) (hu : α < 1/2) :
    energy D.matrix ≤ scaleAverageAt α (fun t => upperTileMean O η ℓ δ D t+upperSkeletonMean O η ℓ δ D t) +
      (54*A*B*(δ^3/ℓ))*(∫ x, D.charge x^2)*Real.log α⁻¹ ∧
    scaleAverageAt α (upperSkeletonMean O η ℓ δ D) ≤
      variableWindowUpper H D S 2 (2*(sk.coefficient*(δ/ℓ))) (8*sk.coefficient/(ℓ*δ)) := by
  have hl : 0 < ℓ := by linarith
  let borel := levyLiebBorel_of_lowerSemicontinuous lsc
  have hs := (subset_tsupport _).trans support
  obtain ⟨ti,ta⟩ := tile_mean_data H product W borel O frames c₀ area reg hd sc
  obtain ⟨si,sa,signed⟩ := skeleton_mean_data H product borel O frames sk hs reg hd sc
  have vi := lattice_variance_integrable_ae O frames hs hd sc reg.regular.charge.aemeasurable reg.direct
  refine ⟨?_,scale_average_le_constant hp hu sa signed⟩
  have ai : IntegrableOn (fun t => (upperTileMean O η ℓ δ D t+upperSkeletonMean O η ℓ δ D t)*scaleWeight t) scaleInterval := by
    simpa only [add_mul,Pi.add_def] using ta.add sa
  have bound := scale_average_bound (C := 0) hp hu ai vi.2 (e := energy D.matrix) (by
    intro t ht
    have tp : 0 < t := by linarith [ht.1]
    have td : 0 < t*δ := mul_pos tp hd
    have scl : t*δ ≤ t*ℓ/2 := by nlinarith only [mul_le_mul_of_nonneg_left sc tp.le]
    have side : 0 < t*ℓ-t*δ := by nlinarith only [mul_pos tp (show 0 < ℓ-δ by linarith)]
    have ctr := fun R => H.variable_centers product W borel reg.regular reg.entries reg.tf reg.lo c₀ area side td R
    have skel := fun R => H.variable_skeleton product borel reg.regular reg.entries reg.tf reg.lo sk hs td scl R
    have framesT := ti t
    simp_rw [upper_tile_eq,tileDilation_of_mem ht] at framesT
    have framesS := si t
    simp_rw [upper_skeleton_eq,tileDilation_of_mem ht] at framesS
    have h := coulomb_variable_upper_localization tensor lsc O haar hs td scl D.matrix reg.entries reg.direct
      (fun R => (ctr R).2.1) framesT
      (ae_of_all _ fun u => by
        filter_upwards [(skel (O.frame u)).1,feasible_lattice_cells (O.frame u) (fun R => (ctr R).1)] with τ hsk hc
        rintro (_|i)
        · exact hsk
        · exact hc i)
      (ae_of_all _ fun u => (skel (O.frame u)).2.1) framesS (vi.1 t ht)
    simpa only [upperTileMean,upperSkeletonMean,upper_tile_eq,upper_skeleton_eq,actualTileWeight_volume hl,
      tileDilation_of_mem ht,div_eq_inv_mul,add_zero,latticeVariance,Density.charge] using h)
  rw [add_zero] at bound
  exact bound.trans (add_le_add_right (coulomb_variable_cubic_variance O tetrahedronCone η.periodicKernelCalculus support
    ha hb transport fourier D.charge reg.regular.charge reg.square hd sc hp hu) _)

/-- The same coefficient works for every representable density and every
admissible choice of the three localization parameters. -/
theorem coulomb_upper_localization (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    (W : WindowSobolevRules) (lsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (tensor : DisjointFockTensorization) (O : TileOrientationLaw) (frames : TileFrameMeasurable O) (haar : CubeFrameInvariant O)
    {η : Mollifier} {C : ℝ} (c₀ : 0 ≤ C) (area : TileCutoffAreaBound η C)
    (sk : SkeletonFisherAverages η) (support : tsupport η.kernel ⊆ closedBall 0 (1/100))
    {A B : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (transport : PeriodicTransportInequality A) (fourier : CoulombFourierAveraging O B)
    (embed : MatrixSobolevEmbeddingFour) :
    ∃ J > 0, ∀ {D : Density} {S : MatrixGradient}, SqrtRegular D S →
    ∀ {ℓ δ α : ℝ}, 0 < δ → δ ≤ ℓ/2 → 0 < α → α < 1/2 →
    energy D.matrix ≤ scaleAverageAt α (fun t => upperTileMean O η ℓ δ D t+upperSkeletonMean O η ℓ δ D t) +
      (J*(δ^3/ℓ))*(∫ x, D.charge x^2)*Real.log α⁻¹ ∧
    scaleAverageAt α (upperSkeletonMean O η ℓ δ D) ≤
      J*(δ/ℓ)*(chargeMoment D (5/3)+sqrtKinetic S)+J/(ℓ*δ)*(∫ x, D.charge x) := by
  let g := sk.coefficient
  let I := H.interiorConstant
  let J := 1 + 54*A*B + 16*g*I
  have g₀ : 0 ≤ g := sk.nonneg
  have i₀ : 0 ≤ I := H.interiorConstant_nonneg
  have v₀ : 0 ≤ 54*A*B := by positivity
  have w₀ : 0 ≤ 16*g*I := by positivity
  refine ⟨J,by dsimp only [J]; linarith only [w₀,v₀],?_⟩
  intro D S regular ℓ δ α hd sc hp hu
  have hl : 0 < ℓ := by linarith
  suffices source : TileDensityDomain D S by
    obtain ⟨main,skel⟩ := coulomb_variable_upper_all_scales H product W lsc tensor O frames haar c₀ area sk support
      ha hb transport fourier source hd sc hp hu
    have jw : 16*g*I ≤ J := by dsimp only [J]; linarith only [v₀]
    have jv : 54*A*B ≤ J := by dsimp only [J]; linarith only [w₀]
    have jtf : I*2^(2/3:ℝ)*(2*g) ≤ J := by
      have two : (2:ℝ)^(2/3:ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
      have gi := mul_nonneg g₀ i₀
      nlinarith only [mul_le_mul_of_nonneg_right two gi,gi,jw]
    have jk : 4*g*I ≤ J := by nlinarith only [mul_nonneg g₀ i₀,jw]
    have ht : 0 ≤ chargeMoment D (5/3) := integral_nonneg fun x => Real.rpow_nonneg (D.charge_nonneg x) _
    have hk : 0 ≤ sqrtKinetic S := integral_nonneg fun _ => sq_nonneg _
    have hm : 0 ≤ ∫ x, D.charge x := integral_nonneg D.charge_nonneg
    have ratio := div_nonneg hd.le hl.le
    refine ⟨main.trans (add_le_add_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right jv (div_nonneg (pow_nonneg hd.le _) hl.le))
        (integral_nonneg fun x => sq_nonneg _)) (Real.log_nonneg ((one_le_inv₀ hp).2 (by linarith)))) _),skel.trans ?_⟩
    change I*(2^(2/3:ℝ)*(2*(g*(δ/ℓ))*chargeMoment D (5/3))+2*(2*(g*(δ/ℓ))*sqrtKinetic S)+
      2*(8*g/(ℓ*δ)*(∫ x, D.charge x))) ≤ _
    simp only [div_eq_mul_inv,mul_inv_rev] at *
    nlinarith only [mul_le_mul_of_nonneg_right jtf (mul_nonneg ratio ht),
      mul_le_mul_of_nonneg_right jk (mul_nonneg ratio hk),mul_le_mul_of_nonneg_right jw (mul_nonneg hm (mul_nonneg (inv_nonneg.mpr hl.le) (inv_nonneg.mpr hd.le)))]
  exact tileDensityDomain_of_representable embed regular

end TSGA.ManyBody
