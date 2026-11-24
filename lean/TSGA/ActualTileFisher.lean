import TSGA.ActualTileCutoffs
import TSGA.IslandSingleFisher
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Weak gradients and Fisher costs of the centered tetrahedral windows -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Set Metric Filter
open scoped ENNReal NNReal Topology

private theorem gradient_coord (f : Position → ℝ) (x : Position) (j : Fin 3) :
    gradient f x j = fderiv ℝ f x (PiLp.single 2 j 1) := by
  simpa only [EuclideanSpace.inner_single_right,one_mul,conj_trivial] using
    (inner_gradient_left (f := f) (x := x) (y := EuclideanSpace.single j (1:ℝ)))

private theorem weak_lip_gradient {f : Position → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (j : Fin 3) :
    WeakPartialOn univ j f (fun x => gradient f x j) := by
  let v : Position := PiLp.single 2 j 1
  have eq : (fun x => lineDeriv ℝ f x v) =ᵐ[volume] (fun x => gradient f x j) := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    exact hx.lineDeriv_eq_fderiv.trans (gradient_coord f x j).symm
  refine ⟨locallyIntegrableOn_univ.mpr hf.continuous.locallyIntegrable,
    locallyIntegrableOn_univ.mpr ((hf.locallyIntegrable_lineDeriv v).congr eq),?_⟩
  intro ψ hψ hc _
  obtain ⟨K,hK⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have h := hf.integral_lineDeriv_mul_eq (μ := volume) hK hc v
  simp_rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv] at h
  simp only [map_neg,neg_mul,integral_neg] at h
  simp only [Measure.restrict_univ,smul_eq_mul]
  rw [show (∫ x, ψ x * gradient f x j) = ∫ x, lineDeriv ℝ f x v * ψ x from
    integral_congr_ae (eq.mono fun x hx => by dsimp at hx ⊢; rw [hx,mul_comm])]
  simpa only [neg_neg] using congrArg Neg.neg h.symm

private theorem weak_unique {f g g' : Position → ℝ} {j : Fin 3} (a : WeakPartialOn univ j f g)
    (b : WeakPartialOn univ j f g') : g =ᵐ[volume] g' := by
  apply ae_eq_of_integral_contDiff_smul_eq (locallyIntegrableOn_univ.mp a.2.1)
    (locallyIntegrableOn_univ.mp b.2.1)
  intro ψ hψ hc
  simpa only [Measure.restrict_univ,neg_inj] using
    (a.2.2 ψ hψ hc (subset_univ _)).symm.trans (b.2.2 ψ hψ hc (subset_univ _))

private def tileFrame (O : TileOrientationLaw) (u : O.Frames) : Position ≃ₗᵢ[ℝ] Position :=
  (LinearIsometryEquiv.neg ℝ).trans (O.frame u)

private def tileRoot (η : Mollifier) (s : CutoffSide) (ℓ : ℝ) (x : Position) :=
  √(smoothedIndicator (tetrahedron (tileSideLength s ℓ)) η 1 x)

def actualTileGradient (O : TileOrientationLaw) (η : Mollifier) (s : CutoffSide) (ℓ : ℝ)
    (p : ℝ × O.Frames) := gradient (fun z => √(actualTileShape O η s ℓ p z))

private theorem actualTileRoot_fderiv (O : TileOrientationLaw) (η : Mollifier) (s : CutoffSide)
    (ℓ : ℝ) (p : ℝ × O.Frames) (z : Position) :
    fderiv ℝ (fun z => √(actualTileShape O η s ℓ p z)) z =
    ((tileDilation p.1)⁻¹ • fderiv ℝ (tileRoot η s ℓ) ((tileDilation p.1)⁻¹ • tileFrame O p.2 z)).comp
      (tileFrame O p.2 : Position →L[ℝ] Position) := by
  simp_rw [actualTileShape_pull]
  let R := (tileFrame O p.2).toContinuousLinearEquiv
  let a := (tileDilation p.1)⁻¹
  change fderiv ℝ ((fun x => tileRoot η s ℓ (a • x)) ∘ R) z = _
  rw [R.comp_right_fderiv,fderiv_comp_smul]
  rfl

private theorem actualTileGradient_norm (O : TileOrientationLaw) (η : Mollifier) (s : CutoffSide)
    (ℓ : ℝ) (p : ℝ × O.Frames) (z : Position) :
    ‖actualTileGradient O η s ℓ p z‖ = (tileDilation p.1)⁻¹ *
    ‖gradient (tileRoot η s ℓ) ((tileDilation p.1)⁻¹ • tileFrame O p.2 z)‖ := by
  simp only [actualTileGradient,gradient,LinearIsometryEquiv.norm_map,actualTileRoot_fderiv,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (tileDilation_pos p.1)).le]

theorem measurable_actualTileFisher (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (s : CutoffSide) (ℓ : ℝ) :
    Measurable (fun p : (ℝ × O.Frames) × Position => ‖actualTileGradient O η s ℓ p.1 p.2‖ ^ 2) := by
  simp_rw [actualTileGradient_norm]
  have ha := (measurable_tileDilation.comp (measurable_fst.comp measurable_fst : Measurable (fun p : (ℝ × O.Frames) × Position => p.1.1))).inv
  have hr := frames.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd.neg :
    Measurable (fun p : (ℝ × O.Frames) × Position => (p.1.2,-p.2)))
  have hg : Measurable (fun z => ‖gradient (tileRoot η s ℓ) z‖) := by
    simp only [gradient,LinearIsometryEquiv.norm_map]
    exact (measurable_fderiv ℝ _).norm
  exact (ha.mul (hg.comp (ha.smul hr))).pow_const 2

private theorem root_lip (O : TileOrientationLaw) (η : Mollifier) (sob : SobolevDifferenceQuotients)
    (s : CutoffSide) (ℓ : ℝ) :
    ∃ A ≥ 0, ∀ p : ℝ × O.Frames, LipschitzWith (Real.toNNReal A) (fun z => √(actualTileShape O η s ℓ p z)) := by
  obtain ⟨C,hC,h⟩ := smoothedRootLipschitz sob η
  refine ⟨2*C,by positivity,?_⟩
  intro p
  have v := (h _ (tetrahedron_open (tileDilation p.1 * tileSideLength s ℓ)).measurableSet (tileDilation_pos p.1)).comp (tileFrame O p.2).isometry.lipschitzWith
  refine v.weaken ?_
  simp only [mul_one]
  apply Real.toNNReal_le_toNNReal
  apply (div_le_iff₀ (tileDilation_pos p.1)).2
  nlinarith only [mul_le_mul_of_nonneg_left (tileDilation_mem p.1).1 hC]

theorem actualTileGradient_bound (O : TileOrientationLaw) (η : Mollifier) (sob : SobolevDifferenceQuotients)
    (s : CutoffSide) (ℓ : ℝ) : ∃ A ≥ 0, ∀ p z, ‖actualTileGradient O η s ℓ p z‖ ≤ A := by
  obtain ⟨A,hA,lip⟩ := root_lip O η sob s ℓ
  refine ⟨A,hA,fun p z => ?_⟩
  simpa only [actualTileGradient,gradient,LinearIsometryEquiv.norm_map, Real.coe_toNNReal _ hA] using
    (norm_fderiv_le_of_lipschitz ℝ (x₀ := z) (lip p))

theorem actualTileGradient_reflected (O : TileOrientationLaw) (η : Mollifier) (sob : SobolevDifferenceQuotients)
    (s : CutoffSide) (ℓ : ℝ) (p : ℝ × O.Frames) (c : Position) (j : Fin 3) :
    WeakPartialOn univ j (fun x => √(actualTileShape O η s ℓ p (c-x)))
      (fun x => -(actualTileGradient O η s ℓ p (c-x) j)) := by
  let f := fun z => √(actualTileShape O η s ℓ p z)
  obtain ⟨A,_,lip⟩ := root_lip O η sob s ℓ
  have hR : Isometry (fun x : Position => c-x) := Isometry.of_dist_eq fun x y => by simp [dist_eq_norm,sub_sub_sub_cancel_left,norm_sub_rev]
  have L := (lip p).comp hR.lipschitzWith
  have eq : (fun x => -(actualTileGradient O η s ℓ p (c-x) j)) = (fun x => gradient (fun y => f (c-y)) x j) := by
    funext x
    rw [gradient_coord,show actualTileGradient O η s ℓ p (c-x) j = fderiv ℝ f (c-x) (PiLp.single 2 j 1) from gradient_coord f _ _]
    let R := (LinearIsometryEquiv.neg ℝ (E := Position)).toContinuousLinearEquiv
    change -(fderiv ℝ f (c-x) _) = fderiv ℝ ((fun y => f (c+y)) ∘ R) x _
    rw [R.comp_right_fderiv,fderiv_comp_add_left]
    simp [R,sub_eq_add_neg]
  rw [eq]
  exact weak_lip_gradient L j

private theorem base_area (η : Mollifier) (s : CutoffSide) (sob : SobolevDifferenceQuotients) {C : ℝ}
    (hC : TileCutoffAreaBound η C) {ℓ : ℝ} (hr : 0 < tileSideLength s ℓ) :
    Integrable (fun x => ‖gradient (tileRoot η s ℓ) x‖^2) ∧
    (∫ x, ‖gradient (tileRoot η s ℓ) x‖^2) ≤ C*(tileSideLength s ℓ)^2 / 24 := by
  obtain ⟨A,_,lip⟩ := smoothedRootLipschitz sob η
  obtain ⟨g,w,m,b⟩ := hC _ 1 hr zero_lt_one
  have eq : gradient (tileRoot η s ℓ) =ᵐ[volume] g := by
    have E (j : Fin 3) := weak_unique (weak_lip_gradient (lip _ (tetrahedron_open _).measurableSet zero_lt_one) j) (w j)
    filter_upwards [ae_all_iff.2 E] with x hx
    ext j
    exact hx j
  have eq' : (fun x => ‖gradient (tileRoot η s ℓ) x‖^2) =ᵐ[volume] (fun x => ‖g x‖^2) := eq.fun_comp (fun v : Position => ‖v‖^2)
  refine ⟨(m.integrable_norm_pow (p := 2) (by decide)).congr eq'.symm,?_⟩
  rw [integral_congr_ae eq']
  apply b.trans_eq
  rw [tetrahedron_volume hr]
  field_simp [hr.ne']

private theorem actual_area_scale (O : TileOrientationLaw) (η : Mollifier) (s : CutoffSide)
    (ℓ : ℝ) (p : ℝ × O.Frames) :
    (∫ x, ‖actualTileGradient O η s ℓ p x‖^2) =
      tileDilation p.1 * ∫ x, ‖gradient (tileRoot η s ℓ) x‖^2 := by
  let t := tileDilation p.1
  let R := tileFrame O p.2
  let f := fun z => ‖gradient (tileRoot η s ℓ) z‖^2
  simp_rw [actualTileGradient_norm,mul_pow]
  rw [integral_const_mul]
  change t⁻¹ ^ 2 * (∫ x, f (t⁻¹ • R x)) = _
  rw [R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding (fun y => f (t⁻¹ • y))]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume f (tileDilation_pos p.1).le]
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
  change _ = t * ∫ x, f x
  dsimp only [t]
  field_simp [(tileDilation_pos p.1).ne']

private theorem integrable_kernel {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [IsFiniteMeasure μ]
    {K : ι → Position → ℝ} (hm : Measurable (Function.uncurry K)) (hn : ∀ i x, 0 ≤ K i x)
    (hi : ∀ i, Integrable (K i)) {B : ℝ} (hb : ∀ i, (∫ x, K i x) ≤ B) :
    Integrable (fun p : Position × ι => K p.2 p.1) (volume.prod μ) := by
  have h : Integrable (Function.uncurry K) (μ.prod volume) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨ae_of_all _ hi,?_⟩
    simp only [Function.uncurry_apply_pair,Real.norm_of_nonneg (hn _ _)]
    apply (integrable_const B).mono' hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    exact ae_of_all _ fun i => (Real.norm_of_nonneg (integral_nonneg (hn i))).le.trans (hb i)
  exact h.swap

/-- The concrete family with the surface constant of the reference cutoff. -/
def actualTetrahedralCutoffs (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (sob : SobolevDifferenceQuotients) {C : ℝ} (hC : 0 ≤ C)
    (area : TileCutoffAreaBound η C) (side : CutoffSide) {ε : ℝ} (he : 0 < ε) (he' : ε < 1) :
    TetrahedralCutoffs (actualTiles O frames η side he he') side ε (C/24) := by
  let ℓ := ε⁻¹
  let r := tileSideLength side ℓ
  have hr : 0 < r := tileSideLength_pos side he he'
  have hl : 0 < ℓ := inv_pos.mpr he
  let g := actualTileGradient O η side ℓ
  let f := tileRoot η side ℓ
  have hb := (base_area η side sob area hr).1
  have ba := (base_area η side sob area hr).2
  have harea (p : ℝ × O.Frames) : (∫ z, ‖g p z‖^2) ≤ (C/24)*(tileDilation p.1*ℓ)^2/tileDilation p.1 := by
    rw [show (∫ z, ‖g p z‖^2) = tileDilation p.1 * ∫ x, ‖gradient f x‖^2 from actual_area_scale ..]
    calc
      _ ≤ tileDilation p.1 * (C*r^2/24) := mul_le_mul_of_nonneg_left ba (tileDilation_pos _).le
      _ ≤ tileDilation p.1 * (C*ℓ^2/24) := by
        apply mul_le_mul_of_nonneg_left _ (tileDilation_pos _).le
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (tileSideLength_le side ℓ) 2) hC
      _ = _ := by field_simp [(tileDilation_pos p.1).ne']
  have wk (p : ℝ × O.Frames) (j : Fin 3) : WeakPartialOn univ j (fun x => √(actualTileShape O η side ℓ p x)) (fun x => g p x j) := by
    obtain ⟨A,_,lip⟩ := root_lip O η sob side ℓ
    exact weak_lip_gradient (lip p) j
  have weight_meas : Measurable (fun p : (ℝ × O.Frames) × Position => actualTileWeight ℓ p.1.1) := by
    unfold actualTileWeight
    fun_prop
  have weight_nn (p : ℝ × O.Frames) : 0 ≤ actualTileWeight ℓ p.1 := div_nonneg (by norm_num)
    (pow_nonneg (mul_nonneg (tileDilation_pos _).le hl.le) _)
  refine ⟨fun p => tileDilation p.1,measurable_tileDilation.comp measurable_fst,g,
    fun p => tileDilation_mem p.1,fun _ => rfl,actualTiles_shape_mass O frames η side he he',wk,harea,?_,?_⟩
  · let χ := actualTileShape O η side ℓ
    have m (p : ℝ × O.Frames) : (∫ z, χ p z) = side.mass ε * (tileDilation p.1 * ℓ)^3 / 24 :=
      actualTiles_shape_mass O frames η side he he' p
    have hm : 0 < side.mass ε := by cases side <;> dsimp [CutoffSide.mass] <;> positivity [sub_pos.mpr he']
    have hh (p : ℝ × O.Frames) : Integrable (χ p) := by
      apply Integrable.of_integral_ne_zero
      rw [m]
      exact (div_pos (mul_pos hm (pow_pos (mul_pos (tileDilation_pos _) hl) _)) (by norm_num)).ne'
    apply integrable_kernel (tileDilationLaw.prod O.law) (K := fun i z => actualTileWeight ℓ i.1 * χ i z)
      (weight_meas.mul (measurable_actualTileShape O frames η side ℓ))
      (fun p x => mul_nonneg (weight_nn _) (smoothedIndicator_bounds _ η (tileDilation_pos p.1) (O.frame p.2 (-x))).1)
      (fun p => (hh p).const_mul _) (B := side.mass ε)
    intro p
    rw [integral_const_mul,m]
    exact le_of_eq (by unfold actualTileWeight; field_simp [hl.ne',(tileDilation_pos p.1).ne'])
  · have hi (p : ℝ × O.Frames) : Integrable (fun x => ‖g p x‖^2) := by
      simp_rw [show ∀ x, ‖g p x‖^2 = (tileDilation p.1)⁻¹^2 * ‖gradient f ((tileDilation p.1)⁻¹ • tileFrame O p.2 x)‖^2 from
        fun x => by rw [show ‖g p x‖ = _ from actualTileGradient_norm O η side ℓ p x,mul_pow]]
      exact ((tileFrame O p.2).measurePreserving.integrable_comp_of_integrable
        (hb.comp_smul (inv_ne_zero (tileDilation_pos p.1).ne'))).const_mul _
    apply integrable_kernel (tileDilationLaw.prod O.law) (K := fun i z => actualTileWeight ℓ i.1 * ‖g i z‖^2)
      (by
        change Measurable fun p : (ℝ × O.Frames) × Position => actualTileWeight ℓ p.1.1 * ‖actualTileGradient O η side ℓ p.1 p.2‖^2
        exact weight_meas.mul (measurable_actualTileFisher O frames η side ℓ))
      (fun p x => mul_nonneg (weight_nn _) (sq_nonneg _)) (fun p => (hi p).const_mul _)
      (B := (192/ℓ^3) * ((3/2) * (C*r^2/24)))
    intro p
    rw [integral_const_mul,show (∫ z, ‖g p z‖^2) = tileDilation p.1 * ∫ x, ‖gradient f x‖^2 from actual_area_scale ..]
    exact mul_le_mul (actualTileWeight_bound hl _) (mul_le_mul (tileDilation_mem _).2 ba
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)) (mul_nonneg (tileDilation_pos _).le
        (integral_nonneg fun _ => sq_nonneg _)) (by positivity)

/-- Both families share one surface constant. Integrating the translated charge
against a spatial field gives its exact retained mass. The Fisher contribution
against a nonnegative spatial field is at most 96kε times its integral. -/
theorem actualTile_average_costs (O : TileOrientationLaw) (frames : TileFrameMeasurable O)
    (η : Mollifier) (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds) :
    ∃ k ≥ 0, ∀ (s : CutoffSide) {ε : ℝ} (he : 0 < ε) (he' : ε < 1),
      let T := actualTiles O frames η s he he'
      ∃ H : TetrahedralCutoffs T s ε k,
        H.gradient = actualTileGradient O η s ε⁻¹ ∧
        ∀ {u : Position → ℝ}, Integrable u →
          (∫ c, cutoffAverage T.cutoffProfile u c) = s.mass ε * ∫ x, u x ∧
          ((∀ᵐ x, 0 ≤ u x) → (∫ c, cutoffAverage H.kineticProfile u c) ≤ (96*k)*ε*∫ x, u x) := by
  obtain ⟨C,hC,area⟩ := tileCutoffAreaBound_of_sobolev sob quant η
  refine ⟨C/24,by positivity,fun s ε he he' => ?_⟩
  let := (actualTiles O frames η s he he').space
  let := (actualTiles O frames η s he he').probability
  let H := actualTetrahedralCutoffs O frames η sob hC area s he he'
  refine ⟨H,rfl,?_⟩
  intro u hu
  constructor
  · have hc : Integrable (actualTiles O frames η s he he').cutoffProfile := H.shape_product.integral_prod_left
    rw [integral_cutoffAverage hc hu,H.cutoff_mass he]
  · intro hnonneg
    have hf : Integrable H.kineticProfile := H.gradient_product.integral_prod_left
    rw [integral_cutoffAverage hf hu]
    exact mul_le_mul_of_nonneg_right (H.kinetic_mass he (by positivity)) (integral_nonneg_of_ae hnonneg)

end TSGA.ManyBody
