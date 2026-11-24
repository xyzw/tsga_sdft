import TSGA.TilingBounds
import TSGA.CoulombLatticeShell
import TSGA.CoulombDilationMeasure
import TSGA.CoulombLowerTiling

/-! # The centered upper and lower tetrahedral cutoff families

After unfolding the 24 cube labels and averaging their frames, a tile is
parametrized by its dilation and orientation. Its spatial argument is reflected
because `AveragedTiles` uses the translation coordinate c − x.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization Set Metric
open scoped ENNReal NNReal

private def dilationWeight (t : ℝ) : ℝ≥0 := Real.toNNReal (scaleWeight t)

def tileDilationLaw : Measure ℝ :=
  ENNReal.ofReal ((∫ t in scaleInterval, scaleWeight t)⁻¹) •
    (volume.restrict scaleInterval).withDensity (fun t => (dilationWeight t : ℝ≥0∞))

theorem integral_tileDilationLaw (f : ℝ → ℝ) :
    (∫ t, f t ∂tileDilationLaw) = scaleAverage f := by
  have hm : Measurable dilationWeight := by unfold dilationWeight scaleWeight; fun_prop
  rw [tileDilationLaw, integral_smul_measure, integral_withDensity_eq_integral_smul hm f]
  have h0 (t : ℝ) : 0 ≤ scaleWeight t := by unfold scaleWeight; positivity
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr scaleWeight_integral_pos.le), dilationWeight,
    NNReal.smul_def,Real.coe_toNNReal _ (h0 _),
    smul_eq_mul, scaleAverage, div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun t => mul_comm _ _

instance : IsProbabilityMeasure tileDilationLaw := by
  constructor
  have h := integral_tileDilationLaw (fun _ => 1)
  simp [scaleAverage,scaleWeight_integral_pos.ne'] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

theorem tileDilationLaw_mem : ∀ᵐ t ∂tileDilationLaw, t ∈ scaleInterval := by
  exact Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)) _

def tileDilation (t : ℝ) : ℝ := max (1/2) (min t (3/2))

theorem tileDilation_mem (t : ℝ) : tileDilation t ∈ scaleInterval := by
  exact ⟨le_max_left .., max_le (by norm_num) (min_le_right ..)⟩
theorem tileDilation_of_mem {t : ℝ} (ht : t ∈ scaleInterval) : tileDilation t = t := by
  unfold tileDilation
  rw [min_eq_left ht.2,max_eq_right ht.1]

theorem tileDilation_pos (t : ℝ) : 0 < tileDilation t := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (tileDilation_mem t).1

@[fun_prop] theorem measurable_tileDilation : Measurable tileDilation := by unfold tileDilation; fun_prop

def tileSideLength : CutoffSide → ℝ → ℝ
  | .upper, ℓ => ℓ-1
  | .lower, ℓ => ℓ

theorem tileSideLength_pos (s : CutoffSide) {ε : ℝ} (he : 0 < ε) (he' : ε < 1) :
    0 < tileSideLength s ε⁻¹ := by
  cases s <;> simp only [tileSideLength]
  · exact sub_pos.mpr ((one_lt_inv₀ he).mpr he')
  · positivity

theorem tileSideLength_le (s : CutoffSide) (ℓ : ℝ) : tileSideLength s ℓ ≤ ℓ := by
  cases s <;> simp [tileSideLength]

variable (O : TileOrientationLaw)
abbrev TileFrameMeasurable := Measurable (fun p : O.Frames × Position => O.frame p.1 p.2)

def actualTileShape (η : Mollifier) (side : CutoffSide) (ℓ : ℝ) (p : ℝ × O.Frames) (z : Position) :=
  smoothedIndicator (tetrahedron (tileDilation p.1 * tileSideLength side ℓ)) η (tileDilation p.1) (O.frame p.2 (-z))

def actualTileWeight (ℓ t : ℝ) := 24 / (tileDilation t * ℓ)^3

theorem actualTileShape_pull (η : Mollifier) (side : CutoffSide) (ℓ : ℝ) (p : ℝ × O.Frames) (z : Position) :
    actualTileShape O η side ℓ p z = smoothedIndicator (tetrahedron (tileSideLength side ℓ)) η 1
      ((tileDilation p.1)⁻¹ • O.frame p.2 (-z)) := by
  simpa only [actualTileShape,mul_one,smul_inv_smul₀ (tileDilation_pos p.1).ne'] using
    smoothed_tetrahedron_dilate (tileDilation_pos p.1) (tileSideLength side ℓ) 1 η ((tileDilation p.1)⁻¹ • O.frame p.2 (-z))

theorem measurable_actualTileShape (frames : TileFrameMeasurable O) (η : Mollifier) (s : CutoffSide) (ℓ : ℝ) :
    Measurable (Function.uncurry (actualTileShape O η s ℓ)) := by
  change Measurable fun p : (ℝ × O.Frames) × Position => actualTileShape O η s ℓ p.1 p.2
  simp_rw [actualTileShape_pull]
  exact (measurable_smoothedTetrahedron η _ zero_lt_one).comp
    (((measurable_tileDilation.comp (measurable_fst.comp measurable_fst)).inv).smul
      (frames.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd.neg)))

theorem actualTileWeight_bound {ℓ : ℝ} (hl : 0 < ℓ) (t : ℝ) : actualTileWeight ℓ t ≤ 192/ℓ^3 := by
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) (tileDilation_mem t).1 3
  dsimp [actualTileWeight]
  rw [div_le_div_iff₀ (pow_pos (mul_pos (tileDilation_pos t) hl) _) (pow_pos hl _),mul_pow]
  nlinarith only [mul_le_mul_of_nonneg_right h (pow_nonneg hl.le 3)]

theorem actualTileWeight_nonneg {ℓ : ℝ} (hl : 0 ≤ ℓ) (t : ℝ) : 0 ≤ actualTileWeight ℓ t :=
  div_nonneg (by norm_num) (pow_nonneg (mul_nonneg (tileDilation_pos _).le hl) _)

@[fun_prop] theorem measurable_actualTileWeight (ℓ : ℝ) : Measurable (actualTileWeight ℓ) :=
  measurable_const.div ((measurable_tileDilation.mul measurable_const).pow_const 3)

private theorem actual_profile_integrable (frames : TileFrameMeasurable O) (η : Mollifier)
    (side : CutoffSide) {ℓ : ℝ} (hl : 0 < ℓ) (z : Position) :
    Integrable (fun i : ℝ × O.Frames => actualTileWeight ℓ i.1 * actualTileShape O η side ℓ i z)
      (tileDilationLaw.prod O.law) := by
  have hm := ((measurable_actualTileWeight ℓ).comp measurable_fst).mul
    ((measurable_actualTileShape O frames η side ℓ).comp (measurable_id.prodMk (measurable_const (a := z))))
  refine (integrable_const (192/ℓ^3)).mono' hm.aestronglyMeasurable (ae_of_all _ fun i => ?_)
  have hr : actualTileShape O η side ℓ i z ∈ Icc 0 1 := smoothedIndicator_bounds _ _ (tileDilation_pos i.1) _
  have hw := actualTileWeight_nonneg hl.le i.1
  rw [Real.norm_of_nonneg (mul_nonneg hw hr.1)]
  exact (mul_le_of_le_one_right hw hr.2).trans (actualTileWeight_bound hl _)

def actualTiles (frames : TileFrameMeasurable O) (η : Mollifier) (side : CutoffSide) {ε : ℝ}
    (he : 0 < ε) (_he' : ε < 1) : AveragedTiles where
  Parameter := ℝ × O.Frames
  measure := tileDilationLaw.prod O.law
  probability := inferInstance
  weight p := actualTileWeight ε⁻¹ p.1
  weight_nonneg p := actualTileWeight_nonneg (inv_pos.mpr he).le p.1
  shape := actualTileShape O η side ε⁻¹
  shape_mem p z := smoothedIndicator_bounds _ η (tileDilation_pos p.1) (O.frame p.2 (-z))
  profile_integrable := actual_profile_integrable O frames η side (inv_pos.mpr he)

private theorem tetrahedron_norm {r : ℝ} (hr : 0 < r) {x : Position} (hx : x ∈ tetrahedron r) :
    ‖x‖ ≤ r := by
  obtain ⟨h2,h1,h0⟩ := hx
  have ha := abs_nonneg (x 2)
  have hb := neg_abs_le (x 2)
  have hc := le_abs_self (x 2)
  have hs (i : Fin 3) : (x i)^2 ≤ (r/2)^2 := by
    apply sq_le_sq' <;> fin_cases i <;> dsimp <;> linarith
  apply (sq_le_sq₀ (norm_nonneg _) hr.le).mp
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x]
  simp only [Fin.sum_univ_three,Real.norm_eq_abs,sq_abs]
  nlinarith only [hs 0,hs 1,hs 2,sq_nonneg r]

/-- The comparison ball of radius 3ℓ contains every translated physical window. -/
theorem actualTiles_supported (frames : TileFrameMeasurable O) (η : Mollifier)
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (side : CutoffSide)
    {ε : ℝ} (he : 0 < ε) (he' : ε < 1) (c : Position)
    (i : (actualTiles O frames η side he he').Parameter) (x : Position)
    (hx : x ∉ closedBall c (3*ε⁻¹)) :
    (actualTiles O frames η side he he').shape i (c-x) = 0 := by
  by_contra hn
  let t := tileDilation i.1
  let r := tileSideLength side ε⁻¹
  let y := O.frame i.2 (-(c-x))
  obtain ⟨z,hz,hd⟩ := smoothed_support_witness hs (tileDilation_pos i.1)
    (show smoothedIndicator (tetrahedron (t*r)) η t y ≠ 0 from hn)
  have hnz := tetrahedron_norm (mul_pos (tileDilation_pos i.1) (tileSideLength_pos side he he')) hz
  have ht : t ≤ 3/2 := (tileDilation_mem i.1).2
  have hl := (one_lt_inv₀ he).mpr he'
  have hl' := mul_le_mul_of_nonneg_right ht (inv_pos.mpr he).le
  have htr := mul_le_mul_of_nonneg_left (tileSideLength_le side ε⁻¹) (tileDilation_pos i.1).le
  have htri := dist_triangle y z 0
  simp only [dist_zero_right] at htri
  apply hx
  rw [mem_closedBall,dist_eq_norm,← norm_sub_rev c x]
  have hy : ‖y‖ = ‖c-x‖ := by
    dsimp only [y]
    rw [LinearIsometryEquiv.norm_map,norm_neg]
  change t * r ≤ _ at htr
  linarith only [hnz,hd,htri,hy,htr,hl',hl,ht]

theorem actualTiles_shape_mass (frames : TileFrameMeasurable O) (η : Mollifier) (side : CutoffSide)
    {ε : ℝ} (he : 0 < ε) (he' : ε < 1) (p : (actualTiles O frames η side he he').Parameter) :
    (∫ z, (actualTiles O frames η side he he').shape p z) =
      side.mass ε * (tileDilation p.1 * ε⁻¹)^3 / 24 := by
  let R := (LinearIsometryEquiv.neg ℝ (E := Position)).trans (O.frame p.2)
  let f := smoothedIndicator (tetrahedron (tileDilation p.1 * tileSideLength side ε⁻¹)) η (tileDilation p.1)
  change (∫ z, f (R z)) = _
  rw [R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding f]
  dsimp only [f]
  rw [tile_cutoff_mass η (mul_pos (tileDilation_pos _) (tileSideLength_pos side he he')) (tileDilation_pos _),
    tetrahedron_volume (mul_pos (tileDilation_pos _) (tileSideLength_pos side he he'))]
  cases side <;> dsimp [tileSideLength,CutoffSide.mass] <;> field_simp [he.ne']

/-- Fubini at a fixed center for an arbitrary spatial field, with the cell weight included in k. -/
theorem tileKernel_convolution {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [IsFiniteMeasure μ]
    {k : ι → Position → ℝ} (hm : Measurable (Function.uncurry k)) {B : ℝ} (hb : ∀ i z, ‖k i z‖ ≤ B)
    {u : Position → ℝ} (hu : Integrable u) (c : Position) :
    Integrable (fun i => ∫ x, u x * k i (c-x)) μ ∧
    (∫ i, ∫ x, u x * k i (c-x) ∂volume ∂μ) = cutoffAverage (fun z => ∫ i, k i z ∂μ) u c := by
  let F := fun p : Position × ι => u p.1 * k p.2 (c-p.1)
  have hf : Integrable F (volume.prod μ) := by
    refine ((hu.norm.mul_const B).comp_fst μ).mono' (hu.1.comp_fst.mul
      ((hm.comp (measurable_snd.prodMk (measurable_const.sub measurable_fst))).aestronglyMeasurable)) ?_
    exact ae_of_all _ fun p => (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left (hb _ _) (norm_nonneg _))
  refine ⟨hf.integral_prod_right,?_⟩
  change (∫ i, ∫ x, F (x,i) ∂volume ∂μ) = ∫ x, u x * (∫ i, k i (c-x) ∂μ)
  rw [← integral_integral_swap hf]
  exact integral_congr_ae (ae_of_all _ fun x => integral_const_mul (u x) (fun i => k i (c-x)))

end TSGA.ManyBody
