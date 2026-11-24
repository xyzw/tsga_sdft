import TSGA.CoulombUpperTiling
import TSGA.CoulombDilationMeasure
import TSGA.IslandMasks
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # Single translated and rotated islands for Appendix C -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW Set Metric

/-- An explicit fixed core. Squaring the smooth bump makes its positive square
root smooth throughout the support boundary. -/
def islandCoreBump : ContDiffBump (0 : Position) := ⟨1/256,1/128,by norm_num,by norm_num⟩

def islandCore (r : ℝ) (x : Position) : ℝ := (islandCoreBump (r⁻¹ • x))^2

def islandCoreFraction : ℝ := 24 * ∫ x : Position, (islandCoreBump x)^2

theorem islandCore_range (r : ℝ) (x : Position) : islandCore r x ∈ Icc 0 1 :=
  ⟨sq_nonneg _,pow_le_one₀ islandCoreBump.nonneg islandCoreBump.le_one⟩

private theorem islandCoreBump_square_compact : HasCompactSupport (fun x => (islandCoreBump x)^2) := by
  simp only [sq]
  exact islandCoreBump.hasCompactSupport.mul_right

theorem islandCoreFraction_pos : 0 < islandCoreFraction := by
  have h := (islandCoreBump.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
    islandCoreBump_square_compact (fun _ => sq_nonneg _) (x := 0)
  apply mul_pos (by norm_num : (0:ℝ)<24)
  apply h
  simp [islandCoreBump.one_of_mem_closedBall (mem_closedBall_self islandCoreBump.rIn_pos.le)]

theorem islandCore_mass {r : ℝ} (hr : 0 < r) :
    Integrable (islandCore r) ∧ (∫ x, islandCore r x) = islandCoreFraction*(r^3/24) := by
  have hi : Integrable (fun x => (islandCoreBump x)^2) :=
    (islandCoreBump.continuous.pow 2).integrable_of_hasCompactSupport islandCoreBump_square_compact
  refine ⟨hi.comp_smul (inv_ne_zero hr.ne'),?_⟩
  change (∫ x, (fun y : Position => (islandCoreBump y)^2) (r⁻¹ • x)) = _
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun y : Position => (islandCoreBump y)^2) hr.le]
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,islandCoreFraction]
  ring

/-- The inner convolution reaches only points where the outer convolution
already equals one. The shift by δ suffices for a kernel of radius 1/100. -/
theorem island_layer_plateau {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {r δ : ℝ} (hd : 0 < δ) {x : Position}
    (hx : smoothedIndicator (tetrahedron (r-δ)) η δ x ≠ 0) :
    smoothedIndicator (tetrahedron r) η δ x = 1 := by
  obtain ⟨y,hy,hxy⟩ := smoothed_support_witness hs hd hx
  apply smoothed_eq_one hs hd
  intro z hz
  have hdist : dist y z < δ/16 := by
    linarith only [dist_triangle y x z,dist_comm y x,dist_comm x z,hxy,mem_closedBall.mp hz,hd]
  apply tetrahedron_mono (show (r-δ)+16*(δ/16) ≤ r by linarith)
  exact tetrahedron_enlarge hy hdist

theorem island_core_plateau {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {r δ : ℝ} (hd : 0 < δ) (hw : δ ≤ r/2) {x : Position} (hx : islandCore r x ≠ 0) :
    smoothedIndicator (tetrahedron (r-δ)) η δ x = 1 := by
  have hr : 0 < r := by linarith
  have hn : r⁻¹ • x ∈ Function.support islandCoreBump := fun h => hx (by simp [islandCore,h])
  rw [islandCoreBump.support_eq,mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at hn
  change r⁻¹ * ‖x‖ < 1/128 at hn
  have hn' : ‖x‖ < r/128 := by
    rw [← div_eq_inv_mul,div_lt_iff₀ hr] at hn; linarith
  apply smoothed_eq_one hs hd
  intro z hz
  have bound : ‖z‖ < (r-δ)/16 := by
    have tri := dist_triangle z x 0
    rw [dist_zero_right,dist_zero_right] at tri
    linarith only [tri,mem_closedBall.mp hz,hn',hd,hw]
  have coords (j : Fin 3) : |z j| < (r-δ)/16 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le z j).trans_lt bound
  have a := abs_lt.mp (coords 0)
  have b := abs_lt.mp (coords 1)
  exact ⟨by linarith [coords 2],by linarith,by linarith⟩

/-- Stationary rigid placements of individual profiles. For a normalized Haar
frame and Lebesgue-distributed center the pullback at every observation point
has intensity κ times Lebesgue measure. -/
structure StationaryIslandPlacements {Z : Type*} [MeasurableSpace Z] (intensity : Measure Z) (κ : ℝ) where
  chart : Z → Position → Position
  measurable : Measurable (Function.uncurry chart)
  isometry : ∀ z, Isometry (chart z)
  spatial : ∀ z, MeasurePreserving (chart z) volume volume
  stationary : ∀ x, MeasurePreserving (fun z => chart z x) intensity (ENNReal.ofReal κ • volume)

/-- Uniform centers and any independent probability distribution of frames
give stationary placements. Taking the normalized Haar law for rotations
gives the placement intensity of the smeared Graf–Schenker formula. -/
def StationaryIslandPlacements.ofFrames {F : Type*} [MeasurableSpace F] (ν : Measure F)
    [IsProbabilityMeasure ν] (R : F → Position ≃ₗᵢ[ℝ] Position)
    (hm : Measurable (fun p : F × Position => R p.1 p.2)) (κ : ℝ) :
    StationaryIslandPlacements (ENNReal.ofReal κ • ν.prod (volume : Measure Position)) κ := by
  let chart := fun (q : F × Position) (x : Position) => R q.1 (x-q.2)
  have hchart : Measurable (Function.uncurry chart) :=
    hm.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.sub (measurable_snd.comp measurable_fst)))
  refine ⟨chart,hchart,?_,?_,?_⟩
  · intro q
    apply (R q.1).isometry.comp
    intro x y
    simp only [edist_dist,dist_eq_norm,sub_sub_sub_cancel_right]
  · intro q
    exact (R q.1).measurePreserving.comp (measurePreserving_sub_right volume q.2)
  · intro x
    let : (volume : Measure Position).IsNegInvariant :=
      ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
    have hm' : Measurable (fun q => chart q x) := hchart.comp measurable_prodMk_right
    apply MeasurePreserving.smul_measure (c := ENNReal.ofReal κ)
    refine ⟨hm',Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply hm' hs, Measure.prod_apply (hm' hs)]
    have e (f : F) : volume (Prod.mk f ⁻¹' ((fun q => chart q x) ⁻¹' s)) = volume s :=
      ((R f).measurePreserving.comp (volume.measurePreserving_sub_left x)).measure_preimage hs.nullMeasurableSet
    simp only [e,lintegral_const,measure_univ,mul_one]

variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] {μ : Measure Ω} {ι : Measure Z}
variable {v r δ : ℝ} {P : PoissonIslandProcess μ ι}

theorem StationaryIslandPlacements.mass {κ : ℝ} (T : StationaryIslandPlacements ι κ) (hk : 0 ≤ κ)
    (f : Position → ℝ) (hf : Integrable f) (hm : Measurable f) (x : Position) :
    Integrable (fun z => f (T.chart z x)) ι ∧ (∫ z, f (T.chart z x) ∂ι) = κ*(∫ y, f y) := by
  have W := T.stationary x
  have hi := hf.smul_measure (c := ENNReal.ofReal κ) ENNReal.ofReal_ne_top
  refine ⟨W.integrable_comp_of_integrable hi,?_⟩
  have e := integral_map W.measurable.aemeasurable (hm.aestronglyMeasurable (μ := Measure.map (fun z => T.chart z x) ι))
  rw [W.map_eq,integral_smul_measure,ENNReal.toReal_ofReal hk] at e
  exact e.symm

/-- Place the three deterministic profiles on precisely the marks of P. -/
def tetraIslandProfiles (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (hv : 0 < v) (hd : 0 < δ) (hw : δ ≤ r/2)
    (T : StationaryIslandPlacements ι (v/(r^3/24)))
    (window : Ω → Position → Finset ℕ)
    (finite_hits : ∀ ω x n, n ∉ window ω x → 3*r ≤ ‖T.chart (P.mark ω n) x‖) :
    IslandProfiles P v := by
  have hr : 0 < r := by linarith
  have hp : 0 < r-δ := by linarith
  have vol : 0 < r^3/24 := by positivity
  have κ := div_pos hv vol
  have ti (a : ℝ) (ha : 0<a) : Integrable (smoothedIndicator (tetrahedron a) η δ) := by
    classical
    have z : Integrable ((tetrahedron a).indicator (fun _ => (1:ℝ))) :=
      (integrable_indicator_iff (tetrahedron_open a).measurableSet).2 (integrableOn_const
        (isBounded_closedBall.subset (tetrahedron_subset ha)).measure_lt_top.ne)
    exact z.integrable_convolution _ (η.scaled_integrable hd)
  have coreM : Measurable (islandCore r) := (islandCoreBump.continuous.comp (continuous_const_smul _)).pow 2 |>.measurable
  refine ⟨fun x z => smoothedIndicator (tetrahedron r) η δ (T.chart z x),
    fun x z => smoothedIndicator (tetrahedron (r-δ)) η δ (T.chart z x),fun x z => islandCore r (T.chart z x),
    fun x z => smoothedIndicator_bounds _ _ hd _,fun x z => smoothedIndicator_bounds _ _ hd _,
    fun x z => islandCore_range _ _,fun _ _ => island_layer_plateau hs hd,fun _ _ => island_core_plateau hs hd hw,
    window,?_,v*(1-δ/r)^3,islandCoreFraction*v,?_,mul_pos islandCoreFraction_pos hv,?_,?_,?_⟩
  · intro ω x n hn
    by_contra nonzero
    obtain ⟨y,hy,hxy⟩ := smoothed_support_witness hs hd nonzero
    have b := mem_closedBall.mp (tetrahedron_subset hr hy)
    have tri := dist_triangle (T.chart (P.mark ω n) x) y 0
    rw [dist_zero_right,dist_zero_right] at tri
    rw [dist_zero_right] at b
    linarith only [b,tri,finite_hits ω x n hn,hxy,hw,hr]
  · exact mul_pos hv (pow_pos (sub_pos.mpr ((div_lt_one hr).mpr (by linarith))) _)
  · intro x
    obtain ⟨i,h⟩ := T.mass κ.le _ (ti r hr) (measurable_smoothedTetrahedron η r hd) x
    exact ⟨i,by rw [h,tile_cutoff_mass_explicit η hr hd,div_mul_cancel₀ _ vol.ne']⟩
  · intro x
    obtain ⟨i,h⟩ := T.mass κ.le _ (ti (r-δ) hp) (measurable_smoothedTetrahedron η _ hd) x
    refine ⟨i,?_⟩
    rw [h,tile_cutoff_mass_explicit η hp hd]
    field_simp
  · intro x
    obtain ⟨i,h⟩ := T.mass κ.le _ (islandCore_mass hr).1 coreM x
    refine ⟨i,?_⟩
    rw [h,(islandCore_mass hr).2]
    field_simp

/-- The 3r window at x also contains all marks influencing a whole
neighborhood of x. Half a radius suffices because the support of the
outer convolution lies within 2r+δ/100 in the isometric chart. -/
theorem tetraIsland_nearby (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (hv : 0 < v) (hd : 0 < δ) (hw : δ ≤ r/2) (T : StationaryIslandPlacements ι (v/(r^3/24)))
    (window : Ω → Position → Finset ℕ)
    (finite_hits : ∀ ω x n, n ∉ window ω x → 3*r ≤ ‖T.chart (P.mark ω n) x‖) :
    ∀ ω x, ∀ᶠ y in nhds x, ∀ n, n ∉ window ω x →
      (tetraIslandProfiles η hs hv hd hw T window finite_hits).outer y (P.mark ω n) = 0 := by
  have hr : 0 < r := by linarith
  intro ω x
  filter_upwards [ball_mem_nhds x (show 0 < r/2 by linarith)] with y hy
  intro n hn
  by_contra h
  change smoothedIndicator (tetrahedron r) η δ (T.chart (P.mark ω n) y) ≠ 0 at h
  obtain ⟨u,hu,hyu⟩ := smoothed_support_witness hs hd h
  have b := mem_closedBall.mp (tetrahedron_subset hr hu)
  have tr := dist_triangle (T.chart (P.mark ω n) y) u 0
  have diff := dist_triangle (T.chart (P.mark ω n) x) (T.chart (P.mark ω n) y) 0
  rw [dist_zero_right] at b
  rw [dist_zero_right,dist_zero_right] at tr
  rw [(T.isometry _).dist_eq,dist_zero_right,dist_zero_right,dist_comm x y] at diff
  linarith only [finite_hits ω x n hn,mem_ball.mp hy,diff,tr,b,hyu,hr,hw]

end TSGA.ManyBody
