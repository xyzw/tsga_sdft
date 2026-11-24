import TSGA.IslandTetraProfiles
import TSGA.IslandOverlapTrial

/-! # Spatial and intensity bounds for the mollified tetrahedral islands -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW Set Metric

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω}
variable {ι : Measure Z} {P : PoissonIslandProcess μ ι} {v r δ L : ℝ}

private theorem pull_mass {f : Position → ℝ} {p : Position → Position}
    (hp : MeasurePreserving p volume volume) (hi : Integrable f) (hm : Measurable f) :
    Integrable (fun x => f (p x)) ∧ (∫ x, f (p x)) = ∫ x, f x := by
  refine ⟨hp.integrable_comp_of_integrable hi,?_⟩
  have e := integral_map hp.measurable.aemeasurable (hm.aestronglyMeasurable (μ := volume.map p))
  rw [hp.map_eq] at e
  exact e.symm

/-- The finite hit window can use the radius 3r ball in reference
coordinates. Its intensity is independent of x and proportional to v. -/
def tetraHitConstant := 24 * 3^3 * volume.real (ball (0 : Position) 1)

theorem StationaryIslandPlacements.tetra_hit_intensity (T : StationaryIslandPlacements ι (v/(r^3/24)))
    (hv : 0 ≤ v) (hr : 0 < r) (x : Position) :
    ι.real ((fun z => T.chart z x) ⁻¹' closedBall 0 (3*r)) = tetraHitConstant*v := by
  rw [(T.stationary x).measureReal_preimage measurableSet_closedBall.nullMeasurableSet,
    measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (div_nonneg hv (by positivity)),
    Measure.addHaar_real_closedBall volume (0 : Position) (show 0 ≤ 3*r by positivity)]
  simp only [tetraHitConstant,finrank_euclideanSpace,Fintype.card_fin]
  field_simp

/-- The core intensity is its volume fraction times v, and nestedness
bounds this fraction by one. -/
theorem tetraIslandCoreFraction_le_one (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (hv : 0 < v) (hd : 0 < δ) (hw : δ ≤ r/2) (T : StationaryIslandPlacements ι (v/(r^3/24)))
    (window : Ω → Position → Finset ℕ)
    (finite_hits : ∀ ω x n, n ∉ window ω x → 3*r ≤ ‖T.chart (P.mark ω n) x‖) :
    islandCoreFraction ≤ 1 := by
  let H := tetraIslandProfiles η hs hv hd hw T window finite_hits
  have h := integral_mono (H.inner_mass 0).1 (H.outer_mass 0).1
    (fun z => (H.core_le_layer 0 z).trans (H.layer_le_outer 0 z))
  rw [(H.inner_mass 0).2,(H.outer_mass 0).2] at h
  change islandCoreFraction*v ≤ v at h
  exact (le_of_mul_le_mul_right (h.trans_eq (one_mul v).symm) hv)

/-- All mark geometry in the overlap estimate comes from the actual
translated, rotated tetrahedra. The same finite observation window is
used in the three masks and both Fock trial states. -/
theorem tetraIslandOverlapGeometry (η : Mollifier) (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (hv : 0 < v) (hd : 0 < δ) (hw : δ ≤ r/2) (T : StationaryIslandPlacements ι (v/(r^3/24)))
    (window : Ω → Position → Finset ℕ)
    (finite_hits : ∀ ω x n, n ∉ window ω x → 3*r ≤ ‖T.chart (P.mark ω n) x‖)
    (hL : 24 ≤ L) :
    IslandOverlapGeometry (tetraIslandProfiles η hs hv hd hw T window finite_hits)
      ((L*r)^3) (L^3*r^2*δ) (L*v*δ/r) (L*r) := by
  let H := tetraIslandProfiles η hs hv hd hw T window finite_hits
  have hr : 0 < r := by linarith
  have hp : 0 < r-δ := by linarith
  have hone : 1 ≤ L := by linarith
  have hvol : r^3/24 ≤ (L*r)^3 := by
    have h := pow_le_pow_left₀ hr.le (le_mul_of_one_le_left hr.le hone) 3
    linarith only [h,pow_nonneg hr.le 3]
  have ti (a : ℝ) (ha : 0<a) : Integrable (smoothedIndicator (tetrahedron a) η δ) := by
    classical
    have z : Integrable ((tetrahedron a).indicator (fun _ => (1:ℝ))) :=
      (integrable_indicator_iff (tetrahedron_open a).measurableSet).2 (integrableOn_const
        (isBounded_closedBall.subset (tetrahedron_subset ha)).measure_lt_top.ne)
    exact z.integrable_convolution _ (η.scaled_integrable hd)
  have tile (a : ℝ) (ha : 0<a) (z : Z) : Integrable (fun x => smoothedIndicator (tetrahedron a) η δ (T.chart z x))
      ∧ (∫ x, smoothedIndicator (tetrahedron a) η δ (T.chart z x)) = a^3/24 := by
    obtain ⟨hi,he⟩ := pull_mass (T.spatial z) (ti a ha) (measurable_smoothedTetrahedron η a hd)
    exact ⟨hi,he.trans (tile_cutoff_mass_explicit η ha hd)⟩
  have out (z : Z) : Integrable (fun x => H.outer x z) ∧ (∫ x, H.outer x z) = r^3/24 := tile r hr z
  have layer (z : Z) : Integrable (fun x => H.layer x z) ∧ (∫ x, H.layer x z) = (r-δ)^3/24 := tile _ hp z
  have coreMeas : Measurable (islandCore r) := (islandCoreBump.continuous.comp (continuous_const_smul _)).pow 2 |>.measurable
  have layerMeas : Measurable (fun q : Z × Position => H.layer q.2 q.1) :=
    (measurable_smoothedTetrahedron η (r-δ) hd).comp T.measurable
  have outerMeas : Measurable (fun q : Z × Position => H.outer q.2 q.1) :=
    (measurable_smoothedTetrahedron η r hd).comp T.measurable
  have core (z : Z) : Integrable (fun x => H.inner x z) :=
    (T.spatial z).integrable_comp_of_integrable (islandCore_mass hr).1
  have Lmass (z : Z) : (∫ x, H.layer x z) ≤ (L*r)^3 :=
    ((integral_mono (layer z).1 (out z).1 fun x => H.layer_le_outer x z).trans_eq (out z).2).trans hvol
  have hα : 0 ≤ δ/r := div_nonneg hd.le hr.le
  have hα' : δ/r ≤ 1 := (div_le_one hr).mpr (by linarith)
  have shellFraction : 1 - (1 - δ/r)^3 ≤ 3*(δ/r) := by
    nlinarith only [mul_nonneg (sq_nonneg (δ/r)) (by linarith : 0 ≤ 3-δ/r)]
  constructor
  · exact ⟨layerMeas,fun z x => H.layer_range x z,fun z => ⟨(layer z).1,Lmass z⟩,fun x =>
      ⟨(H.layer_mass x).1,(integral_mono (H.layer_mass x).1 (H.outer_mass x).1 (H.layer_le_outer x)).trans_eq (H.outer_mass x).2⟩⟩
  · refine ⟨coreMeas.comp T.measurable,fun z x => H.inner_range x z,fun z => ⟨core z,?_⟩,fun x => ⟨(H.inner_mass x).1,?_⟩⟩
    · exact (integral_mono (core z) (layer z).1 (fun x => H.core_le_layer x z)).trans (Lmass z)
    · exact (integral_mono (H.inner_mass x).1 (H.outer_mass x).1
        (fun z => (H.core_le_layer x z).trans (H.layer_le_outer x z))).trans_eq (H.outer_mass x).2
  · refine ⟨outerMeas.sub layerMeas,fun z x => H.boundaryMark_range x z,fun z => ⟨(out z).1.sub (layer z).1,?_⟩,
      fun x => ⟨(H.boundaryMark_hits x).1,?_⟩⟩
    · change (∫ x, H.outer x z - H.layer x z) ≤ _
      rw [integral_sub (out z).1 (layer z).1,(out z).2,(layer z).2]
      have h1 : 1 ≤ L^3 := one_le_pow₀ hone
      have h2 : δ^3 ≤ 3*r*δ^2 := by nlinarith only [mul_nonneg (sq_nonneg δ) (by linarith : 0 ≤ 3*r-δ)]
      nlinarith only [h2,mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg r)) hd.le,
        mul_nonneg (sq_nonneg r) hd.le]
    · rw [(H.boundaryMark_hits x).2]
      change v - v*(1-δ/r)^3 ≤ L*v*δ/r
      have e := mul_le_mul_of_nonneg_left shellFraction hv.le
      have b := mul_le_mul_of_nonneg_right (show 3≤L by linarith) (mul_nonneg hv.le hα)
      calc
        _ = v*(1-(1-δ/r)^3) := by ring
        _ ≤ v*(3*(δ/r)) := e
        _ = 3*(v*(δ/r)) := by ring
        _ ≤ L*(v*(δ/r)) := b
        _ = L*v*δ/r := by ring
  · have supp (x : Position) (z : Z) (hx : H.outer x z ≠ 0) : ‖T.chart z x‖ < 3*r := by
      obtain ⟨y,hy,hxy⟩ := smoothed_support_witness hs hd hx
      have b := mem_closedBall.mp (tetrahedron_subset hr hy)
      have tri := dist_triangle (T.chart z x) y 0
      rw [dist_zero_right,dist_zero_right] at tri
      rw [dist_zero_right] at b
      linarith only [b,tri,hxy,hw,hr]
    intro x y hxy z
    by_contra h
    have tr := dist_triangle (T.chart z y) 0 (T.chart z x)
    rw [(T.isometry z).dist_eq,dist_zero_right,dist_zero_left,dist_eq_norm] at tr
    linarith only [hxy,tr,supp x z (left_ne_zero_of_mul h),supp y z (right_ne_zero_of_mul h),
      mul_le_mul_of_nonneg_right (show 6 ≤ L by linarith) hr.le]

end TSGA.ManyBody
