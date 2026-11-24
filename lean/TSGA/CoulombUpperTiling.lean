import TSGA.TetrahedronBoundary
import TSGA.SkeletonRays

/-! # Separation of the upper Coulomb tiling

The inner tile is mollified at width δ and the larger tile forming the
skeleton at width δ/2. The reference kernel has physical support radius
1/100, as in the manuscript. All distances below refer to the mollified
functions themselves.
-/

noncomputable section

namespace TSGA.SSW

open MeasureTheory Set Metric

private theorem scaled_kernel_dist {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {δ : ℝ} (hδ : 0 < δ)
    {x y : Position} (hne : η.scaled δ (x-y) ≠ 0) : dist x y ≤ δ/100 := by
  have hk : η.kernel (δ⁻¹ • (x-y)) ≠ 0 := fun h => hne (by simp [Mollifier.scaled,h])
  have h := mem_closedBall.mp (hs hk)
  rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hδ.le),← div_eq_inv_mul] at h
  rw [dist_eq_norm]
  linarith [(div_le_iff₀ hδ).mp h]

theorem smoothed_support_witness {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {δ : ℝ} (hδ : 0 < δ)
    {Ω : Set Position} {x : Position} (hx : x ∈ Function.support (smoothedIndicator Ω η δ)) :
    ∃ y ∈ Ω, dist x y ≤ δ/100 := by
  classical
  change (∫ y, Ω.indicator (fun _ => (1:ℝ)) y * η.scaled δ (x-y)) ≠ 0 at hx
  obtain ⟨y,hy⟩ := exists_ne_zero_of_integral_ne_zero hx
  exact ⟨y,by_contra fun h => hy (by simp [h]), scaled_kernel_dist hs hδ (right_ne_zero_of_mul hy)⟩

theorem smoothed_eq_one {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {δ : ℝ} (hδ : 0 < δ)
    {Ω : Set Position} {z : Position} (hz : closedBall z (δ/100) ⊆ Ω) :
    smoothedIndicator Ω η δ z = 1 := by
  classical
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  change (∫ y, Ω.indicator (fun _ => (1:ℝ)) y * η.scaled δ (z-y)) = 1
  calc
    _ = ∫ y, η.scaled δ (z-y) := by
      apply integral_congr_ae (ae_of_all _ fun y => ?_)
      by_cases hy : η.scaled δ (z-y) = 0
      · simp [hy]
      · have hm := hz (mem_closedBall.mpr ((dist_comm y z).trans_le (scaled_kernel_dist hs hδ hy)))
        simp [hm]
    _ = _ := (integral_sub_left_eq_self _ volume z).trans (η.scaled_mass hδ)

/-- At every point within δ/64 of the nonzero upper cutoff, the cutoff
used to define the complementary skeleton is identically one. -/
theorem upper_tile_plateau {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {ℓ δ : ℝ} (hδ : 0 < δ)
    {z : Position}
    (hz : z ∈ thickening (δ/64) (Function.support (smoothedIndicator (tetrahedron (ℓ-δ)) η δ))) :
    smoothedIndicator (tetrahedron (ℓ-δ/2)) η (δ/2) z = 1 := by
  obtain ⟨x,hx,hzx⟩ := mem_thickening_iff.mp hz
  obtain ⟨y,hy,hxy⟩ := smoothed_support_witness hs hδ hx
  apply smoothed_eq_one hs (half_pos hδ)
  intro u hu
  have huz := mem_closedBall.mp hu
  have hdist : dist y u < δ/32 := by
    linarith only [dist_triangle y x u, dist_triangle x z u, dist_comm y x, dist_comm x z,
      dist_comm z u, hxy, hzx, huz, hδ]
  have hw := tetrahedron_enlarge hy hdist
  convert hw using 1
  ring_nf

/-- The entire mollified support, with a collar of width δ/64, lies in the
original open tetrahedron. This applies to either smoothing width. -/
theorem upper_tile_support_inside {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {ℓ δ : ℝ} (hδ : 0 < δ) :
    thickening (δ/64) (Function.support (smoothedIndicator (tetrahedron (ℓ-δ)) η δ)) ⊆
      tetrahedron ℓ := by
  rintro z hz
  obtain ⟨x,hx,hzx⟩ := mem_thickening_iff.mp hz
  obtain ⟨y,hy,hxy⟩ := smoothed_support_witness hs hδ hx
  have hdist : dist y z < δ/16 := by
    linarith only [dist_triangle y x z,dist_comm y x,dist_comm x z,hxy,hzx,hδ]
  have hw := tetrahedron_enlarge hy hdist
  convert hw using 1
  ring_nf

/-- All the mass of a shrunken, mollified tetrahedron stays in the
original cell. -/
theorem upper_tile_mass_in_cell {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {ℓ δ : ℝ} (hδ : 0 < δ)
    (hℓ : δ < ℓ) :
    (∫ x in tetrahedron ℓ, smoothedIndicator (tetrahedron (ℓ-δ)) η δ x) = (ℓ-δ)^3/24 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, tile_cutoff_mass η (sub_pos.mpr hℓ) hδ,
    tetrahedron_volume (sub_pos.mpr hℓ)]
  intro x hout
  by_contra hn
  exact hout (upper_tile_support_inside hs hδ
    (self_subset_thickening (by positivity : 0 < δ/64) _ hn))

/-- Each cell's skeleton carries exactly the mass removed from its inner
tile. The formula uses the physical convolutions at both scales. -/
theorem upper_tile_compensated_mass {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {ℓ δ : ℝ}
    (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) :
    (∫ x in tetrahedron ℓ, smoothedIndicator (tetrahedron (ℓ-δ)) η δ x +
      Skeleton.shellCoefficient (δ/ℓ) *
        (1-smoothedIndicator (tetrahedron (ℓ-δ/2)) η (δ/2) x)) =
      regionVolume (tetrahedron ℓ) := by
  have hℓ : 0 < ℓ := by linarith
  have hfin := (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos hℓ)).2.ne
  let μ := volume.restrict (tetrahedron ℓ)
  have hmass (v : ℝ) (hv : 0 < v) (hl : v < ℓ) :=
    upper_tile_mass_in_cell hs hv hl
  have hi (v : ℝ) (hv : 0 < v) (hl : v < ℓ) :
      Integrable (smoothedIndicator (tetrahedron (ℓ-v)) η v) μ :=
    Integrable.of_integral_ne_zero ((hmass v hv hl).trans_ne (by positivity))
  have hδℓ : δ < ℓ := by linarith
  have hhalf : δ/2 < ℓ := by linarith
  have hc : Integrable (fun _ : Position => (1:ℝ)) μ := integrableOn_const hfin
  have hsub : Integrable (fun x => 1-smoothedIndicator (tetrahedron (ℓ-δ/2)) η (δ/2) x) μ :=
    hc.sub (hi _ (half_pos hδ) hhalf)
  rw [integral_add (hi _ hδ hδℓ) (hsub.const_mul (Skeleton.shellCoefficient (δ/ℓ))),
    integral_const_mul, integral_sub hc (hi _ (half_pos hδ) hhalf),setIntegral_const,
    smul_eq_mul,mul_one,hmass _ hδ hδℓ,hmass _ (half_pos hδ) hhalf]
  change (ℓ-δ)^3/24 + Skeleton.shellCoefficient (δ/ℓ) *
    (regionVolume (tetrahedron ℓ) - (ℓ-δ/2)^3/24) = _
  rw [tetrahedron_volume hℓ]
  have hfrac : 0 < δ/ℓ := div_pos hδ hℓ
  have hb : δ/ℓ ≤ 1/2 := (div_le_iff₀ hℓ).mpr (by linarith)
  have hden := (Skeleton.shellFraction_pos (half_pos hfrac) (by linarith : (δ/ℓ)/2 ≤ 1)).ne'
  have hvol (v : ℝ) : ℓ^3/24 - (ℓ-v)^3/24 = ℓ^3/24 * Skeleton.shellFraction (v/ℓ) := by
    unfold Skeleton.shellFraction
    field_simp [hℓ.ne']
  rw [hvol,show δ/2/ℓ=(δ/ℓ)/2 by ring,Skeleton.shellCoefficient]
  have hcanc : Skeleton.shellFraction (δ/ℓ) / Skeleton.shellFraction (δ/ℓ/2) *
      (ℓ^3/24 * Skeleton.shellFraction (δ/ℓ/2)) = ℓ^3/24 * Skeleton.shellFraction (δ/ℓ) := by
    rw [mul_left_comm,div_mul_cancel₀ _ hden]
  rw [hcanc,← hvol]
  ring

/-- The skeleton in the reference coordinates of a family of rigidly moved
tetrahedra. Its coefficient makes up the mass lost in the inner cutoffs. -/
def upperSkeleton {ι : Type*} (chart : ι → Position → Position) (η : Mollifier)
    (ℓ δ : ℝ) (x : Position) : ℝ :=
  Skeleton.shellCoefficient (δ/ℓ) * (1 - ∑' i,
    smoothedIndicator (tetrahedron (ℓ-δ/2)) η (δ/2) (chart i x))

/-- On a collar of each inner tile every term of the skeleton sum vanishes
apart from the one which equals one. The family can include all lattice
translates. Only pairwise disjointness of the open geometric cells is used. -/
theorem upperSkeleton_zero_near_tile {ι : Type*} (chart : ι → Position → Position)
    (hchart : ∀ i, Isometry (chart i)) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {ℓ δ : ℝ} (hδ : 0 < δ)
    (cells : Pairwise fun i j => Disjoint (chart i ⁻¹' tetrahedron ℓ) (chart j ⁻¹' tetrahedron ℓ))
    (i : ι) {x z : Position}
    (hx : smoothedIndicator (tetrahedron (ℓ-δ)) η δ (chart i x) ≠ 0)
    (hz : dist z x < δ/64) : upperSkeleton chart η ℓ δ z = 0 := by
  have hi : chart i z ∈ thickening (δ/64) (Function.support (smoothedIndicator (tetrahedron (ℓ-δ)) η δ)) :=
    mem_thickening_iff.mpr ⟨chart i x,hx,((hchart i).dist_eq z x).trans_lt hz⟩
  have hplateau := upper_tile_plateau hs hδ hi
  have hin := upper_tile_support_inside hs hδ hi
  have hdis (j : ι) (hj : j ≠ i) :
      smoothedIndicator (tetrahedron (ℓ-δ/2)) η (δ/2) (chart j z) = 0 := by
    by_contra hne
    have hnear := self_subset_thickening (by positivity : 0 < (δ/2)/64)
      (Function.support (smoothedIndicator (tetrahedron (ℓ-δ/2)) η (δ/2))) hne
    exact disjoint_left.mp (cells hj) (upper_tile_support_inside hs (half_pos hδ) hnear) hin
  simp only [upperSkeleton,tsum_eq_single i hdis,hplateau,sub_self,mul_zero]

theorem upperSkeleton_disjoint_tile {ι : Type*} (chart : ι → Position → Position)
    (hchart : ∀ i, Isometry (chart i)) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) {ℓ δ : ℝ} (hδ : 0 < δ)
    (cells : Pairwise fun i j => Disjoint (chart i ⁻¹' tetrahedron ℓ) (chart j ⁻¹' tetrahedron ℓ))
    (i : ι) :
    Disjoint (tsupport (fun x => smoothedIndicator (tetrahedron (ℓ-δ)) η δ (chart i x)))
      (tsupport (upperSkeleton chart η ℓ δ)) := by
  apply disjoint_left.mpr
  intro z htile hskel
  obtain ⟨x,hx,hzx⟩ := Metric.mem_closure_iff.mp htile (δ/128) (by positivity)
  obtain ⟨y,hy,hzy⟩ := Metric.mem_closure_iff.mp hskel (δ/128) (by positivity)
  apply hy
  apply upperSkeleton_zero_near_tile chart hchart hs hδ cells i hx
  linarith only [dist_triangle y z x,dist_comm y z,hzx,hzy]

end TSGA.SSW
