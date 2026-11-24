import TSGA.CoulombUpperTiling
import TSGA.TetrahedralLattice
import TSGA.TilingMollifier

/-! # Neutrality of the actual periodic skeleton on each tetrahedral cell -/

noncomputable section
namespace TSGA.SSW
open MeasureTheory Set Metric
open scoped Pointwise

def latticeWindow (ℓ δ : ℝ) (η : Mollifier) (p : LatticeTile) (x : Position) : ℝ :=
  smoothedIndicator (tetrahedron (ℓ-δ)) η δ (latticeChart ℓ p x)

/-- The physical upper windows, including the skeleton, have disjoint supports. -/
theorem latticeSkeleton_disjoint {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (p : LatticeTile) :
    Disjoint (tsupport (latticeWindow ℓ δ η p)) (tsupport (upperSkeleton (latticeChart ℓ) η ℓ δ)) :=
  upperSkeleton_disjoint_tile _ (latticeChart_isometry ℓ) hs hδ (latticeChart_disjoint hℓ) p

private theorem sum_window_on_cell {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    {p : LatticeTile} {x : Position} (hx : latticeChart ℓ p x ∈ tetrahedron ℓ) :
    (∑' j : LatticeTile, latticeWindow ℓ δ η j x) = latticeWindow ℓ δ η p x := by
  apply tsum_eq_single p
  intro j h
  by_contra hn
  have hm := upper_tile_support_inside hs hδ
    (self_subset_thickening (by positivity : 0 < δ/64)
      (Function.support (smoothedIndicator (tetrahedron (ℓ-δ)) η δ)) hn)
  exact disjoint_left.mp (latticeChart_disjoint hℓ h) hm hx

/-- The compensated periodic charge has exactly zero mean on each of the
24 tetrahedra and on each translated copy, before rotation or dilation. -/
theorem latticeSkeleton_cell_neutral {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (p : LatticeTile) :
    (∫ x in latticeChart ℓ p ⁻¹' tetrahedron ℓ,
      (∑' j : LatticeTile, latticeWindow ℓ δ η j x) + upperSkeleton (latticeChart ℓ) η ℓ δ x) =
      regionVolume (tetrahedron ℓ) := by
  have hℓ : 0 < ℓ := by linarith
  let f := fun y => smoothedIndicator (tetrahedron (ℓ-δ)) η δ y + Skeleton.shellCoefficient (δ/ℓ) *
      (1-smoothedIndicator (tetrahedron (ℓ-δ/2)) η (δ/2) y)
  let S := latticeChart ℓ p ⁻¹' tetrahedron ℓ
  have hS : MeasurableSet S := (tetrahedron_open ℓ).measurableSet.preimage
    (latticeChart_isometry ℓ p).continuous.measurable
  calc
    _ = ∫ x in S, f (latticeChart ℓ p x) := by
      apply setIntegral_congr_fun hS
      intro x hx
      have ha := sum_window_on_cell hℓ hδ hs hx
      have hb := sum_window_on_cell hℓ (half_pos hδ) hs hx
      change _ + (Skeleton.shellCoefficient (δ/ℓ) *
        (1 - ∑' j, latticeWindow ℓ (δ/2) η j x)) = _
      rw [ha,hb]
      rfl
    _ = ∫ y in tetrahedron ℓ, f y :=
      (latticeChart_preserving ℓ p).setIntegral_preimage_emb (latticeChartEquiv ℓ p).toHomeomorph.measurableEmbedding f _
    _ = _ := upper_tile_compensated_mass hs hδ hscale

theorem latticeWindow_periodic (ℓ δ : ℝ) (η : Mollifier) (m : Fin 3 → ℤ) (x : Position) :
    (∑' p : LatticeTile, latticeWindow ℓ δ η p (latticeShift ℓ m + x)) =
      ∑' p : LatticeTile, latticeWindow ℓ δ η p x := by
  let e : LatticeTile ≃ LatticeTile := (Equiv.addRight (-m)).prodCongr (Equiv.refl _)
  have step (p : LatticeTile) :
      latticeChart ℓ p (latticeShift ℓ m+x) = latticeChart ℓ (e p) x := by
    obtain ⟨n,o⟩ := p
    have coord (i : Fin 3) : (latticeShift ℓ m+x) i - ℓ*(n i:ℝ) =
        x i - ℓ*((n+ -m) i:ℝ) := by simp [latticeShift,mul_add]; ring
    change latticeChart ℓ (n,o) _ = latticeChart ℓ (n+ -m,o) x
    simp only [latticeChart,coord]
  simp_rw [latticeWindow,step]
  exact e.tsum_eq (fun p => smoothedIndicator (tetrahedron (ℓ-δ)) η δ (latticeChart ℓ p x))

/-- Mass of the compensated periodic windows on the fundamental cube. -/
theorem latticeWindow_cube_integral {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) :
    (∫ y in latticeCube ℓ 0, (∑' j : LatticeTile, latticeWindow ℓ δ η j y) +
      upperSkeleton (latticeChart ℓ) η ℓ δ y) = ℓ^3 := by
  have hℓ : 0 < ℓ := by linarith
  let S (o : CubeOrientation) := latticeChart ℓ ((0 : Fin 3 → ℤ),o) ⁻¹' tetrahedron ℓ
  let f (y : Position) := (∑' j : LatticeTile, latticeWindow ℓ δ η j y) +
    upperSkeleton (latticeChart ℓ) η ℓ δ y
  have cell (o : CubeOrientation) : (∫ y in S o, f y) = regionVolume (tetrahedron ℓ) :=
    latticeSkeleton_cell_neutral hδ hscale hs _
  rw [setIntegral_congr_set (latticeCube_eq_cells_ae hℓ 0)]
  change (∫ y in ⋃ o, S o, f y) = _
  rw [integral_iUnion_fintype (fun o => (tetrahedron_open ℓ).measurableSet.preimage
    (latticeChart_isometry ℓ (0,o)).continuous.measurable)
    (fun i j h => latticeChart_disjoint hℓ (show ((0,i) : LatticeTile) ≠ (0,j) from fun e => h (congrArg Prod.snd e)))
    (fun o => Integrable.of_integral_ne_zero ((cell o).trans_ne (tetrahedron_volume_pos hℓ).ne'))]
  change (∑ o : CubeOrientation, ∫ y in S o, f y) = ℓ^3
  simp_rw [cell]
  simp only [Finset.sum_const, Finset.card_univ, card_cubeOrientation, nsmul_eq_mul, tetrahedron_volume hℓ]
  norm_num
  ring

/-- The physical resolution of the identity after averaging the translation
of the lattice. The cube integral is unnormalized. -/
theorem latticeWindow_mean {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (x : Position) :
    (∫ τ in latticeCube ℓ 0, (∑' j : LatticeTile, latticeWindow ℓ δ η j (x-τ)) +
      upperSkeleton (latticeChart ℓ) η ℓ δ (x-τ)) = ℓ^3 := by
  have hℓ : 0 < ℓ := by linarith
  let C := latticeCube ℓ 0
  let f (y : Position) := (∑' j : LatticeTile, latticeWindow ℓ δ η j y) +
    upperSkeleton (latticeChart ℓ) η ℓ δ y
  have full : (∫ y in C, f y) = ℓ^3 := latticeWindow_cube_integral hδ hscale hs
  have : Countable (latticeShift ℓ).range := Set.Countable.to_subtype
    (s := Set.range (latticeShift ℓ)) (Set.countable_range _)
  have per (g : (latticeShift ℓ).range) (y : Position) : f (g +ᵥ y) = f y := by
    obtain ⟨_,m,rfl⟩ := g
    unfold f upperSkeleton
    change (∑' j, latticeWindow ℓ δ η j (latticeShift ℓ m + y)) +
      _ * (1 - ∑' j, latticeWindow ℓ (δ/2) η j (latticeShift ℓ m + y)) = _
    rw [latticeWindow_periodic,latticeWindow_periodic]
    rfl
  have hc := latticeCube_fundamental hℓ
  have hset : ((fun τ : Position => x-τ) ⁻¹' (x +ᵥ C)) = C := by
    ext τ
    rw [mem_preimage,mem_vadd_set_iff_neg_vadd_mem]
    change (-x + (x-τ) ∈ latticeCube ℓ 0) ↔ _
    rw [show -x+(x-τ) = -τ by abel]
    simp [C,latticeCube]
  change (∫ τ in C, f (x-τ)) = _
  rw [← hset]
  have emb : MeasurableEmbedding (fun τ : Position => x-τ) :=
    (Homeomorph.addLeft x).measurableEmbedding.comp (Homeomorph.neg Position).measurableEmbedding
  rw [(volume.measurePreserving_sub_left x).setIntegral_preimage_emb emb]
  exact ((hc.vadd_of_comm x).setIntegral_eq hc per).trans full

end TSGA.SSW
