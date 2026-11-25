import TSGA.CoulombLatticeSkeleton
import TSGA.TetrahedronFlux

/-! # The charge fluctuation as a difference of two smoothed periodic shells -/

noncomputable section
namespace TSGA.SSW
open MeasureTheory Set

/-- The region removed when all tetrahedra of the period-ℓ lattice are shrunk
by width δ about their own centers. -/
def latticeShell (ℓ δ : ℝ) : Set Position :=
  (⋃ p : LatticeTile, latticeChart ℓ p ⁻¹' tetrahedron (ℓ-δ))ᶜ

theorem latticeShell_measurable (ℓ δ : ℝ) : MeasurableSet (latticeShell ℓ δ) :=
  (MeasurableSet.iUnion fun p => (tetrahedron_open _).measurableSet.preimage
    (latticeChart_isometry ℓ p).continuous.measurable).compl

private theorem rigid_smoothedIndicator (e : Position ≃ᵢ Position)
    (hp : MeasurePreserving e volume volume) (S : Set Position) (η : Mollifier)
    (δ : ℝ) (x : Position) :
    smoothedIndicator S η δ (e x) = smoothedIndicator (e ⁻¹' S) η δ x := by
  classical
  let f := fun z : Position => S.indicator (fun _ => (1:ℝ)) z * η.scaled δ (e x-z)
  change (∫ z, f z) = _
  rw [← hp.integral_comp e.toHomeomorph.measurableEmbedding f]
  apply integral_congr_ae (ae_of_all _ fun z => ?_)
  have eqn : η.scaled δ (e x-e z) = η.scaled δ (x-z) := by
    unfold Mollifier.scaled
    congr 1
    apply η.radial
    simp only [norm_smul, ← dist_eq_norm, e.dist_eq]
  change S.indicator (fun _ => (1:ℝ)) (e z) * η.scaled δ (e x-e z) = (e ⁻¹' S).indicator (fun _ => (1:ℝ)) z * η.scaled δ (x-z)
  simp [eqn,Set.indicator]

private theorem smoothed_as_setIntegral (S : Set Position) (hS : MeasurableSet S)
    (η : Mollifier) (δ : ℝ) (x : Position) :
    smoothedIndicator S η δ x = ∫ z in S, η.scaled δ (x-z) := by
  classical
  change (∫ z, S.indicator (fun _ => (1:ℝ)) z * η.scaled δ (x-z)) = _
  rw [← integral_indicator hS]
  apply integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases h : z ∈ S <;> simp [h]

/-- A vacancy of the smoothed tiling equals the convolution of the actual
unsmoothed vacancy set. This uses the radiality of the kernel for all 24 charts. -/
theorem latticeWindow_vacancy {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (η : Mollifier) (x : Position) :
    1 - ∑' p : LatticeTile, latticeWindow ℓ δ η p x = smoothedIndicator (latticeShell ℓ δ) η δ x := by
  classical
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  let S := fun p : LatticeTile => latticeChart ℓ p ⁻¹' tetrahedron (ℓ-δ)
  have hm (p) : MeasurableSet (S p) := (tetrahedron_open _).measurableSet.preimage
    (latticeChart_isometry ℓ p).continuous.measurable
  have sub (p) : S p ⊆ latticeChart ℓ p ⁻¹' tetrahedron ℓ := fun _ h =>
    tetrahedron_mono (sub_le_self ℓ hδ.le) h
  have hd (i j : LatticeTile) (h : i ≠ j) : Disjoint (S i) (S j) :=
    (latticeChart_disjoint hℓ h).mono (sub _) (sub _)
  have hi := (η.scaled_integrable hδ).comp_sub_left x
  have eqn (p : LatticeTile) : latticeWindow ℓ δ η p x = ∫ z in S p, η.scaled δ (x-z) := by
    exact (rigid_smoothedIndicator (latticeChartEquiv ℓ p) (latticeChart_preserving ℓ p)
      _ η δ x).trans (smoothed_as_setIntegral _ (hm p) η δ x)
  simp_rw [eqn]
  rw [← integral_iUnion hm hd hi.integrableOn, smoothed_as_setIntegral _ (latticeShell_measurable _ _)]
  change _ = ∫ z in (⋃ p, S p)ᶜ, η.scaled δ (x-z)
  rw [setIntegral_compl (MeasurableSet.iUnion hm) hi,integral_sub_left_eq_self (η.scaled δ) volume x,η.scaled_mass hδ]

/-- The physical error used in the averaged Hartree term. Both terms here
are actual convolutions of positive shell densities at their own width. -/
theorem lattice_charge_shells {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (η : Mollifier) (x : Position) :
    (∑' p : LatticeTile, latticeWindow ℓ δ η p x) + upperSkeleton (latticeChart ℓ) η ℓ δ x - 1 =
      Skeleton.shellCoefficient (δ/ℓ) * smoothedIndicator (latticeShell ℓ (δ/2)) η (δ/2) x -
        smoothedIndicator (latticeShell ℓ δ) η δ x := by
  rw [← latticeWindow_vacancy hℓ hδ, ← latticeWindow_vacancy hℓ (half_pos hδ)]
  change _ + (Skeleton.shellCoefficient (δ/ℓ) * (1 - ∑' p, latticeWindow ℓ (δ/2) η p x)) - 1 = _
  ring

/-- Within a fundamental cube the periodic vacancy consists of one shell in
each of the 24 actual affine cells. The interfaces are Lebesgue null. -/
theorem latticeShell_cube_ae {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) :
    (latticeCube ℓ 0 ∩ latticeShell ℓ δ : Set Position) =ᵐ[volume]
      ⋃ o : CubeOrientation, latticeChart ℓ (0,o) ⁻¹' (tetrahedron ℓ \ tetrahedron (ℓ-δ)) := by
  filter_upwards [latticeCube_eq_cells_ae hℓ 0] with x hx
  constructor
  · rintro ⟨hc,hs⟩
    obtain ⟨o,ho⟩ := mem_iUnion.mp (hx.mp hc)
    refine mem_iUnion.mpr ⟨o,ho,?_⟩
    exact fun h => hs (mem_iUnion.mpr ⟨(0,o),h⟩)
  · intro h
    obtain ⟨o,ho,hs⟩ := mem_iUnion.mp h
    refine ⟨latticeChart_cell_subset_cube (ℓ := ℓ) (0,o) (a := x) ho,?_⟩
    intro hm
    obtain ⟨p,hp⟩ := mem_iUnion.mp hm
    by_cases he : p = (0,o)
    · subst p
      exact hs hp
    · exact disjoint_left.mp (latticeChart_disjoint hℓ he)
        (tetrahedron_mono (sub_le_self ℓ hδ) hp) ho

theorem latticeShell_mem_shift {ℓ δ : ℝ} (m : Fin 3 → ℤ) (x : Position) :
    latticeShift ℓ m + x ∈ latticeShell ℓ δ ↔ x ∈ latticeShell ℓ δ := by
  let e : LatticeTile ≃ LatticeTile := (Equiv.addRight (-m)).prodCongr (Equiv.refl _)
  have step (p : LatticeTile) : latticeChart ℓ p (latticeShift ℓ m+x) = latticeChart ℓ (e p) x := by
    obtain ⟨n,o⟩ := p
    have coord (i : Fin 3) : (latticeShift ℓ m+x) i - ℓ*(n i:ℝ) =
        x i - ℓ*((n+ -m) i:ℝ) := by simp [latticeShift,mul_add]; ring
    change latticeChart ℓ (n,o) _ = latticeChart ℓ (n+ -m,o) x
    simp only [latticeChart,coord]
  simp only [latticeShell,mem_compl_iff,mem_iUnion,mem_preimage,step]
  apply not_congr
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨e p,hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨e.symm p,by simpa using hp⟩

/-- Simultaneously dilating the cell, its vacancy and the kernel leaves the
dimensionless occupancy unchanged. -/
theorem smoothed_tetrahedron_dilate {t : ℝ} (ht : 0 < t) (r d : ℝ)
    (η : Mollifier) (x : Position) :
    smoothedIndicator (tetrahedron (t*r)) η (t*d) (t • x) = smoothedIndicator (tetrahedron r) η d x := by
  classical
  let f (y : Position) := (tetrahedron r).indicator (fun _ => (1:ℝ)) y * η.scaled d (x-y)
  have eqn (y : Position) :
      (tetrahedron (t*r)).indicator (fun _ => (1:ℝ)) y * η.scaled (t*d) (t • x-y) =
        (t^3)⁻¹ * f (t⁻¹ • y) := by
    have mem : y ∈ tetrahedron (t*r) ↔ t⁻¹ • y ∈ tetrahedron r := by
      rw [← tetrahedronRadius_lt, ← tetrahedronRadius_lt,tetrahedronRadius_smul (inv_nonneg.mpr ht.le)]
      rw [← div_eq_inv_mul,div_lt_iff₀ ht,mul_comm]
    have eq : (t*d)⁻¹ • (t • x-y) = d⁻¹ • (x-t⁻¹ • y) := by
      rw [mul_inv_rev, mul_smul, smul_sub, inv_smul_smul₀ ht.ne']
    by_cases hy : y ∈ tetrahedron (t*r)
    · simp only [f,Set.indicator_of_mem hy, Set.indicator_of_mem (mem.mp hy),one_mul,
        Mollifier.scaled,eq,mul_pow]
      rw [mul_inv_rev]
      ring
    · simp [f,hy,mt mem.mpr hy]
  change (∫ y, (tetrahedron (t*r)).indicator (fun _ => (1:ℝ)) y * η.scaled (t*d) (t • x-y)) = ∫ y, f y
  simp_rw [eqn]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume f ht.le]
  simp [finrank_euclideanSpace,ht.ne',smul_eq_mul]

theorem latticeWindow_dilate {t : ℝ} (ht : 0 < t) (ℓ δ : ℝ) (η : Mollifier)
    (p : LatticeTile) (x : Position) :
    latticeWindow (t*ℓ) (t*δ) η p (t • x) = latticeWindow ℓ δ η p x := by
  unfold latticeWindow
  rw [← mul_sub,latticeChart_dilate,smoothed_tetrahedron_dilate ht]

theorem lattice_fluctuation_dilate {t : ℝ} (ht : 0 < t) (ℓ δ : ℝ) (η : Mollifier) (x : Position) :
    (∑' p : LatticeTile, latticeWindow (t*ℓ) (t*δ) η p (t • x)) +
      upperSkeleton (latticeChart (t*ℓ)) η (t*ℓ) (t*δ) (t • x) - 1 =
    (∑' p : LatticeTile, latticeWindow ℓ δ η p x) + upperSkeleton (latticeChart ℓ) η ℓ δ x - 1 := by
  change _ + (Skeleton.shellCoefficient _ * (1-∑' p, latticeWindow _ ((t*δ)/2) η p (t • x))) - 1 = _
  rw [mul_div_mul_left _ _ ht.ne',mul_div_assoc]
  simp_rw [latticeWindow_dilate ht]
  rfl

end TSGA.SSW
