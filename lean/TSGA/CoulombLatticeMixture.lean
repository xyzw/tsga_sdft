import TSGA.CountableCoulombBlocks
import TSGA.CoulombLatticeSkeleton
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # The disjoint trial over translations of the Coulomb lattice -/

noncomputable section
namespace TSGA.SSW

open MeasureTheory Set Metric
open scoped Pointwise

/-- One block for the skeleton, one block for each lattice tetrahedron. -/
def latticeBlock (ℓ δ : ℝ) (η : Mollifier) : Option LatticeTile → Position → ℝ
  | none => upperSkeleton (latticeChart ℓ) η ℓ δ
  | some i => latticeWindow ℓ δ η i

theorem latticeBlock_pairwise {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) :
    Pairwise fun i j => Disjoint (Function.support (latticeBlock ℓ δ η i))
      (Function.support (latticeBlock ℓ δ η j)) := by
  have window (p : LatticeTile) : Function.support (latticeWindow ℓ δ η p) ⊆
      latticeChart ℓ p ⁻¹' tetrahedron ℓ := by
    intro x hx
    exact upper_tile_support_inside hs hδ (self_subset_thickening
      (by positivity : 0 < δ/64) (Function.support (smoothedIndicator (tetrahedron (ℓ-δ)) η δ)) hx)
  have sk (p : LatticeTile) := (latticeSkeleton_disjoint hℓ hδ hs p).mono
    (subset_tsupport _) (subset_tsupport _)
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j => exact (sk j).symm
  | some i =>
    cases j with
    | none => exact sk i
    | some j => exact (latticeChart_disjoint hℓ (fun h => hij (congrArg some h))).mono (window i) (window j)

/-- A common finite set of blocks for all translations in the fundamental
cube and all orthogonal rotations of a profile supported in a fixed ball. -/
theorem latticeWindow_finite_range {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (B : ℝ) :
    ∃ T : Finset LatticeTile, ∀ (R : Position ≃ₗᵢ[ℝ] Position) τ, τ ∈ latticeCube ℓ 0 →
      ∀ x, ‖x‖ ≤ B → ∀ p ∉ T, latticeWindow ℓ δ η p (R x - τ) = 0 := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (B/ℓ+1)
  let T : Finset LatticeTile := (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N:ℤ)) (N:ℤ))).product Finset.univ
  refine ⟨T, fun R τ hτ x hx p hp => by_contra fun hn => hp ?_⟩
  have hcell := latticeChart_cell_subset_cube p (upper_tile_support_inside hs hδ (self_subset_thickening
    (by positivity : 0 < δ/64) (Function.support (smoothedIndicator (tetrahedron (ℓ-δ)) η δ)) hn))
  have hN' : B + ℓ < (N:ℝ)*ℓ := by
    have ha := (div_lt_iff₀ hℓ).mp (show B/ℓ < (N:ℝ)-1 by linarith)
    linarith
  have bounds (i : Fin 3) : -(N:ℤ) ≤ p.1 i ∧ p.1 i ≤ (N:ℤ) := by
    have hz := abs_lt.mp (hcell i)
    have hy := abs_lt.mp (hτ i)
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, sub_zero] at hy
    have hx' : |R x i| ≤ B := by
      exact (PiLp.norm_apply_le (R x) i).trans ((R.norm_map x).le.trans hx)
    have hxi := abs_le.mp hx'
    change - (ℓ/2) < R x i - τ i - ℓ * (p.1 i:ℝ) ∧ R x i - τ i - ℓ*(p.1 i:ℝ) < ℓ/2 at hz
    have hLow : -(N:ℝ) < (p.1 i:ℝ) := (lt_of_mul_lt_mul_left
      (show ℓ * (-(N:ℝ)) < ℓ * (p.1 i:ℝ) by nlinarith only [hz.1,hz.2,hxi.1,hxi.2,hy.1,hy.2,hN']) hℓ.le)
    have hHi : (p.1 i:ℝ) < (N:ℝ) := (lt_of_mul_lt_mul_left
      (show ℓ * (p.1 i:ℝ) < ℓ * (N:ℝ) by nlinarith only [hz.1,hz.2,hxi.1,hxi.2,hy.1,hy.2,hN']) hℓ.le)
    exact_mod_cast And.intro hLow.le hHi.le
  exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr (bounds i)), Finset.mem_univ _⟩

/-- A probability law for a shift uniformly distributed over the cube. -/
def latticeShiftMeasure (ℓ : ℝ) : Measure Position :=
  (ENNReal.ofReal (ℓ^3))⁻¹ • volume.restrict (latticeCube ℓ 0)

theorem latticeShiftMeasure_probability {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsProbabilityMeasure (latticeShiftMeasure ℓ) := by
  have hc := latticeCube_volume hℓ 0
  have hp : 0 < regionVolume (latticeCube ℓ 0) := hc ▸ pow_pos hℓ 3
  have hfin := (ENNReal.toReal_pos_iff.mp hp).2.ne
  have hmass : volume (latticeCube ℓ 0) = ENNReal.ofReal (ℓ^3) := by
    rw [← hc]
    exact (ENNReal.ofReal_toReal hfin).symm
  constructor
  simp only [latticeShiftMeasure,Measure.smul_apply,Measure.restrict_apply_univ,hmass,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hℓ 3)) ENNReal.ofReal_ne_top

theorem ae_latticeShift_mem (ℓ : ℝ) : ∀ᵐ τ ∂latticeShiftMeasure ℓ, τ ∈ latticeCube ℓ 0 := by
  exact Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem (latticeCube_measurable ℓ 0))

def latticeTotalWindow (ℓ δ : ℝ) (η : Mollifier) (y : Position) : ℝ :=
  (∑' p : LatticeTile, latticeWindow ℓ δ η p y) + upperSkeleton (latticeChart ℓ) η ℓ δ y

theorem latticeTotalWindow_shift_mean {ℓ δ : ℝ} (hδ : 0 < δ) (hsc : δ ≤ ℓ/2)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (y : Position) :
    (∫ τ, latticeTotalWindow ℓ δ η (y-τ) ∂latticeShiftMeasure ℓ) = 1 := by
  have hℓ : 0 < ℓ := by linarith
  rw [latticeShiftMeasure, integral_smul_measure]
  change _ • (∫ τ in latticeCube ℓ 0, _) = _
  rw [show (∫ τ in latticeCube ℓ 0, latticeTotalWindow ℓ δ η (y-τ)) = ℓ^3 from
    latticeWindow_mean hδ hsc hs y]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3), hℓ.ne']

end TSGA.SSW

namespace TSGA.SSW

open MeasureTheory Set Metric

private theorem latticeWindow_sum_bounds {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (y : Position) :
    (∑' p : LatticeTile, latticeWindow ℓ δ η p y) ∈ Icc 0 1 := by
  by_cases h : ∃ p : LatticeTile, latticeWindow ℓ δ η p y ≠ 0
  · obtain ⟨p,hp⟩ := h
    rw [tsum_eq_single p]
    · exact smoothedIndicator_bounds _ η hδ _
    · intro j hj
      by_contra hn
      exact disjoint_left.mp (latticeBlock_pairwise hℓ hδ hs
        (i := some j) (j := some p) (fun he => hj (Option.some_inj.mp he))) hn hp
  · push Not at h
    simp [h]

theorem latticeTotalWindow_bounds {ℓ δ : ℝ} (hδ : 0 < δ) (hsc : δ ≤ ℓ/2)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (y : Position) :
    latticeTotalWindow ℓ δ η y ∈ Icc 0 3 := by
  have hℓ : 0 < ℓ := by linarith
  have ha := latticeWindow_sum_bounds hℓ hδ hs y
  have hb := latticeWindow_sum_bounds hℓ (half_pos hδ) hs y
  have hc := Skeleton.shellCoefficient_bounds (div_pos hδ hℓ)
    ((div_le_iff₀ hℓ).2 (by linarith))
  change 0 ≤ _ + Skeleton.shellCoefficient (δ/ℓ)*(1-∑' i, latticeWindow ℓ (δ/2) η i y) ∧ _ ≤ 3
  constructor
  · exact add_nonneg ha.1 (mul_nonneg hc.1 (sub_nonneg.mpr hb.2))
  · change (∑' p : LatticeTile, latticeWindow ℓ δ η p y) + Skeleton.shellCoefficient (δ/ℓ) *
      (1-∑' p : LatticeTile, latticeWindow ℓ (δ/2) η p y) ≤ 3
    nlinarith only [ha.2,hc.2,mul_nonneg hc.1 hb.1]

theorem latticeTotalWindow_measurable (ℓ : ℝ) {δ : ℝ} (hδ : 0 < δ) (η : Mollifier) :
    Measurable (latticeTotalWindow ℓ δ η) := by
  have hm {e : ℝ} (he : 0 < e) (p : LatticeTile) : Measurable (latticeWindow ℓ e η p) :=
    (ManyBody.measurable_smoothedTetrahedron η _ he).comp (latticeChart_isometry ℓ p).continuous.measurable
  exact (Measurable.tsum (hm hδ)).add
    (measurable_const.mul (measurable_const.sub (Measurable.tsum (hm (half_pos hδ)))))

theorem latticeBlock_measurable (ℓ : ℝ) {δ : ℝ} (hδ : 0 < δ) (η : Mollifier) (p : Option LatticeTile) :
    Measurable (latticeBlock ℓ δ η p) := by
  have hm {b : ℝ} (hb : 0 < b) (i : LatticeTile) : Measurable (latticeWindow ℓ b η i) :=
    (ManyBody.measurable_smoothedTetrahedron η _ hb).comp (latticeChart_isometry ℓ i).continuous.measurable
  cases p with
  | some i => exact hm hδ i
  | none => exact measurable_const.mul (measurable_const.sub (Measurable.tsum (hm (half_pos hδ))))

theorem latticeBlock_bounds {ℓ δ : ℝ} (hδ : 0 < δ) (hsc : δ ≤ ℓ/2)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (p : Option LatticeTile)
    (x : Position) : latticeBlock ℓ δ η p x ∈ Icc 0 2 := by
  cases p with
  | some p =>
    have h := smoothedIndicator_bounds (tetrahedron (ℓ-δ)) η hδ (latticeChart ℓ p x)
    exact ⟨h.1,h.2.trans (by norm_num)⟩
  | none =>
    have hℓ : 0 < ℓ := by linarith
    have hc := Skeleton.shellCoefficient_bounds (div_pos hδ hℓ) ((div_le_iff₀ hℓ).2 (by linarith))
    have hb := latticeWindow_sum_bounds hℓ (half_pos hδ) hs x
    exact ⟨mul_nonneg hc.1 (sub_nonneg.mpr hb.2), (mul_le_of_le_one_right hc.1 (sub_le_self _ hb.1)).trans hc.2⟩

end TSGA.SSW

namespace TSGA.ManyBody

open MeasureTheory SSW Set Metric

def latticeBlockDensity (ℓ δ : ℝ) (η : Mollifier) (R : Position ≃ₗᵢ[ℝ] Position)
    (D : Position → SpinMatrix) (τ : Position) (p : Option LatticeTile) (x : Position) : SpinMatrix :=
  (latticeBlock ℓ δ η p (R x-τ) : ℂ) • D x

def latticeBlockEnergySum (ℓ δ : ℝ) (η : Mollifier) (R : Position ≃ₗᵢ[ℝ] Position)
    (D : Position → SpinMatrix) (τ : Position) : ℝ :=
  energy (latticeBlockDensity ℓ δ η R D τ none) + ∑' p, energy (latticeBlockDensity ℓ δ η R D τ (some p))

theorem latticeBlock_sum_enum {A : Type*} [NormedAddCommGroup A] (T : Finset LatticeTile)
    (g : Option LatticeTile → A) (hg : ∀ p ∉ T, g (some p) = 0) :
    let e := (Fintype.equivFin (Option T)).symm
    (∑ i, g ((e i).map Subtype.val)) = g none + ∑' p, g (some p) := by
  classical
  intro e
  rw [tsum_eq_sum hg, e.sum_comp (fun k => g (k.map Subtype.val))]
  simp only [Fintype.sum_option,Option.map_none,Option.map_some,Finset.univ_eq_attach]
  rw [Finset.sum_attach T (fun p => g (some p))]

private theorem disjoint_lattice_densities {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    {η : Mollifier} (hs : Function.support η.kernel ⊆ closedBall 0 (1/100))
    (R : Position ≃ₗᵢ[ℝ] Position) (D : Position → SpinMatrix) (τ : Position) :
    Pairwise fun i j => Disjoint (Function.support (latticeBlockDensity ℓ δ η R D τ i))
      (Function.support (latticeBlockDensity ℓ δ η R D τ j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  apply (disjoint_left.mp (latticeBlock_pairwise hℓ hδ hs hij)) (a := R x - τ)
  · intro h
    exact hi (by simp [latticeBlockDensity,h])
  · intro h
    exact hj (by simp [latticeBlockDensity,h])

private theorem integrable_bounded_pair {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} {f g k : Z → ℝ}
    (hk : Integrable k ν) (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hfb : ∀ z, |f z| ≤ B) (hgb : ∀ z, |g z| ≤ B) :
    Integrable (fun z => f z * g z * k z) ν := by
  apply (hk.norm.const_mul (B*B)).mono' ((hf.mul hg).aestronglyMeasurable.mul hk.aestronglyMeasurable)
  filter_upwards with z
  change ‖f z * g z * k z‖ ≤ B * B * ‖k z‖
  simp only [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hfb z) (hgb z) (abs_nonneg _) ((abs_nonneg _).trans (hfb z)))
    (abs_nonneg _)

private theorem jointDirect_window {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {w : Ω → Position → ℝ} (hw : Measurable (Function.uncurry w)) {B : ℝ} (hb : ∀ ω x, |w ω x| ≤ B)
    (r : Position → ℝ) (hr : Integrable (directKernel r r) pairVolume) :
    JointDirectIntegrable μ (fun ω x => w ω x*r x) := by
  have h₁ : Measurable (fun z : Ω × PairSpace => w z.1 z.2.1) := hw.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h₂ : Measurable (fun z : Ω × PairSpace => w z.1 z.2.2) := hw.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply (integrable_bounded_pair (hr.comp_snd μ) h₁ h₂ (fun z => hb _ _) (fun z => hb _ _)).congr
  filter_upwards with z
  change _ * _ * (r z.2.1 * r z.2.2 / _) = _ * _ / _
  ring

set_option maxHeartbeats 1800000 in
/-- The fixed-rotation Coulomb trial over one whole translation cell.
The right side retains the centered direct energy until averaging also
over the rotations and dilations. -/
private theorem coulomb_variable_lattice_shifts_of_measurable (tensor : DisjointFockTensorization)
    (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (R : Position ≃ₗᵢ[ℝ] Position)
    (D : Position → SpinMatrix) (hmD : ∀ i j, Measurable (fun x => D x i j))
    (hD : ∀ i j, Integrable (fun x => D x i j)) :
    let μ := latticeShiftMeasure ℓ
    let W := fun τ x => latticeTotalWindow ℓ δ η (R x-τ)
    let r := fun x => (D x).trace.re
    let blocks := latticeBlockDensity ℓ δ η R D
    (∀ᵐ τ ∂μ, ∀ p, ∃ Γ, feasible (blocks τ p) Γ) →
    (∀ᵐ τ ∂μ, Summable (fun p => energy (blocks τ (some p)))) →
    Integrable (latticeBlockEnergySum ℓ δ η R D) μ →
    Integrable (directKernel r r) pairVolume →
    energy D ≤ (∫ τ, latticeBlockEnergySum ℓ δ η R D τ ∂μ) +
      ∫ τ, hartree (fun x => (W τ x-1)*r x) ∂μ := by
  classical
  intro μ W r blocks rep sumE hE hr
  have hℓ : 0 < ℓ := by linarith
  let : IsProbabilityMeasure μ := latticeShiftMeasure_probability hℓ
  let u := fun τ x => (W τ x : ℂ) • D x
  have hme : Measurable (fun z : Position × Position => W z.1 z.2) :=
    (latticeTotalWindow_measurable ℓ hδ η).comp ((R.continuous.measurable.comp measurable_snd).sub measurable_fst)
  have bound (τ x : Position) : W τ x ∈ Icc 0 3 := latticeTotalWindow_bounds hδ hscale hs _
  have hjoint := jointDirect_window (μ := μ) (w := W) hme (B := 3)
    (fun τ x => (abs_of_nonneg (bound τ x).1).trans_le (bound τ x).2) r hr
  have hdev : JointDirectIntegrable μ (fun τ x => W τ x*r x-r x) := by
    have hM : Measurable (Function.uncurry (fun τ x => W τ x-1)) := hme.sub measurable_const
    have h := jointDirect_window (μ := μ) (w := fun τ x => W τ x-1) hM (B := 3) (fun τ x => abs_le.mpr
      ⟨by linarith only [(bound τ x).1],by linarith only [(bound τ x).2]⟩) r hr
    simpa only [sub_mul,one_mul] using h
  have pair (τ : Position) (i j : Option LatticeTile) :
      Integrable (directKernel (fun x => (blocks τ i x).trace.re) (fun x => (blocks τ j x).trace.re)) pairVolume := by
    let b := fun p x => latticeBlock ℓ δ η p (R x-τ)
    have bm (p : Option LatticeTile) : Measurable (b p) :=
      (latticeBlock_measurable ℓ hδ η p).comp (R.continuous.measurable.sub_const τ)
    have bb (p : Option LatticeTile) (x : Position) : |b p x| ≤ 2 := by
      have hp := latticeBlock_bounds hδ hscale hs p (R x-τ)
      exact (abs_of_nonneg hp.1).trans_le hp.2
    apply (integrable_bounded_pair hr ((bm i).comp measurable_fst) ((bm j).comp measurable_snd)
      (fun z => bb i z.1) (fun z => bb j z.2)).congr
    filter_upwards with z
    simp [directKernel,blocks,latticeBlockDensity,Matrix.trace_smul,b,r]
    ring
  have hm (i j : Fin 2) : Measurable (fun z : Position × Position => u z.1 z.2 i j) :=
    (Complex.measurable_ofReal.comp hme).mul ((hmD i j).comp measurable_snd)
  have domin (τ x : Position) (i j : Fin 2) : ‖u τ x i j‖ ≤ 3*‖D x i j‖ := by
    change ‖(W τ x : ℂ) * D x i j‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (bound τ x).1]
    exact mul_le_mul_of_nonneg_right (bound τ x).2 (norm_nonneg _)
  have hu (τ : Position) (i j : Fin 2) : Integrable (fun x => u τ x i j) :=
    ((hD i j).norm.const_mul 3).mono' ((hm i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun x => domin τ x i j)
  have hp (i j : Fin 2) : Integrable (fun z : Position × Position => u z.1 z.2 i j) (μ.prod volume) :=
    (((hD i j).norm.comp_snd μ).const_mul 3).mono' (hm i j).aestronglyMeasurable
      (ae_of_all _ fun z => domin z.1 z.2 i j)
  choose v vh ve using fun (i j : Fin 2) => exists_integrable_L1_family (μ := μ) (f := fun τ x => u τ x i j) (hm i j)
    (fun τ => hu τ i j) (hp i j)
  let V := fun τ i j => v i j τ
  have hv : Integrable V μ := Integrable.of_eval (fun i => Integrable.of_eval (vh i))
  have hV (τ : Position) : spinL1Field (V τ) =ᵐ[volume] u τ := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ve i j τ] with x hx
    exact funext fun i => funext (hx i)
  have meanW (x : Position) : ∫ τ, W τ x ∂μ = 1 := latticeTotalWindow_shift_mean hδ hscale hs (R x)
  have bar : spinL1Field (∫ τ, V τ ∂μ) =ᵐ[volume] D := by
    apply spinL1_barycenter_of_pointwise V hv u (ae_of_all _ hV) D hD hp
    filter_upwards with x
    intro i j
    change (∫ τ, (W τ x:ℂ) * D x i j ∂μ) = D x i j
    rw [integral_mul_const,integral_complex_ofReal,meanW]
    simp
  have one : ∀ᵐ τ ∂μ, (∃ Γ, feasible (u τ) Γ) ∧ energy (u τ) ≤ latticeBlockEnergySum ℓ δ η R D τ := by
    filter_upwards [rep,sumE,ae_latticeShift_mem ℓ,hjoint.prod_right_ae] with τ hrep hsum hτ hpair
    let slots (T : Finset LatticeTile) (i : Fin (Fintype.card (Option T))) :=
      ((Fintype.equivFin (Option T)).symm i).map Subtype.val
    let U (T : Finset LatticeTile) := ∑ i, blocks τ (slots T i)
    let e (T : Finset LatticeTile) := energy (blocks τ none) + ∑ p ∈ T, energy (blocks τ (some p))
    have slot_inj (T : Finset LatticeTile) : Function.Injective (slots T) :=
      (Option.map_injective Subtype.val_injective).comp (Fintype.equivFin (Option T)).symm.injective
    have eq_sum (T : Finset LatticeTile) (x : Position)
        (hz : ∀ p ∉ T, latticeWindow ℓ δ η p (R x-τ) = 0) : U T x = u τ x := by
      have hcount := latticeBlock_sum_enum T (fun p => latticeBlock ℓ δ η p (R x-τ)) hz
      simp only [U,Finset.sum_apply,blocks,latticeBlockDensity,← Finset.sum_smul,← Complex.ofReal_sum]
      change (↑(∑ i, latticeBlock ℓ δ η (slots T i) (R x-τ)) : ℂ) • D x = _
      change (∑ i, latticeBlock ℓ δ η (slots T i) (R x-τ)) = _ at hcount
      rw [hcount]
      simp [u,W,latticeTotalWindow,latticeBlock,add_comm]
    have selected (T : Finset LatticeTile) (x : Position) : U T x = u τ x ∨ U T x = 0 := by
      by_cases h : ∀ p ∉ T, latticeWindow ℓ δ η p (R x-τ) = 0
      · exact Or.inl (eq_sum T x h)
      push Not at h
      obtain ⟨p,hp,hx⟩ := h
      right
      simp only [U,Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i _
      have hn : slots T i ≠ some p := by
        intro he
        generalize heq : (Fintype.equivFin (Option T)).symm i = o
        change ((Fintype.equivFin (Option T)).symm i).map Subtype.val = some p at he
        rw [heq] at he
        cases o with
        | none => contradiction
        | some q => exact hp ((Option.some_inj.mp he) ▸ q.property)
      have zero : latticeBlock ℓ δ η (slots T i) (R x-τ) = 0 := by
        by_contra hy
        exact disjoint_left.mp (latticeBlock_pairwise hℓ hδ hs hn) hy hx
      simp [blocks,latticeBlockDensity,zero]
    have cover (x : Position) : ∀ᶠ T in Filter.atTop, U T x = u τ x := by
      obtain ⟨T,hT⟩ := latticeWindow_finite_range hℓ hδ hs ‖x‖
      filter_upwards [Filter.eventually_ge_atTop T] with T' hh
      exact eq_sum T' x fun p hp => hT R τ hτ x le_rfl p (fun hi => hp (hh hi))
    apply coulomb_disjoint_exhaustion hlsc (u τ) U e (tendsto_const_nhds.add hsum.hasSum) (hu τ) _ selected cover
    · convert hpair using 1
      simp [u,r,Matrix.trace_smul]
    · intro T
      obtain ⟨a,b⟩ := coulomb_energy_disjoint_blocks tensor (fun i => blocks τ (slots T i))
        (fun i => hrep _) (fun i j hij => disjoint_lattice_densities hℓ hδ hs R D τ
          (fun h => hij (slot_inj T h))) (fun i j => pair τ _ _)
      refine ⟨a,b.trans_eq ?_⟩
      change (∑ i, energy (blocks τ (((Fintype.equivFin (Option T)).symm i).map Subtype.val))) = _
      rw [(Fintype.equivFin (Option T)).symm.sum_comp (fun k => energy (blocks τ (k.map Subtype.val)))]
      simp only [e,Fintype.sum_option,Option.map_none,Option.map_some,Finset.univ_eq_attach,add_right_inj]
      exact Finset.sum_attach T (fun p => energy (blocks τ (some p)))
    · intro T i j
      change Measurable (fun x => (∑ k, blocks τ (slots T k)) x i j)
      simp only [Finset.sum_apply,Matrix.sum_apply]
      apply Finset.measurable_sum
      intro k _
      exact (Complex.measurable_ofReal.comp ((latticeBlock_measurable ℓ hδ η _).comp
        (R.continuous.measurable.sub_const τ))).mul (hmD i j)
  have hmean (x : Position) : Integrable (fun τ => W τ x) μ :=
    (integrable_const (3:ℝ)).mono' (hme.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun τ => by simpa only [Real.norm_eq_abs,abs_of_nonneg (bound τ x).1] using (bound τ x).2)
  have means : ∀ᵐ x, Integrable (fun τ => W τ x * r x) μ ∧ (∫ τ, W τ x * r x ∂μ) = r x :=
    ae_of_all _ fun x => ⟨(hmean x).mul_const _,by rw [integral_mul_const,meanW,one_mul]⟩
  have hhr := integrable_hartree_of_joint hjoint
  have hupper : ∀ᵐ τ ∂μ, (∃ Γ, feasible (spinL1Field (V τ)) Γ) ∧
      levyLieb (spinL1Field (V τ)) ≤ latticeBlockEnergySum ℓ δ η R D τ + hartree (fun x => W τ x*r x) := by
    filter_upwards [one] with τ h
    obtain ⟨⟨Γ,hΓ⟩,he⟩ := h
    refine ⟨⟨Γ,hΓ.trans (hV τ).symm⟩,?_⟩
    rw [levyLieb_congr_matrix (hV τ)]
    apply sub_le_iff_le_add.mp
    simpa only [energy,u,r,Matrix.trace_smul,smul_eq_mul,Complex.re_ofReal_mul] using he
  obtain ⟨_,_,hll⟩ := levyLieb_barycenter hlsc V _ hv (hE.add hhr) hupper
  simp only [Pi.add_apply] at hll
  rw [integral_add hE hhr,expect_hartree_centered means hjoint hr hdev,levyLieb_congr_matrix bar] at hll
  change levyLieb D - hartree r ≤ _
  simp_rw [sub_mul,one_mul]
  linarith

/-- The shift comparison depends only on the almost-everywhere class of the
density. Choose a jointly Borel representative entry by entry. -/
theorem coulomb_variable_lattice_shifts (tensor : DisjointFockTensorization)
    (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (R : Position ≃ₗᵢ[ℝ] Position)
    (D : Position → SpinMatrix)
    (hD : ∀ i j, Integrable (fun x => D x i j)) :
    let μ := latticeShiftMeasure ℓ
    let W := fun τ x => latticeTotalWindow ℓ δ η (R x-τ)
    let r := fun x => (D x).trace.re
    let blocks := latticeBlockDensity ℓ δ η R D
    (∀ᵐ τ ∂μ, ∀ p, ∃ Γ, feasible (blocks τ p) Γ) →
    (∀ᵐ τ ∂μ, Summable (fun p => energy (blocks τ (some p)))) →
    Integrable (latticeBlockEnergySum ℓ δ η R D) μ →
    Integrable (directKernel r r) pairVolume →
    energy D ≤ (∫ τ, latticeBlockEnergySum ℓ δ η R D τ ∂μ) +
      ∫ τ, hartree (fun x => (W τ x-1)*r x) ∂μ := by
  intro μ W r blocks rep sumE hE hr
  let F : Position → SpinMatrix := fun x i j => (hD i j).1.mk _ x
  have hm (i j) : Measurable (fun x => F x i j) := (hD i j).1.stronglyMeasurable_mk.measurable
  have eqF : D =ᵐ[volume] F := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hD i j).1.ae_eq_mk] with x hx
    exact funext fun i => funext (hx i)
  have eqB (τ p) : blocks τ p =ᵐ[volume] latticeBlockDensity ℓ δ η R F τ p := by
    filter_upwards [eqF] with x hx
    simp [blocks,latticeBlockDensity,hx]
  have eqS : latticeBlockEnergySum ℓ δ η R D = latticeBlockEnergySum ℓ δ η R F := by
    funext τ
    simp only [latticeBlockEnergySum]
    change energy (blocks τ none) + ∑' p, energy (blocks τ (some p)) = _
    simp_rw [fun p => energy_congr (eqB τ p)]
  let r' := fun x => (F x).trace.re
  have eqK : directKernel r r =ᵐ[pairVolume] directKernel r' r' := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae eqF,
      (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae eqF] with z hx hy
    simp [directKernel,r,r',show D z.1 = F z.1 from hx,show D z.2 = F z.2 from hy]
  have eqH (τ) : hartree (fun x => (W τ x-1)*r x) = hartree (fun x => (W τ x-1)*r' x) := by
    apply hartree_congr
    filter_upwards [eqF] with x hx
    simp [r,r',hx]
  rw [energy_congr eqF,eqS]
  simp_rw [eqH]
  apply coulomb_variable_lattice_shifts_of_measurable tensor hlsc hδ hscale hs R F hm
    (fun i j => (hD i j).congr (eqF.mono fun x hx => congrArg (fun A : SpinMatrix => A i j) hx)) _ _ (eqS ▸ hE) (hr.congr eqK)
  · filter_upwards [rep] with τ hτ
    intro p
    obtain ⟨Γ,hΓ⟩ := hτ p
    exact ⟨Γ,hΓ.trans (eqB τ p)⟩
  · filter_upwards [sumE] with τ hτ
    simpa only [fun p => (energy_congr (eqB τ p)).symm] using hτ

set_option maxHeartbeats 1800000 in
/-- The fixed-rotation Coulomb trial over one whole translation cell.
The right side retains the centered direct energy until averaging also
over the rotations and dilations. -/
theorem coulomb_upper_lattice_shifts (tensor : DisjointFockTensorization)
    (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    {ℓ δ : ℝ} (hδ : 0 < δ) (hscale : δ ≤ ℓ/2) {η : Mollifier}
    (hs : Function.support η.kernel ⊆ closedBall 0 (1/100)) (R : Position ≃ₗᵢ[ℝ] Position)
    (D : Position → SpinMatrix) (hmD : ∀ i j, Measurable (fun x => D x i j))
    (hD : ∀ i j, Integrable (fun x => D x i j))
    (hcompact : ∃ B : ℝ, ∀ x, D x ≠ 0 → ‖x‖ ≤ B) :
    let μ := latticeShiftMeasure ℓ
    let W := fun τ x => latticeTotalWindow ℓ δ η (R x-τ)
    let r := fun x => (D x).trace.re
    let blocks := latticeBlockDensity ℓ δ η R D
    (∀ᵐ τ ∂μ, ∀ p, ∃ Γ, feasible (blocks τ p) Γ) →
    Integrable (latticeBlockEnergySum ℓ δ η R D) μ →
    Integrable (directKernel r r) pairVolume →
    energy D ≤ (∫ τ, latticeBlockEnergySum ℓ δ η R D τ ∂μ) +
      ∫ τ, hartree (fun x => (W τ x-1)*r x) ∂μ := by
  classical
  intro μ W r blocks rep hE hr
  have hℓ : 0 < ℓ := by linarith
  obtain ⟨B,hB⟩ := hcompact
  obtain ⟨T,hT⟩ := latticeWindow_finite_range hℓ hδ hs B
  apply coulomb_variable_lattice_shifts_of_measurable tensor hlsc hδ hscale hs R D hmD hD rep _ hE hr
  filter_upwards [ae_latticeShift_mem ℓ] with τ hτ
  apply summable_of_ne_finset_zero (s := T)
  intro p hp
  have zero : blocks τ (some p) = 0 := by
    funext x
    by_cases hx : D x = 0
    · simp [blocks,latticeBlockDensity,hx]
    · simp [blocks,latticeBlockDensity,latticeBlock,hT R τ hτ x (hB x hx) p hp]
  change energy (blocks τ (some p)) = 0
  rw [zero,energy_vacuum]

end TSGA.ManyBody
