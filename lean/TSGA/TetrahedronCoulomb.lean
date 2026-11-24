import TSGA.SSWLocalization
import TSGA.LevyLieb
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Coulomb energy of the smoothed reference tetrahedron -/

noncomputable section
namespace TSGA.SSW

open MeasureTheory Metric Set
open scoped Convolution ComplexOrder

theorem tetrahedron_open (ℓ : ℝ) : IsOpen (tetrahedron ℓ) := by
  have hc (i : Fin 3) : Continuous (fun x : Position => x i) := by fun_prop
  exact (isOpen_lt (hc 2).abs ((hc 1).add continuous_const)).inter
    ((isOpen_lt ((hc 1).add continuous_const) ((hc 0).add continuous_const)).inter
      (isOpen_lt ((hc 0).add continuous_const) continuous_const))

theorem tetrahedron_subset {ℓ : ℝ} (he : 0 < ℓ) :
    tetrahedron ℓ ⊆ closedBall (0 : Position) (2*ℓ) := by
  intro x hx
  obtain ⟨h2,h1,h0⟩ := hx
  have ha := abs_nonneg (x 2)
  have hb := neg_abs_le (x 2)
  have hc := le_abs_self (x 2)
  have hs (i : Fin 3) : (x i)^2 ≤ ℓ^2 := by
    apply sq_le_sq' <;> fin_cases i <;> dsimp <;> linarith
  rw [mem_closedBall, dist_zero_right]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith only [hs 0, hs 1, hs 2, sq_nonneg ℓ]

theorem tetrahedron_volume_pos {ℓ : ℝ} (he : 0 < ℓ) : 0 < regionVolume (tetrahedron ℓ) := by
  have hn : (0 : Position) ∈ tetrahedron ℓ := by
    change |(0:ℝ)| < 0+ℓ/4 ∧ 0+ℓ/4 < 0+3*ℓ/8 ∧ 0+3*ℓ/8 < ℓ/2
    rw [abs_zero]
    exact ⟨by linarith, by linarith, by linarith⟩
  exact ENNReal.toReal_pos ((tetrahedron_open ℓ).measure_pos volume ⟨0,hn⟩).ne'
    (isBounded_closedBall.subset (tetrahedron_subset he)).measure_lt_top.ne

private theorem tetrahedron_volume_le {ℓ : ℝ} (he : 0 < ℓ) :
    regionVolume (tetrahedron ℓ) ≤ (2*ℓ)^3 * volume.real (ball (0 : Position) 1) := by
  apply (measureReal_mono (μ := volume) (tetrahedron_subset he) isBounded_closedBall.measure_lt_top.ne).trans_eq
  simpa [finrank_euclideanSpace] using
    Measure.addHaar_real_closedBall volume (0:Position) (show 0 ≤ 2*ℓ by positivity)

theorem tile_cutoff_mass (η : Mollifier) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) :
    ∫ x, smoothedIndicator (tetrahedron ℓ) η δ x = regionVolume (tetrahedron ℓ) := by
  classical
  have hb := isBounded_closedBall.subset (tetrahedron_subset he)
  have hi : Integrable ((tetrahedron ℓ).indicator fun _ => (1:ℝ)) :=
    (integrable_indicator_iff (tetrahedron_open ℓ).measurableSet).2
      (integrableOn_const hb.measure_lt_top.ne)
  rw [smoothedIndicator, integral_convolution _ hi (η.scaled_integrable hd), η.scaled_mass hd,
    integral_indicator (tetrahedron_open ℓ).measurableSet]
  simp [regionVolume]

theorem smoothedIndicator_bounds (Ω : Set Position) (η : Mollifier) {δ : ℝ} (hd : 0 < δ) (x : Position) :
    smoothedIndicator Ω η δ x ∈ Icc 0 1 := by
  classical
  let K := η.scaled δ
  let f := Ω.indicator (fun _ => (1:ℝ))
  have hK (y) : 0 ≤ K y := mul_nonneg (inv_nonneg.mpr (pow_nonneg hd.le _)) (η.nonneg _)
  have hf (y) : f y ∈ Icc 0 1 := by by_cases h : y ∈ Ω <;> simp [f,h]
  have hsym (y : Position) : K (x-y) = K (y-x) := by
    dsimp only [K, Mollifier.scaled]
    congr 1
    apply η.radial
    rw [norm_smul, norm_smul, norm_sub_rev x y]
  have hi := (η.scaled_integrable hd).comp_sub_right x
  change 0 ≤ (∫ y, f y * K (x-y)) ∧ (∫ y, f y * K (x-y)) ≤ 1
  simp_rw [hsym]
  have hpos (y) := mul_nonneg (hf y).1 (hK (y-x))
  refine ⟨integral_nonneg hpos, (integral_mono_of_nonneg (ae_of_all _ hpos) hi
    (ae_of_all _ fun y => mul_le_of_le_one_left (hK (y-x)) (hf y).2)).trans_eq ?_⟩
  exact (integral_sub_right_eq_self K x).trans (η.scaled_mass hd)

theorem tile_charge_moment (η : Mollifier) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ)
    {A : SpinMatrix} (hA : A.PosSemidef) (q : Position) :
    (∫ x, ((cutoffSpiral (smoothedIndicator (tetrahedron ℓ) η δ) A q x).trace.re)^(4/3:ℝ)) ≤
      A.trace.re^(4/3:ℝ) * regionVolume (tetrahedron ℓ) := by
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  have hf := smoothedIndicator_bounds (tetrahedron ℓ) η hd
  have hr : 0 ≤ A.trace.re := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hm : ∫ y, f y = regionVolume (tetrahedron ℓ) := tile_cutoff_mass η he hd
  have hi : Integrable f := Integrable.of_integral_ne_zero (hm.trans_ne (tetrahedron_volume_pos he).ne')
  have hx (x) : (cutoffSpiral f A q x).trace.re = f x * A.trace.re := by
    simp [cutoffSpiral, Matrix.trace_smul]
  change (∫ x, ((cutoffSpiral f A q x).trace.re)^(4/3:ℝ)) ≤ _
  simp_rw [hx]
  have h := integral_mono_of_nonneg (μ := volume)
    (ae_of_all _ fun x => Real.rpow_nonneg (mul_nonneg (hf x).1 hr) (4/3:ℝ))
    (hi.mul_const (A.trace.re^(4/3:ℝ))) (ae_of_all _ fun x => by
      dsimp only
      rw [Real.mul_rpow (hf x).1 hr]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_le_one
        (hf x).1 (hf x).2 (by norm_num)) (Real.rpow_nonneg hr _))
  rw [integral_mul_const, hm] at h
  exact h.trans_eq (mul_comm ..)

private def nearKernel (ℓ : ℝ) := (ball (0 : Position) ℓ).indicator (fun y => ‖y‖⁻¹)

private theorem nearKernel_integrable (ℓ : ℝ) : Integrable (nearKernel ℓ) := by
  apply (integrable_indicator_iff measurableSet_ball).2
  apply integrableOn_ball_of_norm_le_rpow (α := 1) (C := 1)
    (by simp [finrank_euclideanSpace]) (by simp [finrank_euclideanSpace])
  · exact ae_of_all _ fun y => by simp [Real.rpow_neg_one]
  · exact continuous_norm.measurable.inv.aestronglyMeasurable

private theorem nearKernel_mass {ℓ : ℝ} (he : 0 < ℓ) :
    ∫ y, nearKernel ℓ y = ℓ^2 * ∫ y, nearKernel 1 y := by
  have h (y : Position) : nearKernel ℓ y = ℓ⁻¹ * nearKernel 1 (ℓ⁻¹ • y) := by
    have hball : ℓ⁻¹ • y ∈ ball (0 : Position) 1 ↔ y ∈ ball (0 : Position) ℓ := by
      simp [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos he,
        inv_mul_eq_div, div_lt_one he]
    by_cases hy : y ∈ ball (0 : Position) ℓ
    · simp [nearKernel, hy, hball.mpr hy, norm_smul, Real.norm_eq_abs, abs_of_pos he, mul_comm, he.ne']
    · simp [nearKernel, hy, mt hball.mp hy]
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ he.le]
  simp [finrank_euclideanSpace, smul_eq_mul, he.ne', ← mul_assoc, pow_succ]

/-- A universal constant for the direct cost, independent of the mollifier. -/
def tetrahedronDirectConstant : ℝ :=
  (∫ y, nearKernel 1 y) + 8 * volume.real (ball (0:Position) 1)

theorem tetrahedronDirectConstant_nonneg : 0 ≤ tetrahedronDirectConstant := by
  apply add_nonneg
  · exact integral_nonneg (fun y => indicator_nonneg (fun z _ => inv_nonneg.mpr (norm_nonneg z)) y)
  · positivity

/-- Splitting the Coulomb kernel at the tile length controls the direct energy
using only the cutoff's unit height and its mass. -/
theorem tile_hartree_bound (η : Mollifier) {ℓ δ : ℝ} (he : 0 < ℓ) (hd : 0 < δ) :
    ManyBody.hartree (smoothedIndicator (tetrahedron ℓ) η δ) / regionVolume (tetrahedron ℓ)
      ≤ tetrahedronDirectConstant * ℓ^2 := by
  let f := smoothedIndicator (tetrahedron ℓ) η δ
  let V := regionVolume (tetrahedron ℓ)
  have hV : 0 < V := tetrahedron_volume_pos he
  have hm : ∫ y, f y = V := tile_cutoff_mass η he hd
  have hfi : Integrable f := Integrable.of_integral_ne_zero (hm.trans_ne hV.ne')
  have hf := smoothedIndicator_bounds (tetrahedron ℓ) η hd
  let c := tetrahedronDirectConstant
  have hpos : 0 ≤ c*ℓ^2 := mul_nonneg tetrahedronDirectConstant_nonneg (sq_nonneg _)
  have hpot (x : Position) : (∫ y, f y / ‖x-y‖) ≤ c*ℓ^2 := by
    have hpt (y : Position) : f y / ‖x-y‖ ≤ nearKernel ℓ (y-x) + f y/ℓ := by
      rw [norm_sub_rev x y]
      by_cases hz : y-x ∈ ball (0:Position) ℓ
      · rw [nearKernel, indicator_of_mem hz]
        apply le_add_of_le_of_nonneg _ (div_nonneg (hf y).1 he.le)
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right (hf y).2 (inv_nonneg.mpr (norm_nonneg (y-x)))
      · rw [nearKernel, indicator_of_notMem hz, zero_add]
        exact div_le_div_of_nonneg_left (hf y).1 he (le_of_not_gt (fun hn => hz (mem_ball_zero_iff.mpr hn)))
    apply (integral_mono_of_nonneg (ae_of_all _ fun y => div_nonneg (hf y).1 (norm_nonneg _))
      (((nearKernel_integrable ℓ).comp_sub_right x).add (hfi.div_const ℓ)) (ae_of_all _ hpt)).trans
    change (∫ y, nearKernel ℓ (y-x) + f y/ℓ) ≤ c*ℓ^2
    rw [integral_add ((nearKernel_integrable ℓ).comp_sub_right x) (hfi.div_const ℓ),
      integral_sub_right_eq_self, integral_div, hm, nearKernel_mass he]
    have hvol : V / ℓ ≤ 8 * volume.real (ball (0:Position) 1) * ℓ^2 := by
      apply (div_le_iff₀ he).2
      exact (tetrahedron_volume_le he).trans_eq (by ring)
    dsimp only [c,tetrahedronDirectConstant]
    linarith only [hvol]
  have hout := integral_mono_of_nonneg (μ := volume)
    (ae_of_all _ fun x => mul_nonneg (hf x).1 (integral_nonneg fun y => div_nonneg (hf y).1 (norm_nonneg (x-y))))
    (hfi.mul_const (c*ℓ^2)) (ae_of_all _ fun x => mul_le_mul_of_nonneg_left (hpot x) (hf x).1)
  rw [integral_mul_const, hm] at hout
  change ((∫ x, ∫ y, f x*f y/‖x-y‖)/2)/V ≤ _
  simp_rw [mul_div_assoc, integral_const_mul]
  apply (div_le_iff₀ hV).2
  linarith only [hout, mul_nonneg hV.le hpos]

end TSGA.SSW
