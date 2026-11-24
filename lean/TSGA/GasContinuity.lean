import TSGA.HolderRegularity
import TSGA.DensityMeasurability
import TSGA.ErrorDensity

/-! # Joint continuity of the SSW reference energy

Cancelling the cube root of the maximum trace gives a modulus continuous at
the vacuum as well. It gives measurability on an almost-everywhere measurable
matrix field and a continuous wavevector field.
-/

noncomputable section
namespace TSGA.SSW

open MeasureTheory Filter TSGA.Localization
open scoped Topology ComplexOrder

private def densityFactor (r : ℝ) (q : Position) : ℝ :=
  r + r^(4/3:ℝ) + r^(2/3:ℝ)*‖q‖^2

private theorem growth_div_cube_root {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (q : Position) :
    holderGrowth r q*(d/r)^(1/3:ℝ) = densityFactor r q*d^(1/3:ℝ) := by
  have factor : holderGrowth r q = densityFactor r q * r^(1/3:ℝ) := by
    unfold densityFactor holderGrowth
    have h1 : r * r^(1/3:ℝ) = r^(4/3:ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one r]
      rw [← Real.rpow_add hr]
      norm_num
    have h2 : r^(4/3:ℝ)*r^(1/3:ℝ) = r^(5/3:ℝ) := by rw [← Real.rpow_add hr]; norm_num
    have h3 : r^(2/3:ℝ)*r^(1/3:ℝ) = r := by rw [← Real.rpow_add hr]; norm_num
    rw [add_mul, add_mul, mul_right_comm (r^(2/3:ℝ)) (‖q‖^2), h1, h2, h3]
  rw [factor, Real.div_rpow hd hr.le]
  field_simp [(Real.rpow_pos_of_pos hr (1/3:ℝ)).ne']

/-- Joint continuity on the closed cone of physical spin matrices. -/
theorem continuous_ssw_of_holder {E : EnergyFunctional} {η : Mollifier} {K C : ℝ}
    (gas : SSWGasTheorem (referenceEnergies E η)) (rate : FiniteRateTiling E η K)
    (mat : ∀ {A B : SpinMatrix}, A.PosSemidef → B.PosSemidef → ∀ q : Position,
      let r := max A.trace.re B.trace.re
      0 < r → |sswEnergy E η A q-sswEnergy E η B q| ≤
        C*holderGrowth r q*(hilbertSchmidt (A-B)/r)^(1/3:ℝ)) :
    Continuous (fun z : {M : SpinMatrix // M.PosSemidef} × Position => sswEnergy E η z.1.val z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let B := z.1.val
  let q := z.2
  let Ω := {M : SpinMatrix // M.PosSemidef} × Position
  let r (y : Ω) := max y.1.val.trace.re B.trace.re
  let d (y : Ω) := hilbertSchmidt (y.1.val - B)
  let U (y : Ω) := C*densityFactor (r y) y.2*(d y)^(1/3:ℝ) +
    (2*K+1)*(B.trace.re^(7/6:ℝ) + B.trace.re^(4/3:ℝ) + B.trace.re*max ‖y.2‖ ‖q‖)*‖y.2-q‖
  have hmatrix (y : Ω) : |sswEnergy E η y.1.val y.2 - sswEnergy E η B y.2| ≤
      C*densityFactor (r y) y.2*(d y)^(1/3:ℝ) := by
    have ha := RCLike.nonneg_iff.mp y.1.property.trace_nonneg
    have hb := RCLike.nonneg_iff.mp z.1.property.trace_nonneg
    by_cases hr : 0 < r y
    · have h := mat y.1.property z.1.property y.2 hr
      change _ ≤ C*holderGrowth (r y) y.2*(d y/r y)^(1/3:ℝ) at h
      simpa only [mul_assoc, growth_div_cube_root hr (show 0 ≤ d y from Real.sqrt_nonneg _) y.2] using h
    · have hz : r y = 0 := le_antisymm (le_of_not_gt hr) (ha.1.trans (le_max_left _ _))
      have hA := y.1.property.trace_eq_zero_iff.mp (Complex.ext
        (le_antisymm ((le_max_left _ _).trans_eq hz) ha.1) ha.2)
      have hB : B = 0 := z.1.property.trace_eq_zero_iff.mp (Complex.ext
        (le_antisymm ((le_max_right _ _).trans_eq hz) hb.1) hb.2)
      simp only [hz, hA, hB, sub_self, abs_zero, densityFactor, Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0), zero_mul, add_zero, mul_zero, le_refl]
  have hbound (y : Ω) : ‖sswEnergy E η y.1.val y.2 - sswEnergy E η B q‖ ≤ U y :=
    (abs_sub_le _ (sswEnergy E η B y.2) _).trans
      (add_le_add (hmatrix y) (gas.wavevector_lipschitz_psd rate B z.1.property y.2 q))
  have hU : Continuous U := by
    dsimp only [Ω, U, densityFactor, r, d, hilbertSchmidt]
    fun_prop (disch := norm_num)
  have hz : U z = 0 := by
    simp [U, d, B, q, hilbertSchmidt]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (hz ▸ hU.continuousAt)

theorem local_ssw_measurable_of_continuous {E : EnergyFunctional} {η : Mollifier}
    (hc : Continuous (fun z : {M : SpinMatrix // M.PosSemidef} × Position => sswEnergy E η z.1.val z.2))
    {D : Density} {φ : Phase} {p θ : ℝ} {S T : MatrixGradient} (hD : DensityRegular D p θ S T)
    (hφ : φ.Regular p) : AEStronglyMeasurable (localEnergy (referenceEnergies E η) D φ) volume := by
  have hm : AEMeasurable (fun x => (⟨D.matrix x, D.positive x⟩ : {M : SpinMatrix // M.PosSemidef})) volume :=
    hD.aemeasurable_matrix.subtype_mk
  exact (hc.measurable.comp_aemeasurable (hm.prodMk hφ.continuous_grad.aemeasurable)).aestronglyMeasurable

end TSGA.SSW
