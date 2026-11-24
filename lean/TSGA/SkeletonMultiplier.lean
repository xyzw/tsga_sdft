import TSGA.SSWDomain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The mollifier multiplier in the electrostatic skeleton -/

noncomputable section
namespace TSGA.Skeleton
open MeasureTheory
open scoped InnerProductSpace

private def character (t : ℝ) := Complex.exp ((t : ℂ)*Complex.I)

private theorem char_norm (t : ℝ) : ‖character t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem char_diff (a b : ℝ) : ‖character a-character b‖ ≤ |a-b| := by
  have he : character a-character b = (character (a-b)-1)*character b := by
    rw [sub_mul,one_mul]
    congr 1
    dsimp only [character]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he,norm_mul,char_norm,mul_one]
  simpa only [character,mul_comm Complex.I,Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a-b))

def multiplier (η : SSW.Mollifier) (t : ℝ) (k : Position) : ℂ :=
  ∫ x, η.kernel x • character (-t*⟪k,x⟫_ℝ)

def firstMoment (η : SSW.Mollifier) : ℝ := ∫ x, η.kernel x * ‖x‖

theorem firstMoment_nonneg (η : SSW.Mollifier) : 0 ≤ firstMoment η :=
  integral_nonneg fun x => mul_nonneg (η.nonneg x) (norm_nonneg x)

private theorem firstMoment_integrable (η : SSW.Mollifier) : Integrable (fun x => η.kernel x * ‖x‖) := by
  obtain ⟨R,hR⟩ := η.compact.isBounded.subset_ball (0:Position)
  apply (η.integrable.mul_const R).mono' (η.integrable.aestronglyMeasurable.mul continuous_norm.aestronglyMeasurable)
  filter_upwards with x
  change ‖η.kernel x*‖x‖‖ ≤ η.kernel x*R
  rw [Real.norm_of_nonneg (mul_nonneg (η.nonneg x) (norm_nonneg _))]
  by_cases hx : η.kernel x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp (hR (subset_tsupport _ (Function.mem_support.mpr hx)))).le (η.nonneg x)

private theorem multiplier_integrable (η : SSW.Mollifier) (t : ℝ) (k : Position) :
    Integrable (fun x => η.kernel x • character (-t*⟪k,x⟫_ℝ)) := by
  have hc : Continuous (fun x : Position => character (-t*⟪k,x⟫_ℝ)) := by unfold character; fun_prop
  apply η.integrable.mono' (η.integrable.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  exact ae_of_all _ fun x => by simp [char_norm,Real.norm_of_nonneg (η.nonneg x)]

theorem multiplier_norm (η : SSW.Mollifier) (t : ℝ) (k : Position) : ‖multiplier η t k‖ ≤ 1 := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp [char_norm,Real.norm_of_nonneg (η.nonneg _),η.mass]

/-- The change of smoothing width costs at most its first moment times the
frequency. This estimate holds for every frequency. -/
theorem multiplier_difference (η : SSW.Mollifier) (a b : ℝ) (k : Position) :
    ‖multiplier η a k - multiplier η b k‖ ≤ |a-b| *‖k‖*firstMoment η := by
  rw [multiplier,multiplier,← integral_sub (multiplier_integrable η a k) (multiplier_integrable η b k)]
  apply (norm_integral_le_integral_norm _).trans
  have hi := (firstMoment_integrable η).const_mul (|a-b| *‖k‖)
  have h := integral_mono_of_nonneg (μ := volume) (ae_of_all _ fun x =>
    norm_nonneg (η.kernel x • character (-a*⟪k,x⟫_ℝ)-η.kernel x • character (-b*⟪k,x⟫_ℝ))) hi
    (ae_of_all _ fun x => by
      dsimp only
      rw [← smul_sub,norm_smul,Real.norm_of_nonneg (η.nonneg x)]
      have hd := char_diff (-a*⟪k,x⟫_ℝ) (-b*⟪k,x⟫_ℝ)
      rw [show -a*⟪k,x⟫_ℝ- -b*⟪k,x⟫_ℝ = -(a-b)*⟪k,x⟫_ℝ by ring, abs_mul,abs_neg] at hd
      have hq := hd.trans (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm k x) (abs_nonneg _))
      exact (mul_le_mul_of_nonneg_left hq (η.nonneg x)).trans_eq (by ring))
  simpa only [integral_const_mul,firstMoment] using h

end TSGA.Skeleton
