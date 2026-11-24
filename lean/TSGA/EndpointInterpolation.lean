import TSGA.Exponents
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Slope

/-! # Interpolation of the uniform-gas endpoint exponent -/

namespace TSGA

/-- The bulk exponent for a minority-occupation modulus of order α. -/
noncomputable def endpointBulkExponent (p θ α : ℝ) : ℝ :=
  max (max (2*p) ((1+θ/α)*p)) ((1+3*θ)*p-3) - 1

theorem endpointBulkExponent_from_holder {p θ α : ℝ} (hp : 0 < p) (hθ : 0 < θ)
    (hα : 0 < α) (hpθ : 1 < θ*p) :
    p+p/(min (min 1 (α/θ)) (p/(3*(θ*p-1))))-1 = endpointBulkExponent p θ α := by
  have divmin (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : p/min a b = max (p/a) (p/b) := by
    rcases le_total a b with h | h
    · rw [min_eq_left h,max_eq_left (div_le_div_of_nonneg_left hp.le ha h)]
    · rw [min_eq_right h,max_eq_right (div_le_div_of_nonneg_left hp.le hb h)]
  have hd : 0 < 3*(θ*p-1) := by linarith
  rw [divmin _ _ (lt_min zero_lt_one (div_pos hα hθ)) (div_pos hp hd),divmin _ _ zero_lt_one (div_pos hα hθ),
    div_one,div_div_eq_mul_div,div_div_eq_mul_div,mul_div_cancel_left₀ _ hp.ne',endpointBulkExponent,
    add_max,add_max]
  rw [show p+p=2*p by ring,show p+p*θ/α=(1+θ/α)*p by ring,
    show p+3*(θ*p-1)=(1+3*θ)*p-3 by ring]

theorem endpointBulkExponent_one_third (p θ : ℝ) :
    endpointBulkExponent p θ (1/3) = bulkExponent p θ := by
  unfold endpointBulkExponent bulkExponent
  rw [show θ/(1/3:ℝ) = 3*θ by ring, max_eq_left]
  exact (sub_le_self _ (by norm_num : (0:ℝ) ≤ 3)).trans (le_max_right ..)

theorem endpointBulkExponent_one {p θ : ℝ} (hp : 0 ≤ p) (hθ : θ ≤ 1) :
    endpointBulkExponent p θ 1 = polarizedBulkExponent p θ := by
  unfold endpointBulkExponent polarizedBulkExponent
  rw [div_one,max_eq_left (show (1+θ)*p ≤ 2*p from mul_le_mul_of_nonneg_right (by linarith) hp)]

/-- A symmetric convex energy with a power bound at full polarization
is Lipschitz in the α-power of the minority fraction, including zero. -/
theorem convex_minority_power {F : ℝ → ℝ} {α H : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (hH : 0 ≤ H) (conv : ConvexOn ℝ (Set.Icc 0 1) F)
    (symm : ∀ t ∈ Set.Icc (0:ℝ) 1, F (1-t) = F t)
    (endpoint : ∀ t ∈ Set.Icc (0:ℝ) (1/2), F 0-F t ≤ H*t^α)
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) :
    |F t-F s| ≤ (H/α)*|t^α-s^α| := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm (F t),abs_sub_comm (t^α)]
    exact this ht hs (le_of_not_ge hst)
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have tpos := hs.1.trans_lt hst
  have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1,by linarith [hs.2]⟩
  have ht1 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  have far : 1-s ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hs1.2],by linarith [hs.1]⟩
  have hdec : F t ≤ F s := by
    have sec := conv.secant_mono_aux1 hs1 far hst (by linarith [ht.2] : t < 1-s)
    rw [symm s hs1] at sec
    by_contra! bad
    nlinarith only [sec,mul_pos (show 0 < 1-s-s by linarith [ht.2]) (sub_pos.mpr bad)]
  rw [abs_of_nonpos (sub_nonpos.mpr hdec),abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hs.1 hst.le hα.le))]
  have sec : t*(F s-F t) ≤ (t-s)*(H*t^α) := by
    rcases hs.1.eq_or_lt with h | h
    · rw [←h,sub_zero]
      exact mul_le_mul_of_nonneg_left (endpoint t ht) ht.1
    have slope := conv.secant_mono_aux1 (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) ht1 h hst
    nlinarith only [slope,mul_le_mul_of_nonneg_left (endpoint t ht) (sub_nonneg.mpr hst.le)]
  have tangent := rpow_one_add_le_one_add_mul_self (by linarith [div_nonneg hs.1 tpos.le] : -1 ≤ s/t-1) hα.le hα'
  rw [show 1+(s/t-1) = s/t by ring,Real.div_rpow hs.1 tpos.le] at tangent
  have powpos := Real.rpow_pos_of_pos tpos α
  have htan := (div_le_iff₀ powpos).mp tangent
  have bounded : α*((t-s)*t^α) ≤ t*(t^α-s^α) := by
    have m := mul_le_mul_of_nonneg_left htan tpos.le
    field_simp [tpos.ne'] at m
    nlinarith only [m]
  have hfin : (α*t)*(F s-F t) ≤ (α*t)*((H/α)*(t^α-s^α)) := by
    calc
      _ = α*(t*(F s-F t)) := by ring
      _ ≤ α*((t-s)*(H*t^α)) := mul_le_mul_of_nonneg_left sec hα.le
      _ = H*(α*((t-s)*t^α)) := by ring
      _ ≤ H*(t*(t^α-s^α)) := mul_le_mul_of_nonneg_left bounded hH
      _ = _ := by field_simp
  linarith only [(mul_le_mul_iff_right₀ (mul_pos hα tpos)).mp hfin]

end TSGA
