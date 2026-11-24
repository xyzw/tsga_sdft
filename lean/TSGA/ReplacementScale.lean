import TSGA.BulkLocalization

/-! # The matrix replacement cost at the localization scale

The matrix comparison contributes the power `p+s` from `eq:def_s`.
Young interpolation can increase this power in the general polarization
regime. The global-root proof applies the matrix comparison at θ = 2/p.
-/

namespace TSGA.BulkRegime

/-- The inverse power of δ in the finite replacement bound at scale ℓ = δ⁻¹. -/
noncomputable def replacementExponent (mode : BulkRegime) (p θ : ℝ) : ℝ :=
  match mode with
  | .general | .minority => p + max p (3 * θ * p - 3) - 1
  | .globalRoot => 2 * p - 1

/-- For the minority-density estimate the replacement and bulk powers agree. -/
theorem nativeReplacement_eq_polarized (p θ : ℝ) :
    p + max p (3 * θ * p - 3) - 1 = polarizedBulkExponent p θ := by
  unfold polarizedBulkExponent
  rcases le_total p (3 * θ * p - 3) with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith : 2 * p ≤ (1 + 3 * θ) * p - 3)]
    ring
  · rw [max_eq_left h, max_eq_left (by nlinarith : (1 + 3 * θ) * p - 3 ≤ 2 * p)]
    ring

/-- The native finite comparison at the sharp endpoint has exponent 2p−1. -/
theorem nativeReplacement_at_two_div {p : ℝ} (hp : 3 < p) :
    p + max p (3 * (2 / p) * p - 3) - 1 = 2 * p - 1 := by
  have hp' : 0 < p := by linarith
  have heq : 3 * (2 / p) * p - 3 = 3 := by field_simp; ring
  rw [heq, max_eq_left hp.le]
  ring

theorem replacementExponent_le (mode : BulkRegime) (p θ : ℝ) :
    mode.replacementExponent p θ ≤ mode.exponent p θ := by
  cases mode with
  | general =>
    change p + max p (3 * θ * p - 3) - 1 ≤ bulkExponent p θ
    rw [nativeReplacement_eq_polarized]
    unfold polarizedBulkExponent bulkExponent
    exact sub_le_sub_right (max_le_max_left _ (by linarith)) _
  | minority => exact (nativeReplacement_eq_polarized p θ).le
  | globalRoot => rfl

/-- For `0 < δ ≤ 1` the cost with the native replacement exponent can be
absorbed using the bulk exponent chosen for the theorem. -/
theorem replacement_cost_le (mode : BulkRegime) (p θ : ℝ) {δ X : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hX : 0 ≤ X) :
    X / δ ^ (mode.replacementExponent p θ) ≤ X / δ ^ (mode.exponent p θ) := by
  exact div_le_div_of_nonneg_left hX (Real.rpow_pos_of_pos hδ _)
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (mode.replacementExponent_le p θ))

end TSGA.BulkRegime
