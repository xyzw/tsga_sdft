import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Error exponents in the TSGA and LSDA estimates

The localization proof uses the power `p + p / a - 1` of the inverse error
parameter. The general power is the maximum in Theorem 3.3.
A separate estimate improves it under a positive minority-density bound. Under the particle-number rescaling,
`epsilon = N ^ (-scalingExponent p b)` balances the volume and bulk gradient
terms. This file proves the scalar identities involved in these statements.
-/

namespace TSGA

/-- Bulk exponent for arbitrary polarization. -/
def bulkExponent (p θ : ℝ) : ℝ := max (2 * p) ((1 + 3 * θ) * p) - 1

/-- Bulk exponent when the minority density is bounded below by a fixed fraction
of the total density. -/
def polarizedBulkExponent (p θ : ℝ) : ℝ := max (2 * p) ((1 + 3 * θ) * p - 3) - 1

private theorem exponent_of_min {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    p + p / min 1 (p / t) - 1 = max (2 * p) (p + t) - 1 := by
  by_cases h : p ≤ t
  · rw [min_eq_right (by simpa using (div_le_iff₀ ht).2 (by linarith : p ≤ 1 * t)),
        max_eq_right (by linarith)]
    field_simp
  · rw [min_eq_left ((le_div_iff₀ ht).2 (by linarith)), max_eq_left (by linarith)]
    ring

/-- The first choice of Hölder exponent in the proof of the TSGA theorem. -/
theorem bulkExponent_from_holder {p θ : ℝ} (hp : 0 < p) (hθ : 0 < θ) :
    p + p / min 1 (1 / (3 * θ)) - 1 = bulkExponent p θ := by
  have ht : 0 < 3 * θ * p := by positivity
  have hdiv : 1 / (3 * θ) = p / (3 * θ * p) := by field_simp
  rw [hdiv, exponent_of_min hp ht, bulkExponent]
  ring_nf

/-- The second choice of Hölder exponent. The manuscript assumes `2 ≤ θ * p`. -/
theorem polarizedBulkExponent_from_holder {p θ : ℝ} (hp : 0 < p) (hθp : 1 < θ * p) :
    p + p / min 1 (p / (3 * (θ * p - 1))) - 1 = polarizedBulkExponent p θ := by
  have ht : 0 < 3 * (θ * p - 1) := by linarith
  rw [exponent_of_min hp ht, polarizedBulkExponent]
  ring_nf

/-- Both choices of `a` in the local estimate give Young powers in `[1, 2]`,
so the density errors with `m = 4/3` and `m = 5/3` can be integrated against
the sum of the density and its square. -/
theorem youngDensityPower_mem_Icc {p θ a m : ℝ} (hp : 3 < p) (hθp : 2 ≤ θ * p)
    (ha : a = min 1 (1 / (3 * θ)) ∨ a = min 1 (p / (3 * (θ * p - 1))))
    (hm : m ∈ Set.Icc (4 / 3 : ℝ) (5 / 3)) :
    (m - θ * a) * p / (p - a) ∈ Set.Icc 1 2 := by
  have hp' : 0 < p := by linarith
  have hθ : 0 < θ := pos_of_mul_pos_left (by linarith : 0 < θ * p) hp'.le
  have ht : 0 < 3 * (θ * p - 1) := by linarith
  have hcompare : 1 / (3 * θ) ≤ p / (3 * (θ * p - 1)) := by
    apply (div_le_div_iff₀ (by positivity) ht).2
    linarith
  have bounds : 0 < a ∧ a ≤ 1 ∧ a ≤ p / (3 * (θ * p - 1)) := by
    rcases ha with rfl | rfl
    · exact ⟨lt_min (by norm_num) (by positivity), min_le_left ..,
        (min_le_right ..).trans hcompare⟩
    · exact ⟨lt_min (by norm_num) (div_pos hp' ht), min_le_left .., min_le_right ..⟩
  obtain ⟨ha', ha1, hat⟩ := bounds
  have hden : 0 < p - a := by linarith
  have hupper := (le_div_iff₀ ht).1 hat
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.1) hp'.le]
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) hp'.le,
      mul_nonneg (sub_nonneg.mpr hθp) ha'.le]

theorem bulkExponent_eq_two_mul_sub_one_iff {p θ : ℝ} (hp : 0 < p) :
    bulkExponent p θ = 2 * p - 1 ↔ θ ≤ 1 / 3 := by
  rw [bulkExponent, sub_left_inj, max_eq_left_iff, mul_le_mul_iff_left₀ hp]
  constructor <;> intro h <;> linarith

theorem polarizedBulkExponent_eq_two_mul_sub_one_iff (p θ : ℝ) :
    polarizedBulkExponent p θ = 2 * p - 1 ↔ θ * p ≤ 1 + p / 3 := by
  rw [polarizedBulkExponent, sub_left_inj, max_eq_left_iff]
  constructor <;> intro h <;> linarith

/-- The exponent of the small parameter in the particle-number rescaling. -/
noncomputable def scalingExponent (p b : ℝ) : ℝ := p / (3 * (b + 1))

/-- Volume and bulk gradient terms have the same power of the particle number. -/
theorem scaling_balance {p b : ℝ} (hb : b + 1 ≠ 0) :
    1 - scalingExponent p b = 1 - p / 3 + b * scalingExponent p b := by
  unfold scalingExponent
  field_simp
  ring

theorem scalingExponent_of_sharp_bulk {p : ℝ} (hp : 0 < p) :
    scalingExponent p (2 * p - 1) = 1 / 6 := by
  simp only [scalingExponent, sub_add_cancel]
  field_simp
  ring

/-- In particular the volume term has power `5/6` in the sharp regime. -/
theorem scaling_power_of_sharp_bulk {p : ℝ} (hp : 0 < p) :
    1 - scalingExponent p (2 * p - 1) = 5 / 6 := by
  rw [scalingExponent_of_sharp_bulk hp]
  norm_num

/-- The explicit optimization for unrestricted polarization. -/
theorem scalingExponent_bulk {p θ : ℝ} (hp : 0 < p) (hθ : 0 < θ) :
    scalingExponent p (bulkExponent p θ) = min (1 / 6) (1 / (3 + 9 * θ)) := by
  have hd : 0 < 3 + 9 * θ := by linarith
  by_cases h : θ ≤ 1 / 3
  · rw [(bulkExponent_eq_two_mul_sub_one_iff hp).2 h, scalingExponent_of_sharp_bulk hp]
    exact (min_eq_left ((le_div_iff₀ hd).2 (by linarith))).symm
  · have hmax : 2 * p ≤ (1 + 3 * θ) * p :=
      (mul_le_mul_iff_left₀ hp).2 (by linarith)
    rw [bulkExponent, max_eq_right hmax, scalingExponent, sub_add_cancel,
      min_eq_right ((div_le_iff₀ hd).2 (by linarith))]
    have hpos : 0 < 1 + 3 * θ := by linarith
    field_simp
    ring

end TSGA
