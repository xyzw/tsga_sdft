import TSGA.PhaseLocalization
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # The truncated wavevector modulus

This is the scalar Lipschitz estimate entering the Sobolev product rule
in the large-oscillation argument for Theorem 3.3.
-/

noncomputable section

namespace TSGA.PhaseLocalization

open Set
open scoped NNReal

/-- A Lipschitz coefficient for the truncated speed. -/
def truncationSlope (p δ : ℝ) : ℝ≥0 := (δ ^ (1/p - 1/2)).toNNReal

theorem truncationSlope_rpow {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) :
    ((truncationSlope p δ : ℝ≥0) : ℝ)^p = δ^(1-p/2) := by
  rw [truncationSlope, Real.coe_toNNReal _ (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
  congr 1
  field_simp

/-- On the positive branch `t ≥ √δ`, the derivative decreases as `t` grows.
Clamping the argument at √δ extends this bound across the truncation point. -/
theorem truncatedSpeed_lipschitz {p δ : ℝ} (hp : 2 ≤ p) (hδ : 0 < δ) :
    LipschitzOnWith (truncationSlope p δ) (truncatedSpeed p δ) (Ici 0) := by
  let a := 2/p
  let s := δ^(1/2 : ℝ)
  let L := δ^(1/p-1/2)
  have hp₀ : 0 < p := by linarith
  have ha : 0 ≤ a := div_nonneg (by norm_num) hp₀.le
  have ha₁ : a ≤ 1 := (div_le_one hp₀).2 hp
  have hs : 0 < s := Real.rpow_pos_of_pos hδ _
  have hL : 0 ≤ L := Real.rpow_nonneg hδ.le _
  have hthreshold : s^a = δ^(1/p) := by
    dsimp only [s, a]
    rw [← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hcoef : s^(a-1) = L := by
    dsimp only [s, a, L]
    rw [← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hclamp (t : ℝ) (ht : 0 ≤ t) :
      truncatedSpeed p δ t = (max t s)^a - s^a := by
    change max 0 (t^a - δ^(1/p)) = _
    rw [← hthreshold]
    rcases le_total t s with h | h
    · rw [max_eq_left (sub_nonpos.mpr (Real.rpow_le_rpow ht h ha)), max_eq_right h, sub_self]
    · rw [max_eq_right (sub_nonneg.mpr (Real.rpow_le_rpow hs.le h ha)), max_eq_left h]
  have hdiff : ∀ x ∈ Ici s, DifferentiableAt ℝ (fun t : ℝ => t^a) x :=
    fun _ hx => (Real.hasDerivAt_rpow_const (Or.inl (hs.trans_le hx).ne')).differentiableAt
  have hderiv : ∀ x ∈ Ici s, ‖deriv (fun t : ℝ => t^a) x‖ ≤ L := by
    intro x hx
    have hx' : 0 ≤ x := (hs.trans_le hx).le
    rw [Real.deriv_rpow_const, Real.norm_of_nonneg (mul_nonneg ha (Real.rpow_nonneg hx' _)),
      ← hcoef]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hx' _) ha₁).trans
      (Real.rpow_le_rpow_of_nonpos hs hx (sub_nonpos.mpr ha₁))
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  have h := (convex_Ici s).norm_image_sub_le_of_norm_deriv_le hdiff hderiv
    (le_max_right y s) (le_max_right x s)
  simp only [Real.norm_eq_abs] at h
  rw [Real.dist_eq, hclamp x hx, hclamp y hy, sub_sub_sub_cancel_right, Real.dist_eq,
    truncationSlope, Real.coe_toNNReal _ hL]
  exact h.trans (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs x y s) hL)

end TSGA.PhaseLocalization
