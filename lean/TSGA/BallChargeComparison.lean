import TSGA.SmallBallMatrices

/-! # Charge comparability on balls of small matrix-power oscillation -/

namespace TSGA.ManyBody

open Metric TSGA.Localization

/-- Part (iii) of `lem:oscillation`. If the θ-power oscillates by at most
θ/4 times the θ-power of the maximum charge, every charge on the closed
ball is at least half that maximum. -/
theorem charge_ge_half_of_small_power_oscillation {N : Density} {c z : Position} {R θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 1) (hz : z ∈ closedBall c R)
    (peak : IsMaxOn N.charge (closedBall c R) z)
    (small : ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      hilbertSchmidt (N.power θ x - N.power θ y) ≤ (θ/4) * (N.charge z)^θ)
    (x : Position) (hx : x ∈ closedBall c R) : N.charge z / 2 ≤ N.charge x := by
  let r := N.charge z
  have hr : 0 ≤ r := N.charge_nonneg z
  have scale : r^(1-θ) * r^θ = r := by
    rw [← Real.rpow_add_of_nonneg hr (sub_nonneg.mpr hθ') hθ.le, sub_add_cancel, Real.rpow_one]
  have matrixBound : hilbertSchmidt (N.matrix z - N.matrix x) ≤ r/4 := calc
    _ = hilbertSchmidt (N.power 1 z - N.power 1 x) := by simp only [density_power_one]
    _ ≤ (1/θ * r^(1-θ)) * hilbertSchmidt (N.power θ z - N.power θ x) :=
      matrix_power_oscillation (N.positive z) (N.positive x) hθ hθ' hr le_rfl
        (isMaxOn_iff.mp peak x hx)
    _ ≤ (1/θ * r^(1-θ)) * ((θ/4)*r^θ) :=
      mul_le_mul_of_nonneg_left (small z hz x hx)
        (mul_nonneg (one_div_nonneg.mpr hθ.le) (Real.rpow_nonneg hr _))
    _ = (r^(1-θ) * r^θ)/4 := by field_simp [hθ.ne']
    _ = r/4 := by rw [scale]
  have traceBound := SSW.abs_trace_re_le_hilbertSchmidt (N.matrix z - N.matrix x)
  rw [Matrix.trace_sub, Complex.sub_re] at traceBound
  change |r - N.charge x| ≤ _ at traceBound
  change r/2 ≤ _
  linarith only [(abs_le.mp traceBound).2, matrixBound]

end TSGA.ManyBody
