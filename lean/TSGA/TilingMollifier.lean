import TSGA.RadialMollifier

/-! # The smoothing kernel used inside the tetrahedral tiling -/

noncomputable section
namespace TSGA.SSW

open MeasureTheory Metric
open scoped ContDiff

/-- A smooth radial unit-mass kernel with square root in H¹ can be chosen at
any prescribed radius. The outer cutoff in the gas limit may use its own kernel. -/
theorem exists_smooth_tiling_mollifier {r : ℝ} (hr : 0 < r) :
    ∃ η : Mollifier, ContDiff ℝ ∞ η.kernel ∧ tsupport η.kernel ⊆ closedBall 0 r := by
  let b : ContDiffBump (0 : ℝ) := ⟨r^2 / 2, r^2, by positivity, by nlinarith [sq_pos_of_pos hr]⟩
  let f := fun x : Position => b (‖x‖ ^ 2)
  have hf : ContDiff ℝ ∞ f := b.contDiff.comp (contDiff_norm_sq ℝ)
  have hs : ∀ x : Position, x ∉ closedBall 0 r → f x = 0 := by
    intro x hx
    have h : r < ‖x‖ := by simpa using hx
    apply b.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
    exact pow_le_pow_left₀ hr.le h.le 2
  have hc := HasCompactSupport.intro' (isCompact_closedBall (0 : Position) r) isClosed_closedBall hs
  have h0 : b 0 = 1 := b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)
  let η := Mollifier.ofAmplitude f (hf.of_le (by simp)) hc (fun x => b.nonneg' _)
    (by simp [f, h0]) (fun x y h => by simp [f, h])
  refine ⟨η, (hf.div_const _).pow 2, closure_minimal ?_ isClosed_closedBall⟩
  intro x hx
  by_contra h
  exact hx (by change (f x / _)^2 = 0; rw [hs x h]; simp)

end TSGA.SSW
