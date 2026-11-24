import TSGA.SSWDomain
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # A radial smoothing kernel for the SSW limit

Squaring a smooth radial amplitude before normalizing gives a unit-mass
kernel whose square root has finite kinetic energy, including at its boundary.
-/

noncomputable section

namespace TSGA.SSW

open MeasureTheory

private theorem weak_partial_smooth (f : Position → ℝ) (h : ContDiff ℝ 1 f) (i : Fin 3) :
    WeakPartialOn Set.univ i f (fun x => fderiv ℝ f x (PiLp.single 2 i 1)) := by
  let e : Position := PiLp.single 2 i 1
  have hd := (h.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := e))
  refine ⟨locallyIntegrableOn_univ.mpr h.continuous.locallyIntegrable,
    locallyIntegrableOn_univ.mpr hd.locallyIntegrable, ?_⟩
  intro ψ hψ hc _
  simp only [Measure.restrict_univ]
  have hw := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (v := e)
    (h.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ e))
    (hd.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc)
    (h.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc)
    (fun x _ => hψ.differentiable (by simp) x) (fun x _ => h.differentiable (by norm_num) x)
  rw [hw, neg_neg]

/-- Use the square of a nonzero, nonnegative radial amplitude. -/
def Mollifier.ofAmplitude (f : Position → ℝ) (hd : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hp : ∀ x, 0 ≤ f x) (h0 : f 0 ≠ 0) (hr : ∀ x y, ‖x‖ = ‖y‖ → f x = f y) : Mollifier := by
  let A := ∫ x, f x ^ 2
  have hsq : HasCompactSupport (fun x => f x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hi := (hd.continuous.pow 2).integrable_of_hasCompactSupport hsq (μ := volume)
  have hA : 0 < A := integral_pos_of_integrable_nonneg_nonzero (x := (0 : Position))
    (hd.continuous.pow 2) hi (fun x => sq_nonneg _) (pow_ne_zero _ h0)
  let g := fun x => f x / √A
  have hg : ContDiff ℝ 1 g := hd.div_const _
  have hgc : HasCompactSupport g := hc.comp_left (g := fun t : ℝ => t / √A) (by simp)
  have hg0 (x : Position) : 0 ≤ g x := div_nonneg (hp x) (Real.sqrt_nonneg _)
  have hgs : HasCompactSupport (fun x => g x ^ 2) :=
    hgc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  refine ⟨fun x => g x ^ 2, fun x y hxy => by simp [g, hr x y hxy],
    fun x => sq_nonneg _, hgs, (hg.continuous.pow 2).integrable_of_hasCompactSupport hgs, ?_, ?_⟩
  · simp only [g, div_pow, Real.sq_sqrt hA.le, integral_div]
    exact div_self hA.ne'
  · let pack (L : Position →L[ℝ] ℝ) : Position := WithLp.toLp 2 fun i => L (PiLp.single 2 i 1)
    have hpcont : Continuous pack := (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun _ => continuous_id.clm_apply continuous_const)
    have hpc : HasCompactSupport (fun x => pack (fderiv ℝ g x)) :=
      (hgc.fderiv ℝ).comp_left (g := pack) (by ext i; rfl)
    refine ⟨fun x => pack (fderiv ℝ g x), ?_, (hpcont.comp (hg.continuous_fderiv (by norm_num))).memLp_of_hasCompactSupport hpc⟩
    intro i
    simpa only [Real.sqrt_sq (hg0 _)] using weak_partial_smooth g hg i

/-- A concrete radial kernel supported in the closed unit ball. -/
def unitBallMollifier : Mollifier := by
  let b : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let f := fun x : Position => b (‖x‖ ^ 2)
  have h0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  apply Mollifier.ofAmplitude f (b.contDiff.comp (contDiff_norm_sq ℝ)) _ (fun x => b.nonneg' _)
    (by simp [f, h0]) (fun x y h => by simp [f, h])
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Position) 1) Metric.isClosed_closedBall
  intro x hx
  have h : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  apply b.zero_of_le_dist
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
  change 1 ≤ ‖x‖^2
  nlinarith

end TSGA.SSW
