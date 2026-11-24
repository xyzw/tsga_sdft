import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic.Linarith

/-! # Counting interior spiral tiles in a direction average

The interior fraction can vary with orientation and can be correlated with
the tile energy. A lower bound on the energy gives bounds on both sides of
the integral without requiring a pointwise upper bound on the energy.
-/

namespace TSGA.SSW

open MeasureTheory

private theorem average_mono {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hle : f ≤ᵐ[μ] g) :
    (⨍ x, f x ∂μ) ≤ ⨍ x, g x ∂μ := by
  rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hle) (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- If at most a fraction `γ` of tiles meets the boundary at each orientation
and every tile energy is at least `-a`, compare the weighted interior energy
with the full direction average. The same measure normalizes all three averages. -/
theorem interior_average_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [NeZero μ] {T w : α → ℝ} {γ a : ℝ}
    (hT : Integrable T μ) (hw : AEStronglyMeasurable w μ) (ha : 0 ≤ a)
    (hfrac : ∀ᵐ ω ∂μ, 0 ≤ w ω ∧ 1 - γ ≤ w ω ∧ w ω ≤ 1)
    (hfloor : ∀ᵐ ω ∂μ, -a ≤ T ω) :
    ((⨍ ω, T ω ∂μ) - γ * ((⨍ ω, T ω ∂μ) + a) ≤ ⨍ ω, w ω * T ω ∂μ) ∧
      ((⨍ ω, w ω * T ω ∂μ) ≤ (⨍ ω, T ω ∂μ) + γ * a) := by
  have hwT := hT.bdd_mul hw (c := 1)
    (hfrac.mono fun ω h => by simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.2)
  have hsum : Integrable (fun ω => T ω + a) μ := hT.add (integrable_const a)
  have hlo : (fun ω => T ω - γ * (T ω + a)) ≤ᵐ[μ] (fun ω => w ω * T ω) := by
    filter_upwards [hfrac, hfloor] with ω h hTω
    have hp : 0 ≤ T ω + a := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2.1) hp, mul_nonneg (sub_nonneg.mpr h.2.2) ha]
  have hhi : (fun ω => w ω * T ω) ≤ᵐ[μ] (fun ω => T ω + γ * a) := by
    filter_upwards [hfrac, hfloor] with ω h hTω
    have hp : 0 ≤ T ω + a := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2.2) hp, mul_nonneg (sub_nonneg.mpr h.2.1) ha]
  constructor
  · have hl := average_mono (hT.sub (hsum.const_mul γ)) hwT hlo
    simpa only [Pi.sub_apply, average_fun_sub hT (hsum.const_mul γ), average_const_mul,
      average_fun_add hT (integrable_const a), average_const] using hl
  · have hu := average_mono hwT (hT.add (integrable_const (γ * a))) hhi
    simpa only [Pi.add_apply, average_fun_add hT (integrable_const (γ * a)), average_const] using hu

end TSGA.SSW
