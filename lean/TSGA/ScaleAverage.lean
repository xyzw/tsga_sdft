import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! # The dilation average in the SSW upper localization estimate -/

namespace TSGA.SSW

open Filter MeasureTheory Set
open scoped Topology

noncomputable def scaleInterval : Set ℝ := Icc (1 / 2) (3 / 2)

noncomputable def scaleWeight (t : ℝ) : ℝ := (t ^ 4)⁻¹

private theorem weight_integrable : IntegrableOn scaleWeight scaleInterval := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply (continuousOn_id.pow 4).inv₀
  intro t ht
  have ht' : (1 / 2 : ℝ) ≤ t := ht.1
  exact pow_ne_zero _ (by linarith : t ≠ 0)

private theorem weight_mass_pos : 0 < ∫ t in scaleInterval, scaleWeight t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ weight_integrable).2
  · have hs : scaleInterval ⊆ Function.support scaleWeight := by
      intro t ht
      have ht' : (1 / 2 : ℝ) ≤ t := ht.1
      exact inv_ne_zero (pow_ne_zero _ (by linarith : t ≠ 0))
    rw [inter_eq_right.mpr hs, scaleInterval, Real.volume_Icc]
    norm_num
  · exact ae_of_all _ (fun t => inv_nonneg.mpr (by positivity : 0 ≤ t ^ 4))

/-- The average with probability density proportional to `t⁻⁴` on [1/2, 3/2]. -/
noncomputable def scaleAverage (f : ℝ → ℝ) : ℝ :=
  (∫ t in scaleInterval, f t * scaleWeight t) / (∫ t in scaleInterval, scaleWeight t)

/-- The only convergence required of the tile function is at each fixed smoothing
width. Dominated convergence handles the integral in which width and length both
depend on `t`. -/
theorem scaleAverage_tendsto {tile : ℝ → ℝ → ℝ} {limit : ℝ} {length : ℕ → ℝ}
    (hlength : Tendsto length atTop atTop)
    (htile : ∀ δ : ℝ, 0 < δ → Tendsto (fun ℓ => tile ℓ δ) atTop (𝓝 limit))
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable
      (fun t => tile (t * (length n - 1)) t) (volume.restrict scaleInterval))
    (hbound : ∃ B : ℝ, ∀ ℓ ≥ 1, ∀ t ∈ scaleInterval, |tile ℓ t| ≤ B) :
    Tendsto (fun n => scaleAverage (fun t => tile (t * (length n - 1)) t)) atTop (𝓝 limit) := by
  obtain ⟨B, hB⟩ := hbound
  have hlarge : ∀ᶠ n in atTop, (3 : ℝ) ≤ length n := hlength.eventually_ge_atTop 3
  have hmem : ∀ᵐ t ∂volume.restrict scaleInterval, t ∈ scaleInterval :=
    ae_restrict_mem measurableSet_Icc
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict scaleInterval) (l := (atTop : Filter ℕ))
    (F := fun n t => tile (t * (length n - 1)) t * scaleWeight t)
    (f := fun t => limit * scaleWeight t) (fun t => B * scaleWeight t)
    (hmeas.mono fun _ h => h.mul weight_integrable.aestronglyMeasurable)
    (hlarge.mono fun n hn => hmem.mono fun t ht => by
      have ht' : (1 / 2 : ℝ) ≤ t := ht.1
      have hdiff : 0 ≤ length n - 1 := by linarith
      have hlen : 1 ≤ t * (length n - 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ht') hdiff]
      have hw : 0 ≤ scaleWeight t := inv_nonneg.mpr (by positivity : 0 ≤ t ^ 4)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_right (hB _ hlen t ht) hw)
    (weight_integrable.const_mul B)
    (hmem.mono fun t ht => by
      have ht' : (1 / 2 : ℝ) ≤ t := ht.1
      have hpos : 0 < t := by linarith
      have hsub : Tendsto (fun n => length n - 1) atTop atTop := by
        simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hlength
      exact ((htile t hpos).comp (hsub.const_mul_atTop hpos)).mul_const _)
  simpa [scaleAverage, integral_const_mul, weight_mass_pos.ne'] using
    hlim.div_const (∫ t in scaleInterval, scaleWeight t)

end TSGA.SSW
