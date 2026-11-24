import TSGA.ScaleAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Extending the strict dilation cutoff to the endpoint

Finite energy comparisons stated for 0 < α < 1/2 extend to the normalized
average on [1/2, 3/2] when the weighted finite energy is integrable there.
-/

noncomputable section

namespace TSGA.SSW

open Filter MeasureTheory Set
open scoped Topology

def scaleAverageAt (α : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ t in Icc (1 - α) (1 + α), f t * scaleWeight t) /
    (∫ t in Icc (1 - α) (1 + α), scaleWeight t)

theorem scaleWeight_integrableOn : IntegrableOn scaleWeight scaleInterval := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply (continuousOn_id.pow 4).inv₀
  intro t ht
  have h : (1/2 : ℝ) ≤ t := ht.1
  exact pow_ne_zero _ (by linarith : t ≠ 0)

theorem scaleWeight_integral_pos : 0 < ∫ t in scaleInterval, scaleWeight t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ scaleWeight_integrableOn).2
  · have hs : scaleInterval ⊆ Function.support scaleWeight := by
      intro t ht
      have h : (1/2 : ℝ) ≤ t := ht.1
      exact inv_ne_zero (pow_ne_zero _ (by linarith))
    rw [inter_eq_right.mpr hs, scaleInterval, Real.volume_Icc]
    norm_num
  · exact ae_of_all _ fun t => inv_nonneg.mpr (by positivity : 0 ≤ t^4)

private theorem integral_dilation_endpoint {g : ℝ → ℝ} (hg : IntegrableOn g scaleInterval) :
    Tendsto (fun α : ℝ => ∫ t in Icc (1 - α) (1 + α), g t) (𝓝[<] (1/2 : ℝ))
      (𝓝 (∫ t in scaleInterval, g t)) := by
  let S (α : ℝ) := Icc (1 - α) (1 + α)
  let μ := volume.restrict scaleInterval
  have hα : Tendsto id (𝓝[<] (1/2 : ℝ)) (𝓝 (1/2 : ℝ)) := nhdsWithin_le_nhds
  have hi : ∀ᵐ t ∂μ, t ∈ Ioo (1/2 : ℝ) (3/2 : ℝ) := by
    change ∀ᵐ t ∂volume.restrict (Icc (1/2 : ℝ) (3/2 : ℝ)), _
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[<] (1/2 : ℝ))
    (F := fun α => (S α).indicator g) (f := g) (fun t => ‖g t‖)
    (Eventually.of_forall fun α => hg.aestronglyMeasurable.indicator measurableSet_Icc)
    (Eventually.of_forall fun α => ae_of_all μ fun t => by
      by_cases h : t ∈ S α <;> simp [h])
    hg.norm (hi.mono fun t h => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hα.eventually_const_lt (show 1-t < 1/2 by linarith [h.1]),
        hα.eventually_const_lt (show t-1 < 1/2 by linarith [h.2])] with α ha hb
      have ht : t ∈ S α := ⟨by change 1-α ≤ t; change 1-t < α at ha; linarith,
        by change t ≤ 1+α; change t-1 < α at hb; linarith⟩
      simp [ht])
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with α ha
  have hs : S α ⊆ scaleInterval := by
    intro t h
    change α < (1/2 : ℝ) at ha
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [integral_indicator measurableSet_Icc]
  change (∫ t in S α, g t ∂volume.restrict scaleInterval) = ∫ t in S α, g t
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hs]

theorem scaleAverageAt_tendsto_half {f : ℝ → ℝ}
    (hf : IntegrableOn (fun t => f t * scaleWeight t) scaleInterval) :
    Tendsto (fun α => scaleAverageAt α f) (𝓝[<] (1/2 : ℝ)) (𝓝 (scaleAverage f)) :=
  (integral_dilation_endpoint hf).div (integral_dilation_endpoint scaleWeight_integrableOn)
    scaleWeight_integral_pos.ne'

/-- The electrostatic coefficient at the endpoint is precisely log 2. -/
theorem finite_upper_at_half {f : ℝ → ℝ} {E C : ℝ}
    (hf : IntegrableOn (fun t => f t * scaleWeight t) scaleInterval)
    (h : ∀ α : ℝ, 0 < α → α < 1/2 → E ≤ scaleAverageAt α f + C * Real.log α⁻¹) :
    E ≤ scaleAverage f + C * Real.log 2 := by
  have hα : Tendsto id (𝓝[<] (1/2 : ℝ)) (𝓝 (1/2 : ℝ)) := nhdsWithin_le_nhds
  have hlog := (Real.continuousAt_log (by norm_num : (1/2 : ℝ)⁻¹ ≠ 0)).tendsto.comp
    (hα.inv₀ (by norm_num))
  have hi : Tendsto (fun α : ℝ => Real.log α⁻¹) (𝓝[<] (1/2 : ℝ)) (𝓝 (Real.log 2)) := by
    simpa only [Function.comp_def, id_eq, inv_div, div_one] using hlog
  apply ge_of_tendsto ((scaleAverageAt_tendsto_half hf).add (hi.const_mul C))
  filter_upwards [hα.eventually_const_lt (by norm_num : (0:ℝ) < 1/2), self_mem_nhdsWithin] with α hpos hlt
  exact h α hpos hlt

/-- Replacing log 2 by 1 retains the same bound for a nonnegative error
coefficient. This form is used for both finite upper localization steps. -/
theorem finite_upper_at_half_le_one {f : ℝ → ℝ} {E B C : ℝ}
    (hf : IntegrableOn (fun t => f t * scaleWeight t) scaleInterval) (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → α < 1/2 → E ≤ scaleAverageAt α f + B + C * Real.log α⁻¹) :
    E ≤ scaleAverage f + B + C := by
  have he := finite_upper_at_half (E := E - B) (C := C) hf
    (fun α hα hlt => by linarith only [h α hα hlt])
  have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
  linarith only [he, mul_le_mul_of_nonneg_left hlog hC]

end TSGA.SSW
