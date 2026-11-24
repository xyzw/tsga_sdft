import TSGA.SSWDomain

/-! # The boundary layer in the thermodynamic localization proof

The uniform boundary estimate bounds the fraction of the domain volume
occupied by a tubular neighborhood of its boundary. This applies to the
translated tiles meeting the boundary in Steps 2 and 3 of `thm:spiral_limit`.
-/

namespace TSGA.SSW.DomainSequence

open Filter MeasureTheory
open scoped Topology

variable (D : DomainSequence)

/-- One geometric constant bounds the relative volume for every sequence of
positive radii of order `o(|Ωₙ|^(1/3))`. -/
theorem boundaryLayer_eventually_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ → ℝ, (∀ n, 0 < r n) →
      Tendsto (fun n => r n / D.length n) atTop (𝓝 0) →
      ∀ᶠ n in atTop, regionVolume (Metric.thickening (r n) (frontier (D.region n))) / D.vol n ≤
        C * (r n / D.length n) := by
  obtain ⟨C, hC, hbound⟩ := D.boundary
  refine ⟨C, hC, ?_⟩
  intro r hr hratio
  have hsmall := hratio.eventually_lt_const (inv_pos.mpr hC)
  filter_upwards [hsmall] with n hn
  have hv := D.vol_pos n
  have hlen : 0 < D.length n := Real.rpow_pos_of_pos hv _
  have hcut : r n ≤ D.length n / C := by
    rw [div_eq_inv_mul]
    exact ((div_lt_iff₀ hlen).mp hn).le
  have hfrac := ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg hC.le (hr n).le) (Real.rpow_nonneg hv.le (2 / 3 : ℝ)))
    (hbound n (r n) (hr n) hcut)
  have hpower : D.vol n ^ (2 / 3 : ℝ) * D.length n = D.vol n := by
    rw [length, ← Real.rpow_add hv]
    norm_num
  calc
    _ ≤ C * r n * D.vol n ^ (2 / 3 : ℝ) / D.vol n := div_le_div_of_nonneg_right hfrac hv.le
    _ = C * r n * D.vol n ^ (2 / 3 : ℝ) / (D.vol n ^ (2 / 3 : ℝ) * D.length n) := by rw [hpower]
    _ = C * (r n / D.length n) := by
      field_simp [(Real.rpow_pos_of_pos hv (2 / 3 : ℝ)).ne', hlen.ne']

/-- Every positive radius of order `o(|Ωₙ|^(1/3))` gives a vanishing fraction
of boundary volume. -/
theorem boundaryLayer_tendsto_zero {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hratio : Tendsto (fun n => r n / D.length n) atTop (𝓝 0)) :
    Tendsto (fun n => regionVolume (Metric.thickening (r n) (frontier (D.region n))) / D.vol n)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := D.boundaryLayer_eventually_le
  have hupper : Tendsto (fun n => C * (r n / D.length n)) atTop (𝓝 0) := by
    simpa using hratio.const_mul C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => div_nonneg ENNReal.toReal_nonneg (D.vol_pos n).le)
    (hbound r hr hratio)

private theorem boundary_scale_tendsto (a : ℝ) :
    Tendsto (fun n => a * (D.tileLength n + 1 + D.delta n) / D.length n) atTop (𝓝 0) := by
  simpa only [boundaryFraction, mul_div_assoc, mul_zero] using
    D.boundaryFraction_tendsto_zero.const_mul a

/-- Actual volume of the tile-width boundary neighborhood, divided by the domain volume. -/
noncomputable def tileBoundaryFraction (a : ℝ) (n : ℕ) : ℝ :=
  regionVolume (Metric.thickening (a * (D.tileLength n + 1 + D.delta n)) (frontier (D.region n))) /
    D.vol n

/-- Quantitative fraction of boundary tiles for the scales of Steps 2 and 3. -/
theorem tileBoundaryLayer_eventually_le :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop,
      D.tileBoundaryFraction a n ≤ C * a * D.boundaryFraction n := by
  obtain ⟨C, hC, hbound⟩ := D.boundaryLayer_eventually_le
  refine ⟨C, hC, ?_⟩
  intro a ha
  have h := hbound _ (fun n => mul_pos ha (add_pos (add_pos (D.tileLength_pos n) zero_lt_one)
    (D.delta_pos n))) (D.boundary_scale_tendsto a)
  simpa only [tileBoundaryFraction, boundaryFraction, mul_assoc, mul_div_assoc] using h

/-- Width of the boundary tiles for inner smoothing width one and
`ℓ = |Ωₙ|^(1/6)`, with any fixed positive geometric factor. -/
theorem tileBoundaryLayer_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (D.tileBoundaryFraction a) atTop (𝓝 0) := by
  unfold tileBoundaryFraction
  apply D.boundaryLayer_tendsto_zero
  · intro n
    exact mul_pos ha (add_pos (add_pos (D.tileLength_pos n) zero_lt_one) (D.delta_pos n))
  · exact D.boundary_scale_tendsto a

/-- The outer cutoff cost per volume vanishes. For the cutoff in the manuscript,
`G n` is the weak gradient of its square root. Its squared norm is bounded
by `B / δₙ²` on a layer of width `a δₙ` and vanishes off that layer. -/
theorem cutoffKinetic_tendsto_zero (G : ℕ → Position → Position) (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hmeas : ∀ n, AEStronglyMeasurable (G n) volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖G n x‖ ^ 2 ≤
      (Metric.thickening (a * D.delta n) (frontier (D.region n))).indicator
        (fun _ => B / D.delta n ^ 2) x) :
    Tendsto (fun n => (∫ x, ‖G n x‖ ^ 2) / D.vol n) atTop (𝓝 0) := by
  classical
  obtain ⟨C, _, hgeom⟩ := D.boundaryLayer_eventually_le
  have hδ : Tendsto (fun n => D.delta n / D.length n) atTop (𝓝 0) := D.delta_ratio
  have hratio : Tendsto (fun n => a * D.delta n / D.length n) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hδ.const_mul a
  have hupper : Tendsto (fun n => B * C * a / (D.delta n * D.length n)) atTop (𝓝 0) :=
    D.delta_product.const_div_atTop _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun n =>
      div_nonneg (integral_nonneg fun x => sq_nonneg ‖G n x‖) (D.vol_pos n).le
  filter_upwards [hgeom _ (fun n => mul_pos ha (D.delta_pos n)) hratio] with n hn
  let S := Metric.thickening (a * D.delta n) (frontier (D.region n))
  have hS : MeasurableSet S := Metric.isOpen_thickening.measurableSet
  have hbdd : Bornology.IsBounded S :=
    ((D.region_bounded n).closure.subset frontier_subset_closure).thickening
  have hi : Integrable (S.indicator (fun _ => B / D.delta n ^ 2)) :=
    (integrable_indicator_iff hS).2 (integrableOn_const hbdd.measure_lt_top.ne)
  have hG : Integrable (fun x => ‖G n x‖ ^ 2) :=
    hi.mono' ((hmeas n).norm.pow 2) (by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound n)
  have hint := integral_mono_ae hG hi (hbound n)
  rw [integral_indicator_const _ hS, smul_eq_mul] at hint
  have hk : 0 ≤ B / D.delta n ^ 2 := div_nonneg hB (sq_nonneg _)
  calc
    _ ≤ (regionVolume S * (B / D.delta n ^ 2)) / D.vol n :=
      div_le_div_of_nonneg_right hint (D.vol_pos n).le
    _ = regionVolume S / D.vol n * (B / D.delta n ^ 2) := by ring
    _ ≤ (C * (a * D.delta n / D.length n)) * (B / D.delta n ^ 2) :=
      mul_le_mul_of_nonneg_right hn hk
    _ = B * C * a / (D.delta n * D.length n) := by
      have hlength : 0 < D.length n := Real.rpow_pos_of_pos (D.vol_pos n) _
      field_simp [(D.delta_pos n).ne', hlength.ne']

end TSGA.SSW.DomainSequence
