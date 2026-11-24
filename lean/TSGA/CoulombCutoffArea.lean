import TSGA.TetrahedronBoundary
import TSGA.CutoffGradientBound
import TSGA.CoulombRoughTile

/-! # The surface cost and rough Coulomb bound at every smoothing width

For a narrow mollifier, only a layer along the four faces contributes to
the Fisher integral. For wider smoothing, the global volume estimate is
stronger. Both regimes give the same surface-to-volume bound.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW Set Metric
open scoped ComplexOrder

/-- The outer cutoff gradient required by the thermodynamic argument exists
on every admissible domain sequence, with a vanishing cost per unit volume. -/
def domainCutoffGradient (sob : SobolevDifferenceQuotients) (quant : SobolevDifferenceBounds)
    (D : DomainSequence) : CutoffGradient D := by
  apply Classical.choice
  obtain ⟨R,hR,B,hB,h⟩ := cutoff_gradient_bounds sob quant D.mollifier
  have all (n : ℕ) := h (D.region_open n) (D.region_bounded n).measure_lt_top.ne (D.delta_pos n)
  let g (n : ℕ) := Classical.choose (all n)
  have spec (n : ℕ) := Classical.choose_spec (all n)
  exact ⟨⟨g, fun n => (spec n).1, fun n => (spec n).2.1.aestronglyMeasurable,
    ⟨R,B,hR,hB,fun n => (spec n).2.2.1⟩⟩⟩

theorem tileCutoffAreaBound_of_sobolev (sob : SobolevDifferenceQuotients)
    (quant : SobolevDifferenceBounds) (η : Mollifier) :
    ∃ C ≥ 0, TileCutoffAreaBound η C := by
  obtain ⟨R,hR,B,hB,grad⟩ := cutoff_gradient_bounds sob quant η
  let C := 27744 * R * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ℓ δ hℓ hδ
  have hV : 0 < regionVolume (tetrahedron ℓ) := tetrahedron_volume_pos hℓ
  have hv := (ENNReal.toReal_pos_iff.mp hV).2.ne
  obtain ⟨G,hw,hg,hlayer,hglobal⟩ := grad (tetrahedron_open ℓ) hv hδ
  refine ⟨G,hw,hg,?_⟩
  let S := thickening (R*δ) (frontier (tetrahedron ℓ))
  by_cases h : R*δ ≤ ℓ
  · have hreg := tetrahedron_boundary_volume (mul_pos hR hδ) h
    have main : (∫ x, ‖G x‖^2) ≤ regionVolume S*(B/δ^2) := by
      have hmass : volume S ≠ ⊤ := by
        have hs := tetrahedron_boundary_subset ℓ (R*δ)
        have hpos : 0 < ℓ+16*(R*δ) := by positivity
        exact measure_ne_top_of_subset (hs.trans sdiff_subset)
          (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos hpos)).2.ne
      have hS : MeasurableSet S := isOpen_thickening.measurableSet
      have hi : Integrable (S.indicator (fun _ => B/δ^2)) := (integrable_indicator_iff hS).2 (integrableOn_const hmass)
      have hint := integral_mono_ae (hg.integrable_norm_pow (p := 2) (by decide)) hi hlayer
      simpa only [integral_indicator_const _ hS, smul_eq_mul,regionVolume] using hint
    apply main.trans
    apply (mul_le_mul_of_nonneg_right hreg (div_nonneg hB (sq_nonneg δ))).trans_eq
    rw [tetrahedron_volume hℓ]
    dsimp only [C]
    field_simp [hℓ.ne',hδ.ne']
    ring
  · apply hglobal.trans
    have hsmall : ℓ ≤ R*δ := (lt_of_not_ge h).le
    have hc : B*R ≤ C := by dsimp [C]; nlinarith only [mul_nonneg hB hR.le]
    have hpos : 0 < ℓ*δ := mul_pos hℓ hδ
    rw [div_le_div_iff₀ (sq_pos_of_pos hδ) hpos]
    calc
      _ = ((B*regionVolume (tetrahedron ℓ))*δ)*ℓ := by ring
      _ ≤ ((B*regionVolume (tetrahedron ℓ))*δ)*(R*δ) :=
        mul_le_mul_of_nonneg_left hsmall (mul_nonneg (mul_nonneg hB hV.le) hδ.le)
      _ = (B*R)*(regionVolume (tetrahedron ℓ)*δ^2) := by ring
      _ ≤ C*(regionVolume (tetrahedron ℓ)*δ^2) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hV.le (sq_nonneg δ))
      _ = _ := by ring

/-- The two rough bounds used by the quantitative gas theorem now follow
from the scalar Sobolev theorems and the one-body and Lieb–Oxford inputs.
One constant works for all densities, momenta, sizes and smoothing widths. -/
theorem FiniteEnergyInputs.exists_rough_constant (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (quant : SobolevDifferenceBounds) (η : Mollifier) :
    ∃ K₀ ≥ 1, ∀ K ≥ K₀, ∀ M : SpinMatrix, M.PosSemidef → ∀ (q : Position) (ℓ δ : ℝ), 0 < ℓ → 0 < δ →
      let ρ := M.trace.re
      (-K*(ρ*ρ^(1/3:ℝ)) ≤ averagedTile energy η M q ℓ δ) ∧
      averagedTile energy η M q ℓ δ + K*(ρ*ρ^(1/3:ℝ)) ≤ K*(ρ*rateGrowth ρ q + ρ/(ℓ*δ)) := by
  obtain ⟨C,_,hC⟩ := tileCutoffAreaBound_of_sobolev sob quant η
  let K₀ := max (max 1 H.loCoeff) (max (H.cTF*(1+H.κ₁)) (8*(1+H.κ₂)*C))
  have hl : max 1 H.loCoeff ≤ K₀ := le_max_left _ _
  have hr : max (H.cTF*(1+H.κ₁)) (8*(1+H.κ₂)*C) ≤ K₀ := le_max_right _ _
  have ho := (le_max_left _ _).trans hl
  exact ⟨K₀,ho,fun K hK => H.rough_tile hC (ho.trans hK) ((le_max_right _ _).trans (hl.trans hK))
    ((le_max_left _ _).trans (hr.trans hK)) ((le_max_right _ _).trans (hr.trans hK))⟩

end TSGA.ManyBody
