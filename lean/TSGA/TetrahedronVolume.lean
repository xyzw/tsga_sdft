import TSGA.TetrahedronCoulomb
import TSGA.TilingBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Mass of an individual tetrahedral cutoff

In face-centered coordinates the open cell is given by
|z| < y < x < ℓ/2. Its volume fixes the factor 24 in the averaged tiling.
-/

noncomputable section
namespace TSGA.SSW
open MeasureTheory Set Metric

private def cartesianTriple : Position ≃ᵐ ℝ × ℝ × ℝ :=
  ((MeasurableEquiv.toLp 2 _).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.finTwoArrow (α := ℝ)))

private theorem cartesianTriple_preserving : MeasurePreserving cartesianTriple :=
  ((MeasurePreserving.id (μ := (volume : Measure ℝ))).prod (volume_preserving_finTwoArrow ℝ)).comp
    ((volume_preserving_piFinSuccAbove _ 0).comp (PiLp.volume_preserving_ofLp (Fin 3)))

private def openPyramid (L : ℝ) (u : ℝ × ℝ × ℝ) : ℝ :=
  if |u.2.2| < u.2.1 ∧ u.2.1 < u.1 ∧ u.1 < L then 1 else 0

private theorem openPyramid_inner (L a b : ℝ) :
    (∫ z, openPyramid L (a,b,z)) = if 0 < b ∧ b < a ∧ a < L then 2*b else 0 := by
  classical
  by_cases h : 0 < b ∧ b < a ∧ a < L
  · have e (z : ℝ) : openPyramid L (a,b,z) = (Ioo (-b) b).indicator (fun _ => (1:ℝ)) z := by
      simp [openPyramid,h.2.1,h.2.2,Set.indicator,abs_lt]
    simp only [e,integral_indicator measurableSet_Ioo,setIntegral_const,smul_eq_mul,mul_one,ite_eq_left h]
    rw [Real.volume_real_Ioo_of_le (show -b ≤ b by linarith [h.1])]
    ring
  · have e (z : ℝ) : openPyramid L (a,b,z) = 0 := by
      apply ite_eq_right
      rintro ⟨hz,hb,ha⟩
      exact h ⟨(abs_nonneg z).trans_lt hz,hb,ha⟩
    simp only [e,integral_zero,ite_eq_right h]

private theorem openPyramid_middle (L a : ℝ) :
    (∫ b, ∫ z, openPyramid L (a,b,z)) = (Ioo 0 L).indicator (fun x : ℝ => x^2) a := by
  classical
  simp_rw [openPyramid_inner]
  by_cases h : a ∈ Ioo 0 L
  · have e (b : ℝ) : (if 0 < b ∧ b < a ∧ a < L then 2*b else 0) =
        (Ioo 0 a).indicator (fun x : ℝ => 2*x) b := by simp [Set.indicator,h.2]
    rw [Set.indicator_of_mem h]
    simp only [e,integral_indicator measurableSet_Ioo,← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h.1.le]
    change (∫ b in 0..a, (2:ℝ)*b) = a^2
    rw [intervalIntegral.integral_const_mul 2 (fun x => x), integral_id]
    ring
  · have e (b : ℝ) : ¬ (0 < b ∧ b < a ∧ a < L) := fun hb => h ⟨hb.1.trans hb.2.1,hb.2.2⟩
    simp [e,Set.indicator_of_notMem h]

theorem tetrahedron_volume {ℓ : ℝ} (hℓ : 0 < ℓ) :
    regionVolume (tetrahedron ℓ) = ℓ^3/24 := by
  classical
  let L := ℓ/2
  let v : Position := WithLp.toLp 2 ![3*ℓ/8,ℓ/4,0]
  let g := (tetrahedron ℓ).indicator (fun _ => (1:ℝ))
  have hg : Integrable g := (integrable_indicator_iff (tetrahedron_open ℓ).measurableSet).2
    (integrableOn_const (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos hℓ)).2.ne)
  have hcoord (x : Position) : cartesianTriple x = (x 0,x 1,x 2) := rfl
  have heq (x : Position) : g x = openPyramid L (cartesianTriple (x+v)) := by
    simp [g,hcoord,Set.indicator,openPyramid,v,L,tetrahedron]
  have hv : MeasurePreserving (fun x : Position => cartesianTriple (x+v)) :=
    cartesianTriple_preserving.comp (measurePreserving_add_right volume v)
  have hemb : MeasurableEmbedding (fun x : Position => cartesianTriple (x+v)) :=
    cartesianTriple.measurableEmbedding.comp (Homeomorph.addRight v).toMeasurableEquiv.measurableEmbedding
  have hi : Integrable (openPyramid L) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) :=
    (hv.integrable_comp_emb hemb).1 (by simpa only [Function.comp_def,← heq] using hg)
  have first : regionVolume (tetrahedron ℓ) = ∫ x, g x := by
    simp [g,integral_indicator (tetrahedron_open ℓ).measurableSet,regionVolume]
  rw [first]
  simp_rw [heq]
  rw [hv.integral_comp hemb (openPyramid L)]
  change (∫ z, openPyramid L z ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))) = _
  rw [integral_prod _ hi]
  have hx : (fun a : ℝ => ∫ u : ℝ × ℝ, openPyramid L (a,u) ∂((volume : Measure ℝ).prod volume)) =ᵐ[volume]
      fun a => (Ioo 0 L).indicator (fun x : ℝ => x^2) a := by
    filter_upwards [hi.prod_right_ae] with a ha
    exact (integral_prod _ ha).trans (openPyramid_middle L a)
  rw [integral_congr_ae hx,integral_indicator measurableSet_Ioo,← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show 0 ≤ L from (half_pos hℓ).le),integral_pow]
  dsimp [L]
  ring

theorem tile_cutoff_mass_explicit (η : Mollifier) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) :
    (∫ x, smoothedIndicator (tetrahedron ℓ) η δ x) = ℓ^3/24 :=
  (tile_cutoff_mass η hℓ hδ).trans (tetrahedron_volume hℓ)

end TSGA.SSW

namespace TSGA.Localization
open MeasureTheory SSW

/-- Translating or rotating an individual lower or shrunken upper tile
preserves its mass. This is the per-label mass used by TetrahedralCutoffs. -/
theorem CutoffSide.shape_mass (side : CutoffSide) (η : Mollifier) {ε L δ : ℝ}
    (hle : ε ≤ 1) (hL : 0 < L) (hδ : 0 < δ)
    (e : Position ≃ᵐ Position) (he : MeasurePreserving e)
    (length : ℝ) (hlength : length = match side with | .upper => (1-ε)*L | .lower => L) :
    (∫ x, smoothedIndicator (tetrahedron length) η δ (e x)) = side.mass ε * L^3/24 := by
  rw [he.integral_comp' _]
  cases side with
  | lower => simpa [hlength,CutoffSide.mass] using tile_cutoff_mass_explicit η hL hδ
  | upper =>
    change length = (1-ε)*L at hlength
    subst length
    rcases hle.eq_or_lt with rfl | hlt
    · have he : tetrahedron 0 = ∅ := by
        ext x
        change (|x 2| < x 1 + 0/4 ∧ x 1+0/4 < x 0+3*0/8 ∧ x 0+3*0/8 < 0/2) ↔ False
        constructor
        · rintro ⟨h1,h2,h3⟩
          linarith [abs_nonneg (x 2)]
        · simp
      simp [he,smoothedIndicator,CutoffSide.mass,MeasureTheory.convolution]
    · rw [tile_cutoff_mass_explicit η (mul_pos (sub_pos.mpr hlt) hL) hδ]
      simp [CutoffSide.mass,mul_pow]

end TSGA.Localization
