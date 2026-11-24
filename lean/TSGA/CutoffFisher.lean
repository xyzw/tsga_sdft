import TSGA.SSWDomain
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Sobolev regularity of the square root of a smoothed indicator

At each x, the square root of the convolution is an L² norm over the
domain. The reverse triangle inequality controls its translation differences.
Integration over x gives the volume of the domain times the translation
bound on the mollifier amplitude.
-/

noncomputable section
namespace TSGA.SSW
open MeasureTheory MeasureTheory.Measure Set
open scoped Convolution InnerProductSpace

/-- The usual difference-quotient characterization of scalar H¹ on ℝ³. -/
def SobolevDifferenceQuotients : Prop := ∀ (u : Position → ℝ), MemLp u 2 →
  ((∃ G : Position → Position, (∀ i, WeakPartialOn univ i u (fun x => G x i)) ∧ MemLp G 2) ↔
   ∃ C ≥ 0, ∀ h : Position, (∫ x, (u (x+h)-u x)^2) ≤ C*‖h‖^2)

theorem amplitude_L2 {f : Position → ℝ} (hp : ∀ x, 0 ≤ f x) (hi : Integrable f) :
    MemLp (fun x => √(f x)) 2 :=
  (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable)).2
    (by simpa only [Real.sq_sqrt (hp _)] using hi)

private theorem lp_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ} (h : MemLp f 2 μ) :
    ‖h.toLp f‖^2 = ∫ x, f x^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem norm_difference {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (√(∫ x, f x^2 ∂μ) - √(∫ x, g x^2 ∂μ))^2 ≤ ∫ x, (f x-g x)^2 ∂μ := by
  rw [← lp_norm_sq hf, ← lp_norm_sq hg, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hh := abs_le.mp (abs_norm_sub_norm_le (hf.toLp f) (hg.toLp g))
  have h := sq_le_sq' hh.1 hh.2
  simpa only [← MemLp.toLp_sub, lp_norm_sq, Pi.sub_apply] using h

theorem convolution_restrict (Ω : Set Position) (hm : MeasurableSet Ω) (k : Position → ℝ)
    (x : Position) :
    (Ω.indicator (fun _ => (1:ℝ)) ⋆ k) x = ∫ y in Ω, k (x-y) := by
  classical
  change (∫ y, Ω.indicator (fun _ => (1:ℝ)) y * k (x-y)) = _
  rw [← integral_indicator hm]
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ Ω <;> simp [hy]

/-- The estimate before applying the scalar Sobolev characterization.
Every bounded measurable domain is allowed. -/
theorem cutoff_translation_energy {Ω : Set Position} (hm : MeasurableSet Ω) (hv : volume Ω ≠ ⊤)
    (η : Mollifier) {δ : ℝ} (hδ : 0 < δ) (h : Position) :
    let f := smoothedIndicator Ω η δ
    let u := fun x => √(η.scaled δ x)
    (∫ x, (√(f (x+h))-√(f x))^2) ≤ regionVolume Ω * ∫ x, (u (x+h)-u x)^2 := by
  classical
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  let f := smoothedIndicator Ω η δ
  let u := fun x => √(η.scaled δ x)
  let χ := Ω.indicator (fun _ => (1:ℝ))
  have hχ : Integrable χ := (integrable_indicator_iff hm).2 (integrableOn_const hv)
  have hk (x : Position) : 0 ≤ η.scaled δ x := mul_nonneg (inv_nonneg.mpr (pow_nonneg hδ.le _)) (η.nonneg _)
  have hu : MemLp u 2 := amplitude_L2 hk (η.scaled_integrable hδ)
  have hux (x : Position) : MemLp (fun y => u (x-y)) 2 (volume.restrict Ω) :=
    (hu.comp_measurePreserving (measurePreserving_sub_left volume x)).restrict _
  have hs (x : Position) : ∫ y in Ω, u (x-y)^2 = f x := by
    simp_rw [show ∀ z, u z^2 = η.scaled δ z from fun z => Real.sq_sqrt (hk z)]
    exact (convolution_restrict Ω hm _ x).symm
  let v := fun x => (u (x+h)-u x)^2
  have hi : Integrable v := ((hu.comp_measurePreserving (measurePreserving_add_right volume h)).sub hu).integrable_sq
  have H (x : Position) : (√(f (x+h))-√(f x))^2 ≤ (χ ⋆ v) x := by
    rw [convolution_restrict Ω hm, ← hs (x+h), ← hs x]
    simpa only [v, show ∀ y, x+h-y = x-y+h from fun _ => by abel] using norm_difference (hux (x+h)) (hux x)
  have hI : (∫ x, (χ ⋆ v) x) = regionVolume Ω * ∫ x, v x := by
    rw [integral_convolution _ hχ hi]
    simp [χ,integral_indicator hm, regionVolume]
  exact (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (hχ.integrable_convolution _ hi)
    (ae_of_all _ H)).trans_eq hI

/-- Dilation of the normalized kernel preserves the squared L² translation
cost at the rescaled displacement. -/
theorem scale_amplitude_difference (η : Mollifier) {δ : ℝ} (hδ : 0 < δ) (h : Position) :
    let u := fun x => √(η.kernel x)
    let w := fun x => √(η.scaled δ x)
    (∫ x, (w (x+h)-w x)^2) = ∫ y, (u (y+δ⁻¹ • h)-u y)^2 := by
  intro u w
  let a := √((δ^3)⁻¹)
  have ha : a^2 = (δ^3)⁻¹ := Real.sq_sqrt (by positivity)
  have he (x : Position) : w x = a*u (δ⁻¹ • x) := Real.sqrt_mul (by positivity) _
  have he' (x : Position) : (w (x+h)-w x)^2 = a^2*(u (δ⁻¹ • x + δ⁻¹ • h)-u (δ⁻¹ • x))^2 := by
    rw [he,he,smul_add,← mul_sub,mul_pow]
  simp_rw [he',integral_const_mul,ha]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun y => (u (y+δ⁻¹ • h)-u y)^2) hδ.le]
  simp [smul_eq_mul,finrank_euclideanSpace,hδ.ne']

theorem smoothedIndicator_sqrt_sobolev (sob : SobolevDifferenceQuotients)
    {Ω : Set Position} (hm : MeasurableSet Ω) (hv : volume Ω ≠ ⊤) (η : Mollifier) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : Position → Position, (∀ i, WeakPartialOn univ i (fun x => √(smoothedIndicator Ω η δ x))
      (fun x => G x i)) ∧ MemLp G 2 := by
  classical
  let f := smoothedIndicator Ω η δ
  let u := fun x => √(η.kernel x)
  let w := fun x => √(η.scaled δ x)
  let χ := Ω.indicator (fun _ => (1:ℝ))
  have hχ : Integrable χ := (integrable_indicator_iff hm).2 (integrableOn_const hv)
  have hp (x) : 0 ≤ f x := by
    change 0 ≤ ∫ y, χ y * η.scaled δ (x-y)
    apply integral_nonneg
    intro y
    exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg hδ.le _)) (η.nonneg _))
  have hi : Integrable f := hχ.integrable_convolution _ (η.scaled_integrable hδ)
  obtain ⟨C,hC,htrans⟩ := (sob u (amplitude_L2 η.nonneg η.integrable)).1 η.sqrt_gradient
  apply (sob _ (amplitude_L2 hp hi)).2
  refine ⟨regionVolume Ω*C*(δ⁻¹)^2, by positivity [show 0 ≤ regionVolume Ω from ENNReal.toReal_nonneg], ?_⟩
  intro h
  have hscale : (∫ x, (w (x+h)-w x)^2) = ∫ y, (u (y+δ⁻¹ • h)-u y)^2 :=
    scale_amplitude_difference η hδ h
  have hh := cutoff_translation_energy hm hv η hδ h
  change _ ≤ regionVolume Ω * (∫ x, (w (x+h)-w x)^2) at hh
  rw [hscale] at hh
  apply hh.trans
  have ht := mul_le_mul_of_nonneg_left (htrans (δ⁻¹ • h)) (show 0 ≤ regionVolume Ω from ENNReal.toReal_nonneg)
  simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hδ.le), mul_pow, mul_assoc] using ht

end TSGA.SSW
