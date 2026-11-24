import TSGA.IslandChargeDomain
import TSGA.IslandCoulombKernel

/-! # Finite Coulomb energy and Thomas–Fermi moment for L¹ ∩ L² charges -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set Metric

/-- The unit-ball Coulomb kernel has a finite Schur bound. Outside that
ball the Coulomb energy is dominated by the product of the two L¹ masses. -/
theorem island_direct_integrable {ρ : Position → ℝ} (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x)
    (h₁ : Integrable ρ) (h₂ : Integrable (fun x => ρ x^2)) :
    Integrable (directKernel ρ ρ) pairVolume := by
  have near := ((islandNearSchur (by norm_num : (0:ℝ)<1)).charge_bound hm hp h₂).1
  have far := h₁.mul_prod h₁
  have hmeas : Measurable (directKernel ρ ρ) :=
    ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).div (measurable_fst.sub measurable_snd).norm
  apply (near.add far).mono' hmeas.aestronglyMeasurable
  filter_upwards with z
  change ‖ρ z.1*ρ z.2/‖z.1-z.2‖‖ ≤ ρ z.1*ρ z.2*islandNearKernel 1 (z.2-z.1)+ρ z.1*ρ z.2
  have hn := mul_nonneg (hp z.1) (hp z.2)
  rw [Real.norm_of_nonneg (div_nonneg hn (norm_nonneg _)),norm_sub_rev z.1 z.2]
  by_cases h : ‖z.2-z.1‖ < 1
  · rw [islandNearKernel,indicator_of_mem (mem_ball_zero_iff.mpr h),← div_eq_mul_inv]
    exact le_add_of_nonneg_right hn
  · apply (div_le_self hn (le_of_not_gt h)).trans
    exact le_add_of_nonneg_left (mul_nonneg hn (islandNearKernel_pos _ _))

/-- Instantiate the entire deterministic Coulomb domain of the island
trial using only Borel representatives and the L¹ and L² hypotheses. -/
theorem IslandChargeDomain.of_L1_L2 {B D : Density} (hb : Measurable B.charge) (hd : Measurable D.charge)
    (b₁ : Integrable B.charge) (d₁ : Integrable D.charge)
    (b₂ : Integrable (fun x => B.charge x^2)) (d₂ : Integrable (fun x => D.charge x^2)) :
    IslandChargeDomain B D := by
  have hm : Measurable (B.charge+D.charge) := hb.add hd
  have hs : Integrable (fun x => (B.charge+D.charge) x ^2) := by
    apply ((b₂.add d₂).const_mul 2).mono' (hm.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    change ‖(B.charge x+D.charge x)^2‖ ≤ 2*(B.charge x^2+D.charge x^2)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (B.charge x-D.charge x)]
  exact ⟨hb,hd,island_direct_integrable hm (fun x => add_nonneg (B.charge_nonneg x) (D.charge_nonneg x)) (b₁.add d₁) hs⟩

/-- All intermediate density moments between one and two are integrable. -/
theorem island_moment_integrable {ρ : Position → ℝ} (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x)
    (h₁ : Integrable ρ) (h₂ : Integrable (fun x => ρ x^2)) {p : ℝ} (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) :
    Integrable (fun x => ρ x^p) := by
  apply (h₁.add h₂).mono' (hm.pow_const p).aestronglyMeasurable
  filter_upwards with x
  change ‖ρ x^p‖ ≤ ρ x+ρ x^2
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hp x) _)]
  rcases le_total (ρ x) 1 with hx | hx
  · exact (Real.rpow_le_self_of_le_one (hp x) hx hp₁).trans (le_add_of_nonneg_right (sq_nonneg _))
  · have h := Real.rpow_le_rpow_of_exponent_le hx hp₂
    rw [Real.rpow_two] at h
    exact h.trans (le_add_of_nonneg_left (hp x))

end TSGA.ManyBody
