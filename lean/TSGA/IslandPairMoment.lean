import TSGA.IslandExteriorTrial
import Mathlib.Probability.Distributions.Bernoulli

/-! # Two-point exterior probabilities

A two-point mark with rate `2v` realizes any normalized overlap in the
unit interval. This identifies the auxiliary mark in the exterior
comparison directly from the Poisson process's two-point Laplace formula.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory ProbabilityTheory

private def halfProbability : unitInterval := ⟨1/2, by constructor <;> norm_num⟩

/-- A fixed auxiliary probability space for all exterior pairs. -/
abbrev islandFairCoin : Measure Bool := bernoulliMeasure true false halfProbability

private def pairAt (v : ℝ) (hv : 0 ≤ v) (t : Set.Icc (0:ℝ) 1) : MarkPair islandFairCoin where
  rate := ⟨2*v, by positivity⟩
  b := fun b => if b then 1 else 0
  c := fun b => if b then t.val else 1-t.val
  hb := integrable_bernoulliMeasure _ _ _ _
  hc := integrable_bernoulliMeasure _ _ _ _
  hbc := integrable_bernoulliMeasure _ _ _ _
  range := ae_of_all _ fun b => by
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Set.mem_Icc]
    all_goals constructor <;> constructor <;> linarith [t.property.1,t.property.2]

private theorem pairAt_means {v : ℝ} (hv : 0 ≤ v) (t : Set.Icc (0:ℝ) 1) :
    let w := pairAt v hv t
    (w.rate:ℝ)*(∫ b, w.b b ∂islandFairCoin) = v ∧
    (w.rate:ℝ)*(∫ b, w.c b ∂islandFairCoin) = v ∧ w.overlap = v*t.val := by
  dsimp only
  unfold MarkPair.overlap
  simp only [pairAt,islandFairCoin,integral_bernoulliMeasure,halfProbability,ite_true,
    Bool.false_eq_true,ite_false,smul_eq_mul]
  refine ⟨?_,?_,?_⟩
  all_goals change (2*v)*_ = _
  all_goals ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {χ : Ω → Position → ℝ} {v : ℝ} {h : PairSpace → ℝ}

/-- Realize the auxiliary mark from the two-point moment. Outside the
full-measure set on which the normalized overlap belongs to the unit
interval its value can be clipped without changing either identity. -/
def ExteriorOverlap.of_pair_moment (hv : 0 ≤ v) (hmeas : Measurable h)
    (hrange : ∀ᵐ z ∂pairVolume, h z ∈ Set.Icc 0 1)
    (hmoment : ∀ᵐ z ∂pairVolume, (∫ ω, χ ω z.1*χ ω z.2 ∂μ) = Real.exp (-(2*v))*Real.exp (v*h z)) :
    ExteriorOverlap μ islandFairCoin χ v := by
  let t (z : PairSpace) : Set.Icc (0:ℝ) 1 := ⟨max 0 (min (h z) 1),
    le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have heq : ∀ᵐ z ∂pairVolume, (t z).val = h z := hrange.mono fun z hz => by
    change max 0 (min (h z) 1) = h z
    rw [min_eq_left hz.2,max_eq_right hz.1]
  refine ⟨fun z => pairAt v hv (t z),h,hmeas,hrange,?_,?_⟩
  · filter_upwards [hmoment,heq] with z hh ht
    obtain ⟨hb,hc,ho⟩ := pairAt_means hv (t z)
    rw [hh,(pairAt v hv (t z)).mean_eq hb hc ho,ht]
  · filter_upwards [heq] with z hz
    simpa only [← hz] using pairAt_means hv (t z)

end TSGA.ManyBody
