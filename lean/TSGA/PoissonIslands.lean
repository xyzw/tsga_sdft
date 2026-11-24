import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Local laws of Poisson islands in Appendix C

All marks influencing one or two spatial points lie in a bounded window.
On that window, condition on the Poisson number of islands and integrate
their independent marks against the normalized intensity.
-/

noncomputable section

namespace TSGA.Islands

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

variable {Y : Type*} [MeasurableSpace Y]

/-- Expectation on a bounded window of rate λ with independent marks of law ν. -/
def expect (rate : ℝ≥0) (ν : Measure Y) (X : (n : ℕ) → (Fin n → Y) → ℝ) : ℝ :=
  ∫ n, ∫ y, X n y ∂(Measure.pi (fun _ : Fin n => ν)) ∂(poissonMeasure rate)

def uncovered (b : Y → ℝ) (n : ℕ) (y : Fin n → Y) : ℝ := ∏ i, (1-b (y i))

theorem expect_product (rate : ℝ≥0) (ν : Measure Y) [IsProbabilityMeasure ν] (g : Y → ℝ) :
    expect rate ν (fun n y => ∏ i : Fin n, g (y i)) = Real.exp (rate * ((∫ y, g y ∂ν)-1)) := by
  simp only [expect, integral_fintype_prod_eq_pow, Fintype.card_fin, integral_poissonMeasure, smul_eq_mul]
  rw [show (rate : ℝ)*((∫ y, g y ∂ν)-1) = -rate + rate*(∫ y, g y ∂ν) by ring, Real.exp_add]
  have h := (NormedSpace.expSeries_div_hasSum_exp ((rate:ℝ) * (∫ y, g y ∂ν))).mul_left (Real.exp (-rate))
  rw [← Real.exp_eq_exp_ℝ] at h
  rw [← h.tsum_eq]
  apply tsum_congr
  intro n
  rw [mul_pow]
  ring

theorem expect_uncovered (rate : ℝ≥0) {ν : Measure Y} [IsProbabilityMeasure ν]
    {b : Y → ℝ} (hb : Integrable b ν) :
    expect rate ν (uncovered b) = Real.exp (-((rate : ℝ) * ∫ y, b y ∂ν)) := by
  change expect rate ν (fun n y => ∏ i : Fin n, (1-b (y i))) = _
  rw [expect_product rate ν (fun y => 1-b y), integral_sub (integrable_const _) hb, integral_const]
  simp

/-- The two-point expectation contains exactly one overlap integral. -/
theorem expect_uncovered_pair (rate : ℝ≥0) {ν : Measure Y} [IsProbabilityMeasure ν]
    {b c : Y → ℝ} (hb : Integrable b ν) (hc : Integrable c ν)
    (hbc : Integrable (fun y => b y*c y) ν) :
    expect rate ν (fun n y => uncovered b n y * uncovered c n y) =
      Real.exp (-(rate:ℝ) * ((∫ y, b y ∂ν) + ∫ y, c y ∂ν)) *
      Real.exp ((rate:ℝ) * ∫ y, b y*c y ∂ν) := by
  simp only [uncovered, ← Finset.prod_mul_distrib]
  rw [expect_product rate ν (fun y => (1-b y)*(1-c y)), ← Real.exp_add]
  have he (y : Y) : (1-b y)*(1-c y) = ((1-b y)-c y)+b y*c y := by ring
  simp_rw [he]
  erw [integral_add (((integrable_const (1:ℝ)).sub hb).sub hc) hbc,
    integral_sub ((integrable_const _).sub hb) hc, integral_sub (integrable_const _) hb]
  simp
  ring

/-- Integrate the Poisson two-point formula against a spatial kernel.
For the outside indirect Coulomb energy, `Z` is the space of pairs and
`k` is the signed pair-minus-direct integrand. -/
theorem expect_exterior_integral {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [SFinite μ]
    (rate : ℝ≥0) {ν : Measure Y} [IsProbabilityMeasure ν]
    (b c : Z → Y → ℝ) (k h : Z → ℝ) (v : ℝ)
    (hmark : ∀ᵐ z ∂μ, Integrable (b z) ν ∧ Integrable (c z) ν ∧
      Integrable (fun y => b z y*c z y) ν ∧
      (rate:ℝ)*(∫ y, b z y ∂ν) = v ∧ (rate:ℝ)*(∫ y, c z y ∂ν) = v ∧
      (rate:ℝ)*(∫ y, b z y*c z y ∂ν) = v*h z)
    (hfinite : ∀ n, Integrable (fun p : (Fin n → Y) × Z =>
      k p.2*(uncovered (b p.2) n p.1*uncovered (c p.2) n p.1))
      ((Measure.pi (fun _ : Fin n => ν)).prod μ))
    (hcount : Integrable (fun p : ℕ × Z => ∫ y : Fin p.1 → Y,
      k p.2*(uncovered (b p.2) p.1 y*uncovered (c p.2) p.1 y)
      ∂(Measure.pi (fun _ : Fin p.1 => ν))) ((poissonMeasure rate).prod μ)) :
    expect rate ν (fun n y => ∫ z, k z*(uncovered (b z) n y*uncovered (c z) n y) ∂μ) =
      Real.exp (-(2*v))*(∫ z, Real.exp (v*h z)*k z ∂μ) := by
  let F := fun (n : ℕ) (y : Fin n → Y) (z : Z) => k z*(uncovered (b z) n y*uncovered (c z) n y)
  let Q := fun (n : ℕ) (z : Z) => ∫ y, F n y z ∂(Measure.pi (fun _ : Fin n => ν))
  have hswap : expect rate ν (fun n y => ∫ z, F n y z ∂μ) = ∫ z, ∫ n, Q n z ∂(poissonMeasure rate) ∂μ := by
    unfold expect
    calc
      _ = ∫ n, ∫ z, Q n z ∂μ ∂(poissonMeasure rate) :=
        integral_congr_ae (ae_of_all _ fun n => integral_integral_swap (f := F n) (hfinite n))
      _ = _ := integral_integral_swap (f := Q) hcount
  change expect rate ν (fun n y => ∫ z, F n y z ∂μ) = _
  rw [hswap, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hmark] with z hz
  obtain ⟨hb,hc,hbc,hb',hc',hbc'⟩ := hz
  dsimp only [Q,F]
  simp_rw [integral_const_mul]
  change k z*expect rate ν (fun n y => uncovered (b z) n y*uncovered (c z) n y) = _
  rw [expect_uncovered_pair rate hb hc hbc, hbc', neg_mul, mul_add, hb', hc']
  rw [show -(v+v) = -(2*v) by ring]
  ring

/-- Covariance of uncovered cutoffs, also the covariance of their complements.
The estimate retains the actual overlap and vanishes on disjoint mark supports. -/
theorem covariance_le_overlap (rate : ℝ≥0) {ν : Measure Y} [IsProbabilityMeasure ν]
    {b c : Y → ℝ} (hb : Integrable b ν) (hc : Integrable c ν)
    (hbc : Integrable (fun y => b y*c y) ν)
    (hpos : ∀ᵐ y ∂ν, b y ∈ Set.Icc 0 1 ∧ c y ∈ Set.Icc 0 1) :
    let cov := expect rate ν (fun n y => uncovered b n y * uncovered c n y) -
      expect rate ν (uncovered b) * expect rate ν (uncovered c)
    0 ≤ cov ∧ cov ≤ (rate:ℝ) * ∫ y, b y*c y ∂ν := by
  dsimp only
  rw [expect_uncovered_pair rate hb hc hbc, expect_uncovered rate hb, expect_uncovered rate hc,
    ← Real.exp_add (-((rate:ℝ)*∫ y, b y ∂ν)) (-((rate:ℝ)*∫ y, c y ∂ν))]
  let a := (rate:ℝ) * ∫ y, b y*c y ∂ν
  let t := (rate:ℝ) * ((∫ y, b y ∂ν) + ∫ y, c y ∂ν)
  have ha : 0 ≤ a := mul_nonneg rate.coe_nonneg (integral_nonneg_of_ae (hpos.mono fun _ h => mul_nonneg h.1.1 h.2.1))
  have hat : a ≤ t := by
    apply mul_le_mul_of_nonneg_left _ rate.coe_nonneg
    rw [← integral_add hb hc]
    exact integral_mono_ae hbc (hb.add hc) (hpos.mono fun _ h =>
      (mul_le_of_le_one_right h.1.1 h.2.2).trans (le_add_of_nonneg_right h.2.1))
  rw [show -((rate:ℝ)*∫ y, b y ∂ν) + -((rate:ℝ)*∫ y, c y ∂ν) = -t by dsimp [t]; ring,
    show -(rate:ℝ)*((∫ y, b y ∂ν)+(∫ y, c y ∂ν)) = -t by dsimp [t]; ring]
  change 0 ≤ Real.exp (-t) * Real.exp a - Real.exp (-t) ∧ _ ≤ a
  have e : Real.exp (-t) * Real.exp a - Real.exp (-t) = Real.exp (a-t)*(1-Real.exp (-a)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [e]
  have hn : 0 ≤ 1-Real.exp (-a) := sub_nonneg.mpr ((Real.exp_le_one_iff).mpr (by linarith))
  refine ⟨mul_nonneg (Real.exp_pos _).le hn, ?_⟩
  calc
    _ ≤ 1-Real.exp (-a) := mul_le_of_le_one_left hn (Real.exp_le_one_iff.mpr (sub_nonpos.mpr hat))
    _ ≤ a := by linarith only [Real.one_sub_le_exp_neg a]

def coveredMean (s : ℝ) := 1-Real.exp (-s)

private theorem coveredMean_pos {s : ℝ} (hs : 0 < s) : 0 < coveredMean s :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs))

theorem coveredMean_le {s : ℝ} : coveredMean s ≤ s := by
  unfold coveredMean
  linarith only [Real.one_sub_le_exp_neg s]

theorem coveredMean_half {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1) : s/2 ≤ coveredMean s := by
  unfold coveredMean
  rw [Real.exp_neg]
  have hex := Real.add_one_le_exp s
  suffices (Real.exp s)⁻¹ ≤ 1-s/2 by linarith
  rw [← one_div, div_le_iff₀ (Real.exp_pos _)]
  nlinarith only [mul_nonneg (show 0 ≤ 1 - s/2 by linarith) (sub_nonneg.mpr hex),
    mul_nonneg hs.le (sub_nonneg.mpr hs')]

theorem coveredMean_scaled {s a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    a*coveredMean s ≤ coveredMean (a*s) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-s)) (sub_nonneg.mpr ha') ha
    (by ring : 1-a+a=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_neg] at h
  unfold coveredMean
  linarith

/-- The first density correction differs from one by O(δ/r), uniformly
in the Poisson filling fraction. -/
theorem first_correction {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s) (hs' : s ≤ 1/2) :
    let c := coveredMean v / coveredMean (v*(1-s)^3)
    1 ≤ c ∧ c ≤ 1+24*s := by
  let a := (1-s)^3
  have ha : 0 < a := pow_pos (by linarith) _
  have ha' : a ≤ 1 := by dsimp [a]; exact pow_le_one₀ (by linarith) (by linarith)
  have hl : 1/8 ≤ a := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) (by linarith : 1/2 ≤ 1-s) 3
    norm_num at h
    exact h
  have h3 : 1-a ≤ 3*s := by
    dsimp [a]
    nlinarith only [mul_nonneg (sq_nonneg s) (show 0 ≤ 3-s by linarith)]
  have hden := coveredMean_pos (mul_pos hv ha)
  change 1 ≤ coveredMean v / coveredMean (v*a) ∧ _ ≤ _
  refine ⟨(one_le_div hden).mpr ?_, (div_le_iff₀ hden).mpr ?_⟩
  · unfold coveredMean
    exact sub_le_sub_left (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hv.le (sub_nonneg.mpr ha')])) _
  · have h := coveredMean_scaled (s := v) ha.le ha'
    rw [mul_comm a v] at h
    have hcoeff : 1 ≤ (1+24*s)*a := by nlinarith only [mul_nonneg hs (sub_nonneg.mpr hl), h3]
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff (coveredMean_pos hv).le,
      mul_le_mul_of_nonneg_left h (show 0 ≤ 1+24*s by linarith)]

/-- The mean density of the two corrected island populations is the desired sum. -/
theorem corrected_mean {v m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    Real.exp (-v) + coveredMean v/m₁*m₁ = 1 ∧ (1/m₂)*m₂ = 1 := by
  simp [coveredMean, h₁, h₂]

end TSGA.Islands
