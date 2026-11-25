import TSGA.BallDensityRepresentative
import TSGA.ComparisonMatrices

/-! # Charge and spectral oscillation on a small comparison ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization Metric Set Matrix
open scoped ComplexOrder MatrixOrder

theorem density_power_one (N : Density) (x : Position) : N.power 1 x = N.matrix x := by
  unfold Density.power
  simp only [Real.rpow_one]
  change (N.positive x).1.cfc id = _
  rw [← (N.positive x).1.cfc_eq, cfc_id ℝ _ (N.positive x).1.isSelfAdjoint]

/-- Each oscillation is attained by a pair in the closed comparison ball. -/
structure SmallBallScale (N : Density) (R : ℝ) (c : Position) where
  r : ℝ
  peak : ∃ z ∈ closedBall c R, N.charge z = r
  cap : ∀ x ∈ closedBall c R, N.charge x ≤ r
  omega : ℝ → ℝ
  omega_max : ∀ a, 0 < a → ∃ x ∈ closedBall c R, ∃ y ∈ closedBall c R,
    omega a = hilbertSchmidt (N.power a x - N.power a y)
  osc : ∀ a, 0 < a → ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
    hilbertSchmidt (N.power a x - N.power a y) ≤ omega a
  small : omega 1 ≤ r/64

namespace SmallBallScale
variable {N : Density} {R : ℝ} {c : Position} (s : SmallBallScale N R c)

theorem r_nonneg : 0 ≤ s.r := by
  obtain ⟨z, _, hz⟩ := s.peak
  exact hz ▸ N.charge_nonneg z

theorem omega_nonneg (a : ℝ) (ha : 0 < a) : 0 ≤ s.omega a := by
  obtain ⟨x, _, y, _, h⟩ := s.omega_max a ha
  rw [h]
  exact Real.sqrt_nonneg _

theorem matrix_osc {x y : Position} (hx : x ∈ closedBall c R) (hy : y ∈ closedBall c R) :
    hilbertSchmidt (N.matrix x - N.matrix y) ≤ s.omega 1 := by
  simpa only [density_power_one] using s.osc 1 zero_lt_one x hx y hy

theorem comparable (x : Position) (hx : x ∈ closedBall c R) : s.r/2 ≤ N.charge x := by
  obtain ⟨z,hz,he⟩ := s.peak
  have h := (SSW.abs_trace_re_le_hilbertSchmidt (N.matrix z-N.matrix x)).trans
    (mul_le_mul_of_nonneg_left (s.matrix_osc hz hx) (by norm_num : (0:ℝ) ≤ 2))
  rw [Matrix.trace_sub, Complex.sub_re] at h
  change |N.charge z-N.charge x| ≤ _ at h
  linarith only [(abs_le.mp h).2, he, s.small, s.r_nonneg]

/-- The actual full-matrix oscillation can be estimated by any sublinear
power. For the shifted construction this permits a single shift at all powers. -/
theorem omega_one_le (a : ℝ) (ha : 0 < a) (hle : a ≤ 1) :
    s.omega 1 ≤ (1/a*s.r^(1-a))*s.omega a := by
  obtain ⟨x,hx,y,hy,h⟩ := s.omega_max 1 zero_lt_one
  rw [h]
  exact (matrix_power_oscillation (N.positive x) (N.positive y) ha hle s.r_nonneg
    (s.cap x hx) (s.cap y hy)).trans (mul_le_mul_of_nonneg_left (s.osc _ ha x hx y hy)
      (mul_nonneg (one_div_nonneg.mpr ha.le) (Real.rpow_nonneg s.r_nonneg _)))

private theorem power_bound {a : ℝ} (ha : 0 < a) {x : Position} (hx : x ∈ closedBall c R) :
    hilbertSchmidt (N.power a x) ≤ 2*s.r^a := by
  let h := (N.positive x).1
  let v := h.eigenvalues
  have ht : N.charge x = v 0 + v 1 := by
    change (N.matrix x).trace.re = _
    rw [h.trace_eq_sum_eigenvalues, Fin.sum_univ_two, Complex.add_re]
    rfl
  have eig (i : Fin 2) : v i ≤ s.r := by
    have cap := s.cap x hx
    rw [ht] at cap
    have hn (j : Fin 2) : 0 ≤ v j := (N.positive x).eigenvalues_nonneg _
    fin_cases i
    · change v 0 ≤ _
      linarith only [cap, hn 1]
    · change v 1 ≤ _
      linarith only [cap, hn 0]
  let b := fun i => v i ^ a
  have hn (i : Fin 2) : 0 ≤ b i := Real.rpow_nonneg ((N.positive x).eigenvalues_nonneg _) _
  have hpower : N.power a x = inSpinFrame h.eigenvectorUnitary b := by
    simp only [Density.power, Matrix.IsHermitian.cfc, inSpinFrame, h, b, v,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
  rw [hpower]
  have t := SSW.hilbertSchmidt_le_trace (inSpinFrame_pos h.eigenvectorUnitary hn)
  rw [inSpinFrame_trace] at t
  have pair (i : Fin 2) : b i ≤ s.r^a := Real.rpow_le_rpow ((N.positive x).eigenvalues_nonneg _) (eig i) ha.le
  linarith only [t,pair 0,pair 1]

open scoped Matrix.Norms.Frobenius in
theorem omega_le (a : ℝ) (ha : 0 < a) : s.omega a ≤ 4*s.r^a := by
  obtain ⟨x,hx,y,hy,h⟩ := s.omega_max _ ha
  have hl := s.power_bound ha hx
  have hr := s.power_bound ha hy
  rw [h, SSW.hs_eq_norm]
  rw [SSW.hs_eq_norm] at hl hr
  linarith only [norm_sub_le (N.power a x) (N.power a y), hl, hr]

theorem root_ratio_le {p : ℝ} (hp : 0 < p) : s.omega (1/p)/s.r^(1/p) ≤ 4 := by
  rcases s.r_nonneg.eq_or_lt with h | h
  · rw [← h,Real.zero_rpow (one_div_pos.mpr hp).ne', div_zero]; norm_num
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos h _)).2 (s.omega_le _ (one_div_pos.mpr hp))

end SmallBallScale

/-- Use the original essential test to select maxima on the representative.
The threshold θ/64 makes the full-matrix oscillation at most r/64. -/
theorem smallBallScale_of_regular {N D : Density} {c : Position} {R θ κ : ℝ}
    (e : N.matrix =ᵐ[volume] D.matrix) (hc : Continuous N.matrix)
    (cp : ∀ a : ℝ, 0 < a → Continuous (N.power a)) (hR : 0 < R)
    (hθ : 0 < θ) (hle : θ ≤ 1) (hk : κ ≤ θ/64) (hs : SmallPowerOscillation D θ κ R c) :
    ∃ s : SmallBallScale N R c, s.omega θ ≤ κ*s.r^θ := by
  classical
  let B := closedBall c R
  have hB : IsCompact B := isCompact_closedBall c R
  have hm : c ∈ B := mem_closedBall_self hR.le
  obtain ⟨z,hz,hzsup,cap⟩ := exists_charge_max_on_ball (c := c) e hc hR
  let r := N.charge z
  have hr : 0 ≤ r := N.charge_nonneg _
  let f := fun a (v : Position × Position) => hilbertSchmidt (N.power a v.1-N.power a v.2)
  have maxpair (a : ℝ) (ha : 0 < a) :
      ∃ v ∈ B ×ˢ B, IsMaxOn (f a) (B ×ˢ B) v := by
    apply (hB.prod hB).exists_isMaxOn ⟨(c,c),hm,hm⟩
    have hh : Continuous hilbertSchmidt := by unfold hilbertSchmidt; fun_prop
    exact (hh.comp (((cp a ha).comp continuous_fst).sub ((cp a ha).comp continuous_snd))).continuousOn
  let pair (a : ℝ) := if h : 0 < a then (maxpair a h).choose else (c,c)
  have atpair (a : ℝ) (ha : 0 < a) : pair a ∈ B ×ˢ B ∧ IsMaxOn (f a) (B ×ˢ B) (pair a) := by
    simpa only [pair,dite_eq_left ha] using (maxpair a ha).choose_spec
  let ω := fun a => f a (pair a)
  have osc a (ha : 0 < a) x (hx : x ∈ B) y (hy : y ∈ B) : f a (x,y) ≤ ω a :=
    isMaxOn_iff.mp (atpair a ha).2 (x,y) ⟨hx,hy⟩
  have smallθ : ω θ ≤ κ*r^θ := by
    have h := ((smallPowerOscillation_iff_closedBall e hc (cp _ hθ) hR).mp hs)
      _ (atpair _ hθ).1.1 _ (atpair _ hθ).1.2
    simpa only [r,hzsup] using h
  have prod : r^(1-θ)*r^θ = r := by
    rcases hr.eq_or_lt with h | h
    · simp [← h,Real.zero_rpow hθ.ne']
    · rw [← Real.rpow_add h,sub_add_cancel,Real.rpow_one]
  let x := (pair 1).1
  let y := (pair 1).2
  have hx := (atpair 1 zero_lt_one).1.1
  have hy := (atpair 1 zero_lt_one).1.2
  have coef : 0 ≤ 1/θ*r^(1-θ) := mul_nonneg (one_div_nonneg.mpr hθ.le) (Real.rpow_nonneg hr _)
  have h : ω 1 ≤ (1/θ*r^(1-θ))*(κ*r^θ) :=
    (matrix_power_oscillation (N.positive x) (N.positive y) hθ hle hr (cap x hx) (cap y hy)).trans
      (mul_le_mul_of_nonneg_left ((osc θ hθ x hx y hy).trans smallθ) coef)
  have eprod : (1/θ*r^(1-θ))*(κ*r^θ) = (κ/θ)*r := by
    calc
      _ = (κ/θ)*(r^(1-θ)*r^θ) := by ring
      _ = _ := by rw [prod]
  have frac : κ/θ ≤ 1/64 := (div_le_iff₀ hθ).2 (by linarith only [hk])
  have small₁ : ω 1 ≤ r/64 := by linarith only [h,eprod,mul_le_mul_of_nonneg_right frac hr]
  exact ⟨⟨r,⟨z,hz,rfl⟩,cap,ω,fun a ha =>
    ⟨_,(atpair a ha).1.1,_,(atpair a ha).1.2,rfl⟩,osc,small₁⟩,smallθ⟩

end TSGA.ManyBody
