import TSGA.RayRegularity
import TSGA.OrderedScale

/-! # The matrix Hölder estimate at the polarization boundary

The common upper matrix B + ‖A-B‖HS I dominates A. Scaling it back to
the trace of B produces a mixture of B and the unpolarized matrix.
This converts the one-sided removal estimate into a two-sided estimate.
-/

noncomputable section

namespace TSGA.SSW

open TSGA.Localization
open scoped ComplexOrder Matrix.Norms.Frobenius

private theorem growth_nonnegative {r : ℝ} (hr : 0 ≤ r) (q : Position) : 0 ≤ holderGrowth r q := by
  unfold holderGrowth
  positivity

private theorem growth_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (q : Position) :
    holderGrowth r q ≤ holderGrowth s q :=
  add_le_add (add_le_add (Real.rpow_le_rpow hr hrs (by norm_num)) (Real.rpow_le_rpow hr hrs (by norm_num)))
    (mul_le_mul_of_nonneg_right hrs (sq_nonneg _))

private theorem growth_five {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hsr : s ≤ 5*r) (q : Position) :
    holderGrowth s q ≤ 25*holderGrowth r q := by
  apply (growth_mono hs hsr q).trans
  unfold holderGrowth
  have h (a : ℝ) (ha : a ≤ 2) : (5:ℝ)^a ≤ 25 := by
    simpa only [Real.rpow_two, show (5:ℝ)^2 = 25 by norm_num] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 5) ha
  rw [Real.mul_rpow (by norm_num) hr, Real.mul_rpow (by norm_num) hr]
  linarith only [mul_le_mul_of_nonneg_right (h (4/3) (by norm_num)) (Real.rpow_nonneg hr (4/3)),
    mul_le_mul_of_nonneg_right (h (5/3) (by norm_num)) (Real.rpow_nonneg hr (5/3)),
    mul_nonneg hr (sq_nonneg ‖q‖)]

theorem FiniteRateTiling.abs_le_holderGrowth {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (rate : FiniteRateTiling E η K) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position) :
    |sswEnergy E η M q| ≤ K*holderGrowth M.trace.re q := by
  let r := M.trace.re
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have he : holderGrowth r q = r * rateGrowth r q := by
    rcases hr.eq_or_lt with hz | hp
    · simp [← hz, holderGrowth, Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0)]
    · exact holderGrowth_eq hp q
  obtain ⟨hl, hu⟩ := rate.ssw_power_bounds hM q
  change |sswEnergy E η M q| ≤ K*holderGrowth r q
  rw [he]
  apply abs_le.mpr ⟨_, hu⟩
  have h := mul_le_mul_of_nonneg_left (show r^(1/3:ℝ) ≤ rateGrowth r q by
    unfold rateGrowth
    linarith only [Real.rpow_nonneg hr (2/3:ℝ), sq_nonneg ‖q‖]) hr
  change -K * (r * r ^ (1/3:ℝ)) ≤ _ at hl
  linarith only [hl, mul_le_mul_of_nonneg_left h (zero_le_one.trans rate.one_le)]

private theorem linear_le_cube_root {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 2) :
    x ≤ 2*x^(1/3:ℝ) := by
  by_cases hx1 : x ≤ 1
  · have h := Real.self_le_rpow_of_le_one hx hx1 (by norm_num : (1/3:ℝ) ≤ 1)
    linarith only [h, hx]
  · linarith only [hx', Real.one_le_rpow (le_of_not_ge hx1) (by norm_num : (0:ℝ) ≤ 1/3)]

private theorem upper_matrix_interpolation (e : SpinMatrix → ℝ) {B : SpinMatrix} (hB : B.PosSemidef)
    {s d : ℝ} (hs : 0 < s) (hd : 0 ≤ d) (hsum : s = B.trace.re + 2*d)
    (conv : ∀ t : ℝ, 0 < t → ConvexOn ℝ (fixedCharge t) e)
    {T : ℝ} (hT : ∀ {P : SpinMatrix}, P ∈ fixedCharge B.trace.re → |e P| ≤ T) :
    e ((B.trace.re/s) • (B + d • (1:SpinMatrix))) - e B ≤ 2*(1-B.trace.re/s)*T := by
  let t := B.trace.re
  let α := t/s
  have ht : 0 ≤ t := (RCLike.nonneg_iff.mp hB.trace_nonneg).1
  have ha : 0 ≤ α := div_nonneg ht hs.le
  have has : α*s = t := div_mul_cancel₀ _ hs.ne'
  have ha' : α ≤ 1 := (div_le_one hs).2 (by change B.trace.re ≤ s; linarith only [hsum,hd])
  let P := (t/2) • (1 : SpinMatrix)
  have hP : P ∈ fixedCharge t := by
    refine ⟨Matrix.PosSemidef.one.smul (div_nonneg ht (by norm_num)), ?_⟩
    simp [P, Matrix.trace_smul, Complex.real_smul]
  have mix : α • B + (1-α) • P = α • (B+d • (1:SpinMatrix)) := by
    have h : (1-α)*(t/2) = α*d := by
      change s = t+2*d at hsum
      rw [hsum] at has
      linarith only [has]
    simp only [P, smul_add, smul_smul, h]
  have hc : e (α • B + (1-α) • P) ≤ α*e B + (1-α)*e P := by
    rcases ht.eq_or_lt with hz | ht'
    · have heq := hB.trace_eq_zero_iff.mp (Complex.ext hz.symm (RCLike.nonneg_iff.mp hB.trace_nonneg).2)
      simp [α, ← hz, P, heq]
    · exact (conv t ht').2 ⟨hB,rfl⟩ hP ha (sub_nonneg.mpr ha') (by ring)
  rw [mix] at hc
  have hdiff : e P-e B ≤ 2*T := by
    linarith only [(abs_le.mp (hT hP)).2, (abs_le.mp (hT (P := B) ⟨hB,rfl⟩)).1]
  change e (α • _) - e B ≤ 2*(1-α)*T
  linarith only [hc, mul_le_mul_of_nonneg_left hdiff (sub_nonneg.mpr ha')]

private theorem directional_holder (e : SpinMatrix → ℝ) (q : Position) {K C R : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (power : ∀ {P : SpinMatrix}, P.PosSemidef → |e P| ≤ K*holderGrowth P.trace.re q)
    (conv : ∀ t : ℝ, 0 < t → ConvexOn ℝ (fixedCharge t) e)
    (ray : ∀ {P : SpinMatrix}, P.PosSemidef → ∀ {a : ℝ}, 0 ≤ a → a ≤ 1 →
      |e (a • P) - e P| ≤ R*(1-a)*holderGrowth P.trace.re q)
    (ordered : ∀ {P Q : SpinMatrix}, P.PosSemidef → (Q-P).PosSemidef → 0 < Q.trace.re →
      e P - e Q ≤ C*holderGrowth Q.trace.re q*((Q.trace.re-P.trace.re)/Q.trace.re)^(1/3:ℝ))
    {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) (hr : 0 < max A.trace.re B.trace.re) :
    let r := max A.trace.re B.trace.re
    e A-e B ≤ (100*C+100*R+8*K)*holderGrowth r q*(hilbertSchmidt (A-B)/r)^(1/3:ℝ) := by
  let r := max A.trace.re B.trace.re
  let d := hilbertSchmidt (A-B)
  let Z := B + d • (1:SpinMatrix)
  let s := Z.trace.re
  let u := d/r
  let w := u^(1/3:ℝ)
  let G := holderGrowth r q
  have ha := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  have hb := (RCLike.nonneg_iff.mp hB.trace_nonneg).1
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hZ : Z.PosSemidef := hB.add (Matrix.PosSemidef.one.smul hd)
  have hZtr : s = B.trace.re + 2*d := by
    simp [s,Z,Matrix.trace_add,Matrix.trace_smul,Complex.real_smul, mul_comm]
  have hcomm : hilbertSchmidt (B-A) = d := hs_sub_comm B A
  have hZA : (Z-A).PosSemidef := by
    have h := hilbertSchmidt_shift_posSemidef (hB.isHermitian.sub hA.isHermitian)
    rw [hcomm, show d • (1:SpinMatrix)+(B-A)=Z-A by unfold Z; abel] at h
    exact h
  have htr : 0 ≤ (Z-A).trace.re := (RCLike.nonneg_iff.mp hZA.trace_nonneg).1
  rw [Matrix.trace_sub, Complex.sub_re] at htr
  change 0 ≤ s - A.trace.re at htr
  have hrs : r ≤ s := max_le (by linarith only [htr]) (by linarith only [hZtr,hd])
  have hs := hr.trans_le hrs
  have hd2 : d ≤ 2*r := by
    have htriangle : d ≤ hilbertSchmidt A + hilbertSchmidt B := by
      change hilbertSchmidt (A-B) ≤ _
      simpa only [hs_eq_norm] using norm_sub_le A B
    linarith only [htriangle, hilbertSchmidt_le_trace hA, hilbertSchmidt_le_trace hB,
      le_max_left A.trace.re B.trace.re, le_max_right A.trace.re B.trace.re]
  have hu : 0 ≤ u := div_nonneg hd hr.le
  have hur := div_mul_cancel₀ d hr.ne'
  change u*r=d at hur
  have huw : u ≤ 2*w := linear_le_cube_root hu ((div_le_iff₀ hr).2 hd2)
  have hwu := Real.rpow_nonneg hu (1/3:ℝ)
  have hG : 0 ≤ G := growth_nonnegative hr.le q
  have hGs : holderGrowth s q ≤ 25*G := growth_five hs.le hr.le (by
    linarith only [hZtr,hd2,le_max_right A.trace.re B.trace.re]) q
  have hdelta := abs_trace_re_le_hilbertSchmidt (B-A)
  rw [Matrix.trace_sub,Complex.sub_re,hcomm] at hdelta
  have hf : (s-A.trace.re)/s ≤ 4*u := (div_le_iff₀ hs).2 (by
    linarith only [hZtr,(abs_le.mp hdelta).2,hur,mul_le_mul_of_nonneg_left hrs hu])
  have hpow : ((s-A.trace.re)/s)^(1/3:ℝ) ≤ 4*w := by
    apply (Real.rpow_le_rpow (div_nonneg (by linarith only [htr]) hs.le) hf (by norm_num)).trans
    rw [Real.mul_rpow (by norm_num) hu]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) hwu
  have h1 := ordered hA hZA hs
  change e A-e Z ≤ C*holderGrowth s q*((s-A.trace.re)/s)^(1/3:ℝ) at h1
  have h1' := h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left hGs hC) hpow
    (Real.rpow_nonneg (div_nonneg (by linarith only [htr]) hs.le) _) (by positivity))
  let α := B.trace.re/s
  have hα : 0 ≤ α := div_nonneg hb hs.le
  have hα' : α ≤ 1 := (div_le_one hs).2 (by linarith only [hZtr,hd])
  have hfrac : 1-α ≤ 4*w := by
    have has : α*s = B.trace.re := div_mul_cancel₀ _ hs.ne'
    have hh : 1-α ≤ 2*u := (le_of_mul_le_mul_right (a := s) (by
      linarith only [has,hZtr,hur,mul_le_mul_of_nonneg_left hrs hu]) hs)
    linarith only [hh,huw]
  have h2 := (abs_le.mp (ray hZ hα hα')).1
  have h2' : R*(1-α)*holderGrowth s q ≤ R*(4*w)*(25*G) := mul_le_mul
    (mul_le_mul_of_nonneg_left hfrac hR) hGs (growth_nonnegative hs.le q) (by positivity)
  have h3 := upper_matrix_interpolation e hB hs hd hZtr conv (T := K*G) (fun {P} hP =>
    (power hP.1).trans (mul_le_mul_of_nonneg_left (hP.2 ▸ growth_mono hb (le_max_right _ _) q) hK))
  change e (α • Z)-e B ≤ 2*(1-α)*(K*G) at h3
  have h3' := mul_le_mul_of_nonneg_right hfrac (mul_nonneg hK hG)
  change e A-e B ≤ (100*C+100*R+8*K)*G*w
  linarith only [h1',h2,h2',h3,h3']

/-- Arbitrary positive matrices, including rank-one matrices and a vacuum endpoint. -/
theorem holder_of_ordered_and_ray (e : SpinMatrix → ℝ) (q : Position) {K C R : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (power : ∀ {P : SpinMatrix}, P.PosSemidef → |e P| ≤ K*holderGrowth P.trace.re q)
    (conv : ∀ t : ℝ, 0 < t → ConvexOn ℝ (fixedCharge t) e)
    (ray : ∀ {P : SpinMatrix}, P.PosSemidef → ∀ {a : ℝ}, 0 ≤ a → a ≤ 1 →
      |e (a • P) - e P| ≤ R*(1-a)*holderGrowth P.trace.re q)
    (ordered : ∀ {P Q : SpinMatrix}, P.PosSemidef → (Q-P).PosSemidef → 0 < Q.trace.re →
      e P-e Q ≤ C*holderGrowth Q.trace.re q*((Q.trace.re-P.trace.re)/Q.trace.re)^(1/3:ℝ))
    {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) (hr : 0 < max A.trace.re B.trace.re) :
    let r := max A.trace.re B.trace.re
    |e A-e B| ≤ (100*C+100*R+8*K)*holderGrowth r q*(hilbertSchmidt (A-B)/r)^(1/3:ℝ) := by
  have h₁ := directional_holder e q hK hC hR power conv ray ordered hA hB hr
  have h₂ := directional_holder e q hK hC hR power conv ray ordered hB hA (by simpa only [max_comm B.trace.re A.trace.re] using hr)
  rw [max_comm B.trace.re A.trace.re, hs_sub_comm B A] at h₂
  exact abs_le.mpr ⟨by linarith only [h₂], h₁⟩

end TSGA.SSW
