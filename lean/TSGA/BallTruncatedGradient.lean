import TSGA.PhaseTruncation
import TSGA.PowerOscillation
import TSGA.RayRegularity

/-! # Weak gradient of the truncated phase density

The two compositions below use the local Sobolev Lipschitz chain rule. The
positive threshold puts the closed support of the product inside the active
set, where the matrix root has a weak derivative. -/

noncomputable section
namespace TSGA.PhaseLocalization

open MeasureTheory Set TSGA.Localization Metric
open scoped ComplexOrder

/-- Local Sobolev calculus for finite dimensional fields. The first two rules
are Lipschitz composition, written on the image of the original field. The
other two are the locally bounded Leibniz rule and locality
across the complement of the closed support. -/
structure TruncationSobolevCalculus : Prop where
  matrix_chain : ∀ {U : Set Position} {F : Position → SpinMatrix} {G : MatrixGradient}
    {f : Position → ℝ} {p L : ℝ}, IsOpen U → 1 ≤ p → 0 ≤ L →
    (∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ IsMatrixGradientOn (ball x r) F G ∧
      (∀ j k, MemLp (fun y => F y j k) (ENNReal.ofReal p) (volume.restrict (ball x r))) ∧
      MemLp (matrixGradNorm G) (ENNReal.ofReal p) (volume.restrict (ball x r))) →
    (∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ L * hilbertSchmidt (F x - F y)) →
    ∃ A : Position → Position, (∀ i, WeakPartialOn U i f (fun x => A x i)) ∧
      ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ L * matrixGradNorm G x
  vector_chain : ∀ {F : Position → Position} {H : Position → Fin 3 → Fin 3 → ℝ}
    {f : Position → ℝ} {p L : ℝ}, 1 ≤ p → 0 ≤ L →
    (∀ i, LocalLpOn univ p fun x => F x i) → (∀ i j, LocalLpOn univ p fun x => H x i j) →
    (∀ i j, WeakPartialOn univ i (fun x => F x j) (fun x => H x i j)) →
    (∀ x y, |f x - f y| ≤ L * ‖F x - F y‖) →
    ∃ B : Position → Position, (∀ i, WeakPartialOn univ i f (fun x => B x i)) ∧
      ∀ᵐ x, ‖B x‖ ≤ L * Real.sqrt (∑ i, ∑ j, H x i j ^ 2)
  leibniz : ∀ {U : Set Position} {i : Fin 3} {f v a b : Position → ℝ}, IsOpen U →
    ContinuousOn f U → ContinuousOn v U → WeakPartialOn U i f a → WeakPartialOn U i v b →
    WeakPartialOn U i (fun x => f x * v x) (fun x => v x * a x + f x * b x)
  extend_zero : ∀ {U : Set Position} {i : Fin 3} {f a : Position → ℝ}, IsOpen U →
    tsupport f ⊆ U → WeakPartialOn U i f a → WeakPartialOn univ i f (U.indicator a)

/-- A test function supported in the smaller set, together with its derivative,
vanishes on the part removed from the integration domain. -/
theorem weakPartialOn_restrict {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U V : Set Position} {i : Fin 3} {f a : Position → F} (hU : MeasurableSet U)
    (hVU : V ⊆ U) (h : WeakPartialOn U i f a) : WeakPartialOn V i f a := by
  refine ⟨h.1.mono_set hVU, h.2.1.mono_set hVU, ?_⟩
  intro ψ hψ hcompact hs
  have restrictTest (k : Position → F) (hk : ∀ x ∉ tsupport ψ, k x = 0) :
      (∫ x in U, k x) = ∫ x in V, k x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hVU (fun x hx => hk x (fun h => hx.2 (hs h)))
  have hw := h.2.2 ψ hψ hcompact (hs.trans hVU)
  rwa [restrictTest (fun x => (fderiv ℝ ψ x (PiLp.single 2 i 1)) • f x)
    (fun x hx => by simp [fderiv_of_notMem_tsupport ℝ hx]),
    restrictTest (fun x => ψ x • a x) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])] at hw

private theorem chargeRoot_ordered {D : Density} {x y : Position} {p : ℝ}
    (hp : 1 ≤ p) (hxy : D.charge x ≤ D.charge y) :
    D.charge y^(1/p) - D.charge x^(1/p) ≤
      2*p * hilbertSchmidt (D.power (1/p) x - D.power (1/p) y) := by
  let a := 1/p
  let r := D.charge y
  let s := D.charge x
  let d := hilbertSchmidt (D.power a x - D.power a y)
  have hp₀ : 0 < p := by linarith
  have ha : 0 < a := one_div_pos.mpr hp₀
  have ha₁ : a ≤ 1 := (div_le_one hp₀).2 hp
  have hs : 0 ≤ s := D.charge_nonneg x
  have hr : 0 ≤ r := D.charge_nonneg y
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  change r^a - s^a ≤ 2*p*d
  rcases hr.eq_or_lt with hz | hpos
  · have hs₀ : s = 0 := le_antisymm (hxy.trans hz.ge) hs
    rw [← hz, hs₀, sub_self]
    positivity
  have hm := matrix_power_oscillation (D.positive x) (D.positive y) (u := 1) ha ha₁ hr hxy le_rfl
  have one {M : SpinMatrix} (hM : M.PosSemidef) : hM.1.cfc (fun t => t^(1:ℝ)) = M := by
    simp only [Real.rpow_one]
    change hM.1.cfc id = _
    rw [← hM.1.cfc_eq, cfc_id ℝ M hM.1.isSelfAdjoint]
  rw [one (D.positive x), one (D.positive y), show 1/a = p by simp [a]] at hm
  have ht := SSW.abs_trace_re_le_hilbertSchmidt (D.matrix x - D.matrix y)
  rw [Matrix.trace_sub, Complex.sub_re] at ht
  change |s-r| ≤ _ at ht
  rw [abs_of_nonpos (sub_nonpos.mpr (show s ≤ r from hxy))] at ht
  change _ ≤ p*r^(1-a)*d at hm
  have hgap : r-s ≤ 2*(p*r^(1-a)*d) := by linarith only [ht, hm]
  have hrs : r^a*r^(1-a) = r := by rw [← Real.rpow_add hpos, show a + (1-a) = 1 by ring, Real.rpow_one]
  have hss : s ≤ s^a*r^(1-a) := by
    rcases hs.eq_or_lt with hz | hpos'
    · rw [← hz, Real.zero_rpow ha.ne', zero_mul]
    calc s = s^a*s^(1-a) := by rw [← Real.rpow_add hpos', show a + (1-a) = 1 by ring, Real.rpow_one]
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hxy (sub_nonneg.mpr ha₁))
           (Real.rpow_nonneg hs _)
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hpos (1-a))).1
  rw [sub_mul, hrs]
  linarith only [hgap,hss]

theorem chargeRoot_lipschitz (D : Density) {p : ℝ} (hp : 1 ≤ p) (x y : Position) :
    |D.charge x^(1/p) - D.charge y^(1/p)| ≤
      2*p * hilbertSchmidt (D.power (1/p) x - D.power (1/p) y) := by
  have hp' : 0 ≤ 1/p := by positivity
  rcases le_total (D.charge x) (D.charge y) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_rpow (D.charge_nonneg x) h hp')), neg_sub]
    exact chargeRoot_ordered hp h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow (D.charge_nonneg y) h hp')),
      SSW.hs_sub_comm]
    exact chargeRoot_ordered hp h

private theorem truncation_support {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) {φ : Phase}
    (hc : Continuous φ.grad) {v : Position → ℝ} (hv : ∀ x, 0 ≤ v x)
    (cap : ∀ x, v x ≤ ‖φ.grad x‖) :
    tsupport (fun x => truncatedSpeed p ε (v x)) ⊆ φ.active := by
  have he : 0 < 2/p := div_pos (by norm_num) hp
  have hs : Continuous (fun x => ‖φ.grad x‖ ^ (2/p)) := hc.norm.rpow_const (fun _ => Or.inr he.le)
  have closed : IsClosed {x | ε ^ (1/p) ≤ ‖φ.grad x‖ ^ (2/p)} := isClosed_le continuous_const hs
  apply (closure_minimal (t := {x | ε ^ (1/p) ≤ ‖φ.grad x‖ ^ (2/p)}) _ closed).trans
  · intro x hx hz
    change φ.grad x = 0 at hz
    change ε ^ (1/p) ≤ ‖φ.grad x‖ ^ (2/p) at hx
    rw [hz, norm_zero, Real.zero_rpow he.ne'] at hx
    exact (Real.rpow_pos_of_pos hε _).not_ge hx
  · intro x hx
    change ε^(1/p) ≤ ‖φ.grad x‖^(2/p)
    apply le_of_not_gt
    intro h
    exact hx (max_eq_left (sub_nonpos.mpr ((Real.rpow_le_rpow (hv x) (cap x) he.le).trans h.le)))

private theorem weighted_sum_power {p a b z : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : 0 ≤ z) (h : z ≤ 2*p*a+b) : z^p ≤ (4*p)^p*(a^p+b^p) := by
  have hp₀ : 0 ≤ p := by linarith
  have h4 : 0 ≤ 4*p := by positivity
  have hm : 0 ≤ max a b := ha.trans (le_max_left ..)
  have h' : z ≤ (4*p)*max a b := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left a b) (by positivity : 0 ≤ 2*p)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ 2*p) hm
    linarith only [h, h1, h2, le_max_right a b]
  apply (Real.rpow_le_rpow hz h' hp₀).trans
  rw [Real.mul_rpow h4 hm]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg h4 _)
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  · rw [max_eq_left hba]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)

/-- A nonnegative 1-Lipschitz function of the wavevector, bounded by its
norm, can be truncated with the same weighted gradient bound. -/
theorem truncatedSpeedProduct_gradient (calcRules : TruncationSobolevCalculus)
    {D : Density} {φ : Phase} {G : MatrixGradient} {p ε : ℝ} (hp : 3 < p) (hε : 0 < ε)
    (hφ : PhaseAdmissible D p φ G) (hc : Continuous D.charge)
    (speed : Position → ℝ) (lip : LipschitzWith 1 speed)
    (range : ∀ v, speed v ∈ Icc 0 ‖v‖) :
    ∃ Z : Position → Position, (∀ U, IsOpen U → ∀ i,
      WeakPartialOn U i (fun x => D.charge x^(1/p) * truncatedSpeed p ε (speed (φ.grad x)))
        (fun x => Z x i)) ∧ MemLp Z (ENNReal.ofReal p) ∧ ∀ K : Set Position,
      (∫ x in K, ‖Z x‖^p) ≤ (4*p)^p*((∫ x in K, weightedRoot φ G p x) +
        ε^(1-p/2)*∫ x in K, D.charge x*φ.hessianNorm x^p) := by
  classical
  let u := fun x => D.charge x^(1/p)
  let v := fun x => truncatedSpeed p ε (speed (φ.grad x))
  let L : ℝ := truncationSlope p ε
  have hU := hφ.regular.isOpen_active
  have hp₀ : 0 < p := by linarith
  have hp₁ : 1 ≤ p := by linarith
  have hu (x) : 0 ≤ u x := Real.rpow_nonneg (D.charge_nonneg x) _
  have hv (x) : 0 ≤ v x := le_max_left ..
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hlip := truncatedSpeed_lipschitz (by linarith : 2 ≤ p) hε
  have hvc : Continuous v := hlip.continuousOn.comp_continuous (lip.continuous.comp hφ.regular.continuous_grad)
    (fun x => (range _).1)
  have huc : Continuous u := hc.rpow_const (fun _ => Or.inr (by positivity))
  obtain ⟨A, hA, boundA⟩ := calcRules.matrix_chain (f := u) hU hp₁ (by positivity : 0 ≤ 2*p)
    hφ.root_regular (fun x _ y _ => chargeRoot_lipschitz D hp₁ x y)
  obtain ⟨B, hB, boundB⟩ := calcRules.vector_chain (f := v) hp₁ hL hφ.regular.grad_Lp
    hφ.regular.hessian_Lp hφ.regular.weak_hessian (fun x y => by
      have h := (lipschitzOnWith_iff_dist_le_mul.mp hlip) _ (range (φ.grad x)).1 _ (range (φ.grad y)).1
      simp only [Real.dist_eq] at h
      have diff : |speed (φ.grad x) - speed (φ.grad y)| ≤ ‖φ.grad x - φ.grad y‖ := by
        simpa [Real.dist_eq, dist_eq_norm] using lip.dist_le_mul (φ.grad x) (φ.grad y)
      exact h.trans (mul_le_mul_of_nonneg_left diff hL))
  let Z := φ.active.indicator (fun x => v x • A x + u x • B x)
  have support : tsupport (fun x => u x * v x) ⊆ φ.active :=
    tsupport_mul_subset_right.trans (truncation_support hp₀ hε hφ.regular.continuous_grad
      (fun x => (range _).1) (fun x => (range _).2))
  have weak (i) : WeakPartialOn univ i (fun x => u x * v x) (fun x => Z x i) := by
    have prod := calcRules.leibniz hU huc.continuousOn hvc.continuousOn (hA i)
      (weakPartialOn_restrict MeasurableSet.univ (subset_univ _) (hB i))
    have ext := calcRules.extend_zero hU support prod
    convert ext using 2 with x
    by_cases hx : x ∈ φ.active <;> simp [Z, hx]
  have Zm : AEStronglyMeasurable Z volume := by
    have coords (i : Fin 3) : AEMeasurable (fun x => Z x i) volume :=
      (locallyIntegrableOn_univ.mp (weak i).2.1).aestronglyMeasurable.aemeasurable
    exact ((WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp_aemeasurable (aemeasurable_pi_lambda _ coords)).aestronglyMeasurable
  let scale := ε^(1-p/2)
  let major := fun x => (4*p)^p*(weightedRoot φ G p x + scale*(D.charge x*φ.hessianNorm x^p))
  have h4 : 0 ≤ (4*p)^p := Real.rpow_nonneg (by positivity) _
  have hscale : 0 ≤ scale := Real.rpow_nonneg hε.le _
  have hcurv (x) : 0 ≤ D.charge x*φ.hessianNorm x^p :=
    mul_nonneg (D.charge_nonneg x) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have bound : ∀ᵐ x, ‖Z x‖^p ≤ major x := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp boundA, boundB] with x hAx hBx
    by_cases hx : x ∈ φ.active
    · have hab : ‖Z x‖ ≤ 2*p*(v x * matrixGradNorm G x) + (u x * L * φ.hessianNorm x) := by
        have hn := norm_add_le (v x • A x) (u x • B x)
        simp only [norm_smul, Real.norm_of_nonneg (hu x), Real.norm_of_nonneg (hv x)] at hn
        have h := add_le_add (mul_le_mul_of_nonneg_left (hAx hx) (hv x))
          (mul_le_mul_of_nonneg_left hBx (hu x))
        rw [show Z x = v x • A x + u x • B x from indicator_of_mem hx _]
        change ‖B x‖ ≤ L*φ.hessianNorm x at hBx
        change _ ≤ v x*(2*p*matrixGradNorm G x)+u x*(L*φ.hessianNorm x) at h
        exact (hn.trans h).trans_eq (by ring)
      have hG : 0 ≤ matrixGradNorm G x := Real.sqrt_nonneg _
      have hH : 0 ≤ φ.hessianNorm x := Real.sqrt_nonneg _
      have hpow := weighted_sum_power hp₁ (mul_nonneg (hv x) hG) (mul_nonneg (mul_nonneg (hu x) hL) hH)
        (norm_nonneg _) hab
      apply hpow.trans (mul_le_mul_of_nonneg_left _ h4)
      apply add_le_add
      · rw [Real.mul_rpow (hv x) hG]
        exact mul_le_mul_of_nonneg_right ((truncation_bounds hp₀ hε.le (range (φ.grad x)).1).1.trans
          (pow_le_pow_left₀ (range _).1 (range _).2 2))
          (Real.rpow_nonneg hG _)
      · apply le_of_eq
        rw [Real.mul_rpow (mul_nonneg (hu x) hL) hH, Real.mul_rpow (hu x) hL,
          show L^p = scale from truncationSlope_rpow hp₀ hε]
        change (D.charge x^(1/p))^p*scale*φ.hessianNorm x^p = _
        rw [← Real.rpow_mul (D.charge_nonneg x), div_mul_cancel₀ _ hp₀.ne', Real.rpow_one]
        ring
    · simp only [Z, indicator_of_notMem hx, norm_zero, Real.zero_rpow hp₀.ne']
      exact mul_nonneg h4 (add_nonneg (weightedRoot_nonneg ..) (mul_nonneg hscale (hcurv x)))
  have iMajor : Integrable major :=
    ((integrable_weightedRoot hφ).add (hφ.curvature.const_mul scale)).const_mul _
  have iZ : Integrable (fun x => ‖Z x‖^p) := iMajor.mono' (Zm.norm.aemeasurable.pow_const _).aestronglyMeasurable
    (bound.mono fun x hx => by simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)] using hx)
  have Zlp : MemLp Z (ENNReal.ofReal p) :=
    (integrable_norm_rpow_iff Zm (by simp [hp₀]) (by simp)).mp (by simpa [ENNReal.toReal_ofReal hp₀.le] using iZ)
  refine ⟨Z, fun U _ i => weakPartialOn_restrict MeasurableSet.univ (subset_univ _) (weak i), Zlp, ?_⟩
  intro K
  have h := integral_mono_ae iZ.integrableOn (iMajor.integrableOn (s := K)) (ae_restrict_of_ae bound)
  dsimp only [major] at h
  rwa [integral_const_mul, integral_add (integrable_weightedRoot hφ).integrableOn
    (hφ.curvature.integrableOn.const_mul scale), integral_const_mul] at h

/-- The same weak gradient works on every open set and obeys the weighted
product estimate on every comparison ball. -/
theorem truncatedDensity_gradient (calcRules : TruncationSobolevCalculus)
    {D : Density} {φ : Phase} {G : MatrixGradient} {p ε : ℝ} (hp : 3 < p) (hε : 0 < ε)
    (hφ : PhaseAdmissible D p φ G) (hc : Continuous D.charge) :
    ∃ Z : Position → Position, (∀ U, IsOpen U → ∀ i, WeakPartialOn U i (truncatedDensity D φ p ε)
      (fun x => Z x i)) ∧ MemLp Z (ENNReal.ofReal p) ∧ ∀ K : Set Position,
      (∫ x in K, ‖Z x‖^p) ≤ (4*p)^p*((∫ x in K, weightedRoot φ G p x) +
        ε^(1-p/2)*∫ x in K, D.charge x*φ.hessianNorm x^p) :=
  truncatedSpeedProduct_gradient calcRules hp hε hφ hc (fun v => ‖v‖)
    lipschitzWith_one_norm (fun v => ⟨norm_nonneg v, le_rfl⟩)

end TSGA.PhaseLocalization
