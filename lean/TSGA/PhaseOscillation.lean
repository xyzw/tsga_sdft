import TSGA.AxialPhaseCorrection
import TSGA.OrderedCoulombFrame
import TSGA.IslandExteriorTrial

/-! # Oscillation and integrated kinetic cost of the residual axial rotation -/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization Set Metric

/-- Maximum wavevector mismatch from the center, used in the oscillation form of Lemma 4.17. -/
def tilePhaseOscillation (φ : Phase) (c : Position) (ℓ : ℝ) : ℝ :=
  sSup ((fun x => ‖φ.grad x - φ.grad c‖) '' closedBall c (3*ℓ))

theorem tilePhaseOscillation_attained {φ : Phase} {p ℓ : ℝ} (hφ : φ.Regular p) (c : Position)
    (hℓ : 0 < ℓ) :
    ∃ x ∈ closedBall c (3*ℓ), tilePhaseOscillation φ c ℓ = ‖φ.grad x - φ.grad c‖ ∧
      ∀ y ∈ closedBall c (3*ℓ), ‖φ.grad y - φ.grad c‖ ≤ tilePhaseOscillation φ c ℓ := by
  obtain ⟨x,hx,he,hm⟩ := (isCompact_closedBall c (3*ℓ)).exists_sSup_image_eq_and_ge
    ⟨c,mem_closedBall_self (by positivity)⟩ (hφ.continuous_grad.sub continuous_const).norm.continuousOn
  exact ⟨x,hx,he,fun y hy => (hm y hy).trans_eq he.symm⟩

/-- Standard vector-valued Sobolev–Morrey inequality on Euclidean balls
for continuous representatives of arbitrary locally W¹ᵖ vector fields. -/
def VectorMorreyOnBalls (p C : ℝ) : Prop :=
  3 < p → ∀ (u : Position → Position) (G : Position → Fin 3 → Fin 3 → ℝ), Continuous u →
    (∀ i, LocalLpOn univ p fun x => u x i) →
    (∀ i j, LocalLpOn univ p fun x => G x i j) →
    (∀ i j, WeakPartialOn univ i (fun x => u x j) (fun x => G x i j)) →
    ∀ (c : Position) (R : ℝ), 0 < R → ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      ‖u x - u y‖ ^ p ≤ C * R ^ (p-3) *
        (∫ z in closedBall c R, Real.sqrt (∑ i, ∑ j, G z i j ^ 2) ^ p)

theorem tilePhaseOscillation_morrey {φ : Phase} {p ℓ C : ℝ} (hp : 3 < p) (hφ : φ.Regular p)
    (morrey : VectorMorreyOnBalls p C) (c : Position) (hℓ : 0 < ℓ) :
    tilePhaseOscillation φ c ℓ ^ p ≤ (C * 3^(p-3)) * ℓ^(p-3) *
      ∫ x in closedBall c (3*ℓ), φ.hessianNorm x ^ p := by
  obtain ⟨x,hx,he,_⟩ := tilePhaseOscillation_attained hφ c hℓ
  have h := morrey hp φ.grad φ.hessian hφ.continuous_grad hφ.grad_Lp hφ.hessian_Lp hφ.weak_hessian
    c (3*ℓ) (by positivity) x hx c (mem_closedBall_self (by positivity))
  simpa only [he, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hℓ.le, mul_assoc, Phase.hessianNorm] using h

variable {K : Set Position}

/-- Starting from a state for the original density, restrict by the real
window and apply the constant-wavevector spin twist sector by sector. -/
theorem SpiralTaper.field_representable (t : SpiralTaper K) (M : Density) {Γ : MixedState}
    (hΓ : feasible M.matrix Γ) (restrictor : SpatialFockRestriction Γ M)
    {g : Position → Fin 3 → ℝ}
    (weak : ∀ i, WeakPartialOn univ i (fun x => Real.sqrt (t.shape x)) (fun x => g x i))
    (fisher : Integrable (fun x => maskFisher g x * M.charge x)) :
    ∃ Λ, feasible (t.field M).matrix Λ := by
  have localized := (restrictor.restrict t.shape g hΓ t.range weak fisher).1
  refine ⟨(restrictor.state t.shape).twist (axialShift t.wavevector),localized.mono fun x hx => ?_⟩
  rw [MixedState.density_axialShift, hx]
  change rotate _ (t.shape x • M.matrix x) = (t.shape x : ℂ) • rotate _ (M.matrix x)
  rw [← SSW.rotate_smul]
  rfl

/-- A bounded squared gradient of the square-root taper has finite
localization cost against every nonnegative integrable charge. -/
theorem SpiralTaper.integrable_fisher (t : SpiralTaper K) (M : Density) {g : Position → Fin 3 → ℝ}
    (weak : ∀ i, WeakPartialOn univ i (fun x => Real.sqrt (t.shape x)) (fun x => g x i))
    {b : ℝ} (bounded : ∀ᵐ x, maskFisher g x ≤ b) (mass : Integrable M.charge) :
    Integrable (fun x => maskFisher g x * M.charge x) := by
  have hm : AEMeasurable (maskFisher g) volume := Finset.aemeasurable_fun_sum _ fun i _ =>
    ((locallyIntegrableOn_univ.mp (weak i).2.1).aestronglyMeasurable.aemeasurable).pow_const 2
  apply (mass.const_mul b).mono' (hm.aestronglyMeasurable.mul mass.aestronglyMeasurable)
  filter_upwards [bounded] with x hx
  change ‖maskFisher g x * M.charge x‖ ≤ b * M.charge x
  have hn : 0 ≤ maskFisher g x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_of_nonneg (mul_nonneg hn (M.charge_nonneg x))]
  exact mul_le_mul_of_nonneg_right hx (M.charge_nonneg x)

theorem SpiralTaper.integrable_weight (t : SpiralTaper K) (f : Position → ℝ)
    (hm : AEMeasurable t.shape volume) (hf : Integrable f) : Integrable (fun x => t.shape x*f x) := by
  apply hf.mono (hm.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with x
  change ‖t.shape x * f x‖ ≤ ‖f x‖
  rw [norm_mul,Real.norm_of_nonneg (t.range x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (t.range x).2

theorem SpiralTaper.phase_weighted_cost (t : SpiralTaper K) (M : Density) {φ : Phase} {p ω : ℝ}
    (hφ : φ.Regular p) (mass : Integrable (fun x => t.shape x * M.charge x))
    (osc : ∀ x ∈ K, ‖φ.grad x - t.wavevector‖ ≤ ω) :
    let w := phaseCorrectionWeight φ t.wavevector
    Integrable (fun x => (t.field M).charge x * w x) ∧
      (∫ x, (t.field M).charge x * w x) ≤ (ω^2/4) * ∫ x, t.shape x * M.charge x := by
  have meas : Continuous (phaseCorrectionWeight φ t.wavevector) :=
    ((hφ.continuous_grad.sub continuous_const).norm.pow 2).div_const 4
  have major := mass.const_mul (ω^2/4)
  have weight_nonneg (x : Position) : 0 ≤ phaseCorrectionWeight φ t.wavevector x :=
    div_nonneg (sq_nonneg _) (by norm_num)
  have h (x : Position) : (t.shape x * M.charge x) * phaseCorrectionWeight φ t.wavevector x ≤
      (ω^2/4) * (t.shape x * M.charge x) := by
    by_cases hx : x ∈ K
    · rw [mul_comm (ω^2/4)]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (osc x hx) 2) (by norm_num))
        (mul_nonneg (t.range x).1 (M.charge_nonneg x))
    · simp [t.outside x hx]
  have hi := major.mono' (mass.aestronglyMeasurable.mul meas.aestronglyMeasurable)
    (ae_of_all _ fun x => (Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (t.range x).1 (M.charge_nonneg x)) (weight_nonneg x))).le.trans (h x))
  simp only [SpiralTaper.field_charge]
  exact ⟨hi,(integral_mono hi major h).trans_eq (integral_const_mul _ _)⟩

/-- The tapered Lieb–Oxford moment in either gauge is bounded by the
linear taper multiplying the unrotated density moment. -/
theorem SpiralTaper.chargeMoment_bound (t : SpiralTaper K) (M : Density)
    (moment : Integrable (fun x => t.shape x * M.charge x ^ (4/3:ℝ))) :
    chargeMoment (t.field M) (4/3) ≤ ∫ x, t.shape x * M.charge x ^ (4/3:ℝ) := by
  apply integral_mono_of_nonneg (ae_of_all _ fun x => Real.rpow_nonneg ((t.field M).charge_nonneg x) _)
    moment (ae_of_all _ fun x => ?_)
  change (t.field M).charge x ^ (4/3:ℝ) ≤ _
  rw [t.field_charge, Real.mul_rpow (t.range x).1 (M.charge_nonneg x)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_self_of_le_one (t.range x).1 (t.range x).2 (by norm_num)) (Real.rpow_nonneg (M.charge_nonneg x) _)

end TSGA.ManyBody
