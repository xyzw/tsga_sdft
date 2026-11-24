import TSGA.PhaseOscillation
import TSGA.LocalGaugeComparison
import TSGA.LocalSpinRotation

/-! # Local wavevector replacement for the Coulomb constrained search (Lemma 4.17) -/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization Metric
open scoped ComplexOrder MatrixOrder

variable {K : Set Position}

private def SpiralTaper.phaseGaugeOfCost (t : SpiralTaper K) (M : Density)
    (C : LocalSpinCalculus) (F : FiniteEnergyInputs) (chain : WeakPhaseProduct)
    {φ : Phase} {p W : ℝ} (hφ : φ.Regular p)
    (rep : ∃ Γ, feasible (t.field M).matrix Γ)
    (hi : Integrable (fun x => (t.field M).charge x * phaseCorrectionWeight φ t.wavevector x))
    (cap : (∫ x, (t.field M).charge x * phaseCorrectionWeight φ t.wavevector x) ≤ W) :
    GaugeComparison (t.field M) (t.phaseField M φ) F.loCoeff := by
  let w := phaseCorrectionWeight φ t.wavevector
  have dom (A : Density) : LocalRotationDomain A Set.univ :=
    Or.inl ⟨isOpen_univ,Set.subset_univ _⟩
  have grad := phaseCorrection_weak chain hφ t.wavevector
  have adj := phaseCorrection_adjoint_weak chain hφ t.wavevector
  have measU {V : Position → unitary SpinMatrix} {Z : MatrixGradient}
      (hz : IsMatrixGradientOn Set.univ (fun x => (V x : SpinMatrix)) Z) (j k : Fin 2) :
      AEMeasurable (fun x => (V x : SpinMatrix) j k) volume :=
    (locallyIntegrableOn_univ.mp (hz 0 j k).1).aestronglyMeasurable.aemeasurable
  have wc : Continuous w := ((hφ.continuous_grad.sub continuous_const).norm.pow 2).div_const 4
  have wp (x : Position) : 0 ≤ w x := div_nonneg (sq_nonneg _) (by norm_num)
  have same : (t.phaseField M φ).charge = (t.field M).charge := by funext x; simp
  have fw := C.rotationLaw (dom (t.field M)) (measU grad) grad wc.aemeasurable wp
    (ae_of_all _ fun x => (phaseCorrection_square φ t.wavevector x).le) hi
  have bw := C.rotationLaw (dom (t.phaseField M φ)) (measU adj) adj wc.aemeasurable wp
    (ae_of_all _ fun x => (phaseCorrection_adjoint_square φ t.wavevector x).le) (by simpa only [same] using hi)
  exact GaugeComparison.of_rotationLaws F (t.phaseCorrection_target M φ) rep
    (fw.mono cap) (bw.mono (by simpa only [same] using cap))

/-- The same quarter-oscillation coefficient supplies both rotation laws of
the phase comparison used in the signed replacement inequality. -/
def SpiralTaper.phaseGauge (t : SpiralTaper K) (M : Density)
    (C : LocalSpinCalculus) (F : FiniteEnergyInputs) (chain : WeakPhaseProduct)
    {φ : Phase} {p ω : ℝ} (hφ : φ.Regular p)
    (rep : ∃ Γ, feasible (t.field M).matrix Γ)
    (mass : Integrable (fun x => t.shape x * M.charge x))
    (osc : ∀ x ∈ K, ‖φ.grad x - t.wavevector‖ ≤ ω) :
    GaugeComparison (t.field M) (t.phaseField M φ) F.loCoeff :=
  let h := t.phase_weighted_cost M hφ mass osc
  t.phaseGaugeOfCost M C F chain hφ rep h.1 h.2

/-- Lemma 4.17 with the exact tapered mismatch and the same error in both
directions. Compact support and continuity of the wavevector give the finite cost. -/
theorem SpiralTaper.weighted_wavevector_energy (t : SpiralTaper K) (M : Density)
    (C : LocalSpinCalculus) (F : FiniteEnergyInputs) (chain : WeakPhaseProduct)
    {φ : Phase} {p ε : ℝ} (hφ : φ.Regular p) (compact : IsCompact K)
    (rep : ∃ Γ, feasible (t.field M).matrix Γ)
    (mass : Integrable (fun x => t.shape x * M.charge x))
    (moment : Integrable (fun x => t.shape x * M.charge x ^ (4/3:ℝ)))
    (he : 0 < ε) (hle : ε ≤ 1) :
    let err := ε * F.loCoeff * (∫ x, t.shape x * M.charge x ^ (4/3:ℝ)) +
      (∫ x, (t.shape x * M.charge x) * ‖φ.grad x - t.wavevector‖^2) / (2*ε)
    energy (t.phaseField M φ).matrix ≤ (1+ε) * energy (t.field M).matrix + err ∧
      energy (t.field M).matrix ≤ (1+ε) * energy (t.phaseField M φ).matrix + err := by
  obtain ⟨ω, hω⟩ := compact.bddAbove_image ((hφ.continuous_grad.sub continuous_const).norm.continuousOn)
  have hi := (t.phase_weighted_cost M hφ mass (fun x hx => hω ⟨x, hx, rfl⟩)).1
  let W := ∫ x, (t.field M).charge x * phaseCorrectionWeight φ t.wavevector x
  have hw : 0 ≤ W := integral_nonneg fun x => mul_nonneg ((t.field M).charge_nonneg x)
    (div_nonneg (sq_nonneg _) (by norm_num))
  have mismatch : (∫ x, (t.shape x * M.charge x) * ‖φ.grad x - t.wavevector‖^2) = 4*W := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [t.field_charge, phaseCorrectionWeight]
    ring
  obtain ⟨fw,bw⟩ := (t.phaseGaugeOfCost M C F chain hφ rep hi (le_refl W)).signed he
  have cost : (1+1/ε)*W ≤ (4*W)/(2*ε) := by
    field_simp
    nlinarith only [mul_nonneg hw (sub_nonneg.mpr hle)]
  have mom := mul_le_mul_of_nonneg_left (t.chargeMoment_bound M moment)
    (mul_nonneg he.le F.lo_nonneg)
  have same : chargeMoment (t.phaseField M φ) (4/3) = chargeMoment (t.field M) (4/3) := by
    simp only [chargeMoment, SpiralTaper.phaseField_charge, SpiralTaper.field_charge]
  change energy _ ≤ energy _ + (ε*(energy _ + F.loCoeff*chargeMoment (t.field M) (4/3)) +
    (1+1/ε)*W) at fw
  change energy _ ≤ energy _ + (ε*(energy _ + F.loCoeff*chargeMoment (t.phaseField M φ) (4/3)) +
    (1+1/ε)*W) at bw
  rw [same] at bw
  dsimp only
  rw [mismatch]
  constructor <;> linarith only [fw,bw,mom,cost]

/-- The oscillation form of the two inequalities, with coefficient
ϖ²/(2ε), valid for any compactly supported taper satisfying the oscillation bound. -/
theorem SpiralTaper.constant_wavevector_energy (t : SpiralTaper K) (M : Density)
    (C : LocalSpinCalculus) (F : FiniteEnergyInputs) (chain : WeakPhaseProduct)
    {φ : Phase} {p ω ε : ℝ} (hφ : φ.Regular p)
    (rep : ∃ Γ, feasible (t.field M).matrix Γ)
    (mass : Integrable (fun x => t.shape x * M.charge x))
    (moment : Integrable (fun x => t.shape x * M.charge x ^ (4/3:ℝ)))
    (osc : ∀ x ∈ K, ‖φ.grad x - t.wavevector‖ ≤ ω) (he : 0 < ε) (hle : ε ≤ 1) :
    let err := ε * F.loCoeff * (∫ x, t.shape x * M.charge x^(4/3:ℝ)) +
      ω^2/(2*ε) * ∫ x, t.shape x * M.charge x
    energy (t.phaseField M φ).matrix ≤ (1+ε)*energy (t.field M).matrix + err ∧
      energy (t.field M).matrix ≤ (1+ε)*energy (t.phaseField M φ).matrix + err := by
  obtain ⟨forward,backward⟩ := (t.phaseGauge M C F chain hφ rep mass osc).signed he
  let m := ∫ x, t.shape x * M.charge x
  have hm : 0 ≤ m := integral_nonneg fun x => mul_nonneg (t.range x).1 (M.charge_nonneg x)
  have hc : (1+1/ε)*(ω^2/4) ≤ ω^2/(2*ε) := by
    field_simp
    nlinarith only [mul_nonneg (sq_nonneg ω) (sub_nonneg.mpr hle)]
  have cost := mul_le_mul_of_nonneg_right hc hm
  have momentA := mul_le_mul_of_nonneg_left (t.chargeMoment_bound M moment)
    (mul_nonneg he.le F.lo_nonneg)
  have mm : chargeMoment (t.phaseField M φ) (4/3) = chargeMoment (t.field M) (4/3) := by
    simp only [chargeMoment, SpiralTaper.phaseField_charge, SpiralTaper.field_charge]
  change energy _ ≤ energy _ + (ε*(energy _ + F.loCoeff*chargeMoment (t.field M) (4/3)) +
    (1+1/ε)*(ω^2/4*m)) at forward
  change energy _ ≤ energy _ + (ε*(energy _ + F.loCoeff*chargeMoment (t.phaseField M φ) (4/3)) +
    (1+1/ε)*(ω^2/4*m)) at backward
  rw [mm] at backward
  dsimp only
  change _ ≤ _ + (_ + ω^2/(2*ε)*m) ∧ _ ≤ _ + (_ + ω^2/(2*ε)*m)
  constructor <;> linarith only [forward,backward,momentA,cost]

/-- Center the wavevector at ∇φ(c) and use the attained maximum on the
closed comparison ball. The curvature constant depends only on the constant
in the vector-valued Morrey inequality and on the exponent. -/
theorem constant_wavevector_on_ball {φ : Phase} {p ℓ ε Cₘ : ℝ} (hp : 3 < p)
    (hφ : φ.Regular p) (morrey : VectorMorreyOnBalls p Cₘ)
    (c : Position) (hℓ : 0 < ℓ) (t : SpiralTaper (closedBall c (3*ℓ)))
    (hq : t.wavevector = φ.grad c) (M : Density) (leibniz : LocalSectorLeibniz) (F : FiniteEnergyInputs)
    (chain : WeakPhaseProduct) {Γ : MixedState} (hΓ : feasible M.matrix Γ)
    (restrictor : SpatialFockRestriction Γ M) {g : Position → Fin 3 → ℝ}
    (weak : ∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (t.shape x)) (fun x => g x i))
    {b : ℝ} (bounded : ∀ᵐ x, maskFisher g x ≤ b)
    (hm : AEMeasurable t.shape volume) (mass : Integrable M.charge)
    (moment : Integrable (fun x => M.charge x ^ (4/3:ℝ))) (he : 0 < ε) (hle : ε ≤ 1) :
    let ω := tilePhaseOscillation φ c ℓ
    let err := ε * F.loCoeff * (∫ x, t.shape x * M.charge x^(4/3:ℝ)) +
      ω^2/(2*ε) * ∫ x, t.shape x * M.charge x
    ω^p ≤ (Cₘ*3^(p-3)) * ℓ^(p-3) * (∫ x in closedBall c (3*ℓ), φ.hessianNorm x ^ p) ∧
      energy (t.phaseField M φ).matrix ≤ (1+ε)*energy (t.field M).matrix + err ∧
      energy (t.field M).matrix ≤ (1+ε)*energy (t.phaseField M φ).matrix + err := by
  obtain ⟨_,_,_,bound⟩ := tilePhaseOscillation_attained hφ c hℓ
  have rep := t.field_representable M hΓ restrictor weak (t.integrable_fisher M weak bounded mass)
  exact ⟨tilePhaseOscillation_morrey hp hφ morrey c hℓ,
    t.constant_wavevector_energy M (LocalSpinCalculus.of_leibniz leibniz) F chain hφ rep
      (t.integrable_weight _ hm mass) (t.integrable_weight _ hm moment)
      (by simpa only [hq] using bound) he hle⟩

end TSGA.ManyBody
