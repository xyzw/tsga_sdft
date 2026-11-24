import TSGA.SmallBallGas

/-! # Choosing the physical gas modulus in each bulk regime -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Metric Set
open scoped ComplexOrder

variable {η : Mollifier} {K p θ ν : ℝ}

/-- Use the manuscript's power modulus, its positive minority-floor version,
or its global-root version as determined by the bulk regime. -/
def CoulombGasInputs.freezeModulus (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (S : SobolevDifferenceQuotients) (mode : BulkRegime) (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1)
    (minority : mode = .minority → 0 < ν ∧ ν ≤ 1/2) : PhysicalTileModulus η :=
  match mode with
  | .general => L.generalModulus H S hp.le hθ
  | .minority => L.minorityModulus H S hp.le hθ hθ'
      (div_pos (minority rfl).1 (by norm_num : (0:ℝ)<16)) (by linarith only [(minority rfl).2])
  | .globalRoot => L.rootModulus H S hp.le

/-- All cutoff and domain statements use the original field. The choice
of the coefficient precedes the choice of density, center and taper. -/
def SmallGasChoice (M : PhysicalTileModulus η) (mode : BulkRegime) (p θ ν K J : ℝ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {D N : Density} {φ : Phase} {G : MatrixGradient} {c : Position},
    ∀ (s : SmallBallScale N (3*ε⁻¹) c) (m : SmallBallMatrices s),
    N.matrix =ᵐ[volume] D.matrix → Continuous N.matrix →
    (∀ z : ℝ, 0 < z → Continuous (N.power z)) → φ.Regular p → RegimeHyp mode ν N G p →
    s.omega θ ≤ s.r^θ → ∀ {F : SpinMatrix} (hF : F.PosSemidef), F=m.low ∨ F=m.high →
    ∀ (P : TileProfile), (∀ x, P.cutoff (c-x) ≠ 0 → x ∈ closedBall c (3*ε⁻¹)) → ∀ σ : ℝ,
    let f := fun x => M.value F (D.matrix x) hF (D.positive x) (φ.grad c) (φ.grad x)
    let r := s.r
    let d := s.omega (1/p)/r^(1/p)
    let phase := smallBallPhaseCost r d ε (tilePhaseOscillation φ c ε⁻¹) (φ.grad c)
    let b := mode.densityPower p θ
    (∀ᵐ x, M.domain F (D.matrix x)) ∧
    Integrable (fun x => (σ*localEnergy (referenceEnergies energy η) D φ x)*P.cutoff (c-x)) ∧
    Integrable (fun x => f x*P.cutoff (c-x)) ∧
    cutoffAverage P.cutoff f c ≤ smallGasConstant J K*(smallGasBulk r (s.omega b) b (mode.holderPower p θ)+phase)

theorem CoulombGasInputs.freezeGas (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (S : SobolevDifferenceQuotients) (mode : BulkRegime) (hp : 3 < p) (hθ : 0 < θ) (hθ' : θ ≤ 1)
    (hpθ : 2 ≤ p*θ) (minority : mode = .minority → 0 < ν ∧ ν ≤ 1/2) :
    ∃ J > 0, SmallGasChoice (L.freezeModulus H S mode hp hθ hθ' minority) mode p θ ν K J := by
  have hK := zero_le_one.trans L.rate.one_le
  have hp₀ : 0 < p := by linarith
  cases mode with
  | general =>
    obtain ⟨J,hJ,law⟩ := L.general_formula H S hp.le hθ
    refine ⟨J,hJ,?_⟩
    intro ε he hle D N φ G c s m e hc cp phase _ _ F hF sel P support σ
    have cutoff := m.gas_cutoff _ law hJ.le hK hp hθ hθ' (lt_min zero_lt_one (by positivity))
      (min_le_left ..) he hle phase e hc cp hF sel P support (Or.inl rfl)
    exact ⟨ae_of_all _ fun _ => trivial, L.local_cutoff_integrable H S e hc phase P c σ _ (by positivity) support, cutoff⟩
  | minority =>
    have hν := minority rfl
    obtain ⟨J,hJ,law⟩ := L.minority_formula H S hp.le hθ hθ'
      (div_pos hν.1 (by norm_num : (0:ℝ)<16)) (by linarith only [hν.2])
    refine ⟨J,hJ,?_⟩
    intro ε he hle D N φ G c s m e hc cp phase hr small F hF sel P support σ
    have hratio : s.omega θ/s.r^θ ≤ 1 := div_le_one_of_le₀ small (Real.rpow_nonneg s.r_nonneg _)
    have ha : 0 ≤ BulkRegime.minority.holderPower p θ := by
      unfold BulkRegime.holderPower
      have hden : 0 ≤ 3*(θ*p-1) := by linarith only [hpθ,mul_comm p θ]
      exact le_min zero_le_one (div_nonneg hp₀.le hden)
    have cutoff := m.gas_cutoff _ law hJ.le hK hp hθ hθ' zero_lt_one le_rfl he hle phase e hc cp hF sel
      P support (Or.inr ⟨ha,min_le_left ..,hratio⟩)
    exact ⟨m.minority_gas_domain L H S hp.le hθ hθ' hν.1 hν.2 hr e hF sel,
      L.local_cutoff_integrable H S e hc phase P c σ _ (by positivity) support, cutoff⟩
  | globalRoot =>
    obtain ⟨J,hJ,law⟩ := L.root_formula H S hp.le
    refine ⟨J,hJ,?_⟩
    intro ε he hle D N φ G c s m e hc cp phase _ _ F hF sel P support σ
    have ha := one_div_pos.mpr hp₀
    have ha' : 1/p ≤ 1 := (div_le_one hp₀).2 (by linarith)
    have cutoff := m.gas_cutoff _ law hJ.le hK hp ha ha' zero_lt_one le_rfl he hle phase e hc cp hF sel
      P support (Or.inl rfl)
    exact ⟨ae_of_all _ fun _ => trivial, L.local_cutoff_integrable H S e hc phase P c σ _ (by positivity) support, cutoff⟩

end TSGA.ManyBody
