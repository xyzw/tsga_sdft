import TSGA.ConstantWavevectorRotation
import TSGA.RepresentableTileDensity

/-! # Local wavevector replacement on the finite-energy density domain -/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization

/-- Lemma 4.17 for any compact taper with bounded weak square-root gradient.
Localization and a constant spin twist supply the trial for the tapered
density. The H¹ embedding controls its Lieb–Oxford moment. -/
theorem SpiralTaper.weighted_wavevector_energy_of_sqrtRegular
    {K : Set Position} (t : SpiralTaper K) (compact : IsCompact K) (M : Density)
    {S : MatrixGradient} (regular : SqrtRegular M S)
    {g : Position → Fin 3 → ℝ} (weak : ∀ i, WeakPartialOn Set.univ i
      (fun x => Real.sqrt (t.shape x)) (fun x => g x i))
    {b : ℝ} (bounded : ∀ᵐ x, maskFisher g x ≤ b)
    (F : FiniteEnergyInputs) (embed : MatrixSobolevEmbeddingFour)
    (restrictor : ∀ Γ : MixedState, SpatialFockRestriction Γ M)
    (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct)
    {φ : Phase} {p ε : ℝ} (hφ : φ.Regular p) (he : 0 < ε) (hle : ε ≤ 1) :
    let err := ε * F.loCoeff * (∫ x, t.shape x * M.charge x ^ (4/3:ℝ)) +
      (∫ x, (t.shape x * M.charge x) * ‖φ.grad x - t.wavevector‖^2) / (2*ε)
    energy (t.phaseField M φ).matrix ≤ (1+ε) * energy (t.field M).matrix + err ∧
      energy (t.field M).matrix ≤ (1+ε) * energy (t.phaseField M φ).matrix + err := by
  obtain ⟨Γ, hΓ⟩ := F.representable regular
  have trial := t.field_representable M hΓ (restrictor Γ) weak
    (t.integrable_fisher M weak bounded regular.charge)
  have root := (locallyIntegrableOn_univ.mp (weak 0).1).aestronglyMeasurable.aemeasurable
  have shape : AEMeasurable t.shape volume := by
    have eq : (fun x => Real.sqrt (t.shape x) ^ 2) = t.shape :=
      funext fun x => Real.sq_sqrt (t.range x).1
    rw [← eq]
    exact root.pow_const (2 : ℕ)
  have domain := tileDensityDomain_of_representable embed regular
  exact t.weighted_wavevector_energy M (LocalSpinCalculus.of_leibniz leibniz) F chain hφ compact
    trial (t.integrable_weight _ shape regular.charge) (t.integrable_weight _ shape domain.lo) he hle

end TSGA.ManyBody
