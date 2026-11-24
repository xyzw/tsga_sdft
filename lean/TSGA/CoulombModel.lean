import TSGA.CoulombFrozenTile
import TSGA.CoulombBallKinematics

/-! # The TSGA estimate from finite Coulomb trial and tiling data

All three local gas moduli are derived for the constrained search. The
remaining finite inputs describe the physical trials, their cutoffs, and
the local integration estimates with those explicit moduli.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization TSGA.SSW PhaseLocalization
open scoped ComplexOrder

/-- Finite-volume hypotheses used to construct the gas and prove its regularity. -/
structure CoulombGasInputs (η : Mollifier) (K : ℝ) where
  localization : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position,
    FiniteLocalization energy η M q
  transport : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
    ∀ n, SpiralTransport (DomainSequence.balls unitBallMollifier) M n ζ θ
  rate : FiniteRateTiling energy η K
  frames : ∀ ℓ > 0, ∀ δ > 0, δ ≤ ℓ → ∀ q : Position,
    Nonempty (OrderedSpiralFrame (smoothedIndicator (tetrahedron ℓ) η δ) (regionVolume (tetrahedron ℓ)) q)

variable {η : Mollifier} {K : ℝ}

theorem FiniteEnergyInputs.indirect_lower (H : FiniteEnergyInputs) (D : Density) (Γ : MixedState)
    (hΓ : feasible D.matrix Γ) : -H.loCoeff * (∫ x, D.charge x^(4/3:ℝ)) ≤ indirectAt D.matrix Γ := by
  change _ ≤ Γ.interaction - hartree D.charge
  have h := H.liebOxford D Γ hΓ
  unfold chargeMoment at h
  linarith only [h]

theorem CoulombGasInputs.removal (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (sob : SobolevDifferenceQuotients) : SpiralRemovalTrials η (max 1 tetrahedronDirectConstant) :=
  spiralRemovalTrials_of_frames H sob L.frames

def CoulombGasInputs.kinematics (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (sob : SobolevDifferenceQuotients) := ballSpiralKinematics H sob L.transport

def CoulombGasInputs.generalModulus (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (sob : SobolevDifferenceQuotients) {p θ : ℝ} (hp : 3 ≤ p) (hθ : 0 < θ) : PhysicalTileModulus η :=
  generalTileModulus L.localization (L.kinematics H sob) L.rate (L.removal H sob)
    H.lo_nonneg H.indirect_lower hp hθ

def CoulombGasInputs.minorityModulus (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (sob : SobolevDifferenceQuotients) {p θ ν : ℝ} (hp : 3 ≤ p) (hθ : 0 < θ) (hθ' : θ ≤ 1) (hν : 0 < ν) (hν' : ν ≤ 1/2) :
    PhysicalTileModulus η := by
  let law := coulomb_minority_tile_modulus L.localization (L.kinematics H sob) L.rate H.lo_nonneg H.indirect_lower
    hp hθ hθ' hν hν'
  let C := Classical.choose law
  let floor := fun A : SpinMatrix => (A - ((ν*A.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef
  refine ⟨fun A B => floor A ∧ floor B, fun A B hA hB q k =>
    let r := max A.trace.re B.trace.re
    let d := fun a : ℝ => hilbertSchmidt (hA.1.cfc (fun t => t^a) - hB.1.cfc (fun t => t^a))/r^a
    C*((r^(4/3:ℝ)+r^(5/3:ℝ))*d θ + r*‖q‖^2*d (1/p)) +
      (2*K+1)*(B.trace.re^(7/6:ℝ)+B.trace.re^(4/3:ℝ)+B.trace.re*max ‖q‖ ‖k‖)*‖q-k‖, ?_⟩
  intro A B hA hB h q k
  exact (Classical.choose_spec law).2 hA hB h.1 h.2 q k

def CoulombGasInputs.rootModulus (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (sob : SobolevDifferenceQuotients) {p : ℝ} (hp : 3 ≤ p) : PhysicalTileModulus η := by
  let law := coulomb_root_tile_modulus L.localization (L.kinematics H sob) L.rate (L.removal H sob)
    H.lo_nonneg H.indirect_lower hp
  let C := Classical.choose law
  refine ⟨fun _ _ => True, fun A B hA hB q k =>
    let r := max A.trace.re B.trace.re
    C*holderGrowth r q*(hilbertSchmidt
      (hA.1.cfc (fun t => t^(1/p:ℝ)) - hB.1.cfc (fun t => t^(1/p:ℝ)))/r^(1/p:ℝ)) +
      (2*K+1)*(B.trace.re^(7/6:ℝ)+B.trace.re^(4/3:ℝ)+B.trace.re*max ‖q‖ ‖k‖)*‖q-k‖, ?_⟩
  intro A B hA hB _ q k
  exact (Classical.choose_spec law).2 hA hB q k

/-- At each admissible scale both signs have physical trials and the given
cutoffs satisfy the local geometric and Sobolev estimates. -/
def CoulombTileTrials (H : FiniteEnergyInputs) (rate : FiniteRateTiling energy η K)
    (M : PhysicalTileModulus η) (mode : BulkRegime) (ν p θ : ℝ) : Prop :=
  ∃ A ≥ 1, ∃ τ > 0, ∀ (D : Density) (φ : Phase) (S T G : MatrixGradient), DensityRegular D p θ S T →
    PhaseAdmissible D p φ G → RegimeHyp mode ν D G p →
    ∀ δ : ℝ, 0 < δ → δ ≤ τ → δ ≤ 1 → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
    ∃ geom : SignedTilingData (referenceEnergies energy η) mode D φ S T G p θ δ A σ,
      CoulombFrozenComparison H rate M D φ geom.tiles geom.profile θ σ
        (fun c => geom.bulkError c + geom.phaseError c +
          A * (ballAverage geom.profile.radius (rootPower T p) c / δ ^ mode.replacementExponent p θ))

theorem CoulombTileTrials.finite {H : FiniteEnergyInputs} {rate : FiniteRateTiling energy η K}
    {M : PhysicalTileModulus η} {mode : BulkRegime} {ν p θ : ℝ}
    (h : CoulombTileTrials H rate M mode ν p θ) :
    ∃ A ≥ 1, ∃ τ > 0, FiniteComparisons (referenceEnergies energy η) mode ν p θ A τ := by
  obtain ⟨A,hA,τ,hτ,h⟩ := h
  refine ⟨A,hA,τ,hτ,?_⟩
  intro D φ S T G hD hφ hr δ hδ hτ' hδ' σ hσ
  obtain ⟨geom,hf⟩ := h D φ S T G hD hφ hr δ hδ hτ' hδ' σ hσ
  exact ⟨{ toSignedTilingData := geom, comparison := hf.toFrozen hσ }⟩

/-- Theorem 3.3 for the grand-canonical Coulomb constrained search. The
remaining tile hypotheses are evaluated using the three proved gas moduli. -/
theorem levyLieb_tsga_of_coulomb_tiles (H : FiniteEnergyInputs) (L : CoulombGasInputs η K)
    (chain : WeakPhaseProduct) (sobolev : SobolevLipschitzComposition) (diff : SobolevDifferenceQuotients)
    (general : ∀ p θ : ℝ, ∀ hp : 3 < p, ∀ hθ : 0 < θ, θ < 1 → 2 ≤ p*θ →
      CoulombTileTrials H L.rate (L.generalModulus H diff hp.le hθ) .general 0 p θ)
    (minority : ∀ p θ ν : ℝ, ∀ hp : 3 < p, ∀ hθ : 0 < θ, ∀ hθ' : θ < 1, 2 ≤ p*θ →
      ∀ hν : 0 < ν, ∀ hν' : ν ≤ 1/2,
      CoulombTileTrials H L.rate (L.minorityModulus H diff hp.le hθ hθ'.le (div_pos hν (by norm_num : (0:ℝ) < 16)) (by linarith))
        .minority ν p θ)
    (sharp : ∀ p : ℝ, ∀ hp : 3 < p,
      CoulombTileTrials H L.rate (L.rootModulus H diff hp.le) .globalRoot 0 p (2/p)) :
    MainExtendedTSGAEstimate (referenceEnergies energy η) := by
  apply levyLieb_tsga_of_spin_removal H chain sobolev L.rate diff L.frames L.localization (L.kinematics H diff)
  exact ⟨fun p θ hp hθ h₁ h₂ => (general p θ hp hθ h₁ h₂).finite,
    fun p θ ν hp hθ h₁ h₂ hν hν' => (minority p θ ν hp hθ h₁ h₂ hν hν').finite,
    fun p hp => (sharp p hp).finite⟩

end TSGA.ManyBody
