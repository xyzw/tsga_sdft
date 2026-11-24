import TSGA.CoulombBoost
import TSGA.OrderedCoulombFrame
import TSGA.RankOneCurrent
import TSGA.PlanarCurrent
import TSGA.CoulombModel

/-! # Finite spin transport from fermionic Coulomb wavefunctions

On every admissible sequence, rotation, boosts, conjugation averaging and
current alignment at rank one all act on the states of the original constrained
search. The only spin-removal input on tetrahedra concerns geometric Fock
localization and its reduced observables.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW
open scoped ComplexOrder InnerProductSpace

/-- The finite transport for every smoothed domain, including the
current identity at the fully polarized endpoint. -/
def coulombSpiralTransport (D : DomainSequence) (M : SpinMatrix) (ζ θ : ℝ)
    (hM : SpinParameters M ζ θ) (n : ℕ) :
    SpiralTransport D M n ζ θ where
  momentum s := s.val.momentum
  spinCurrent s := s.val.axialCurrent
  rotation := spiralRotation _ M n
  rotation_energy := spiralRotation_value _ M n
  planar s := by
    have hp : ∃ α : ℝ, ∀ᵐ x, rotate α ((D.spiralField M n 0 x).map (starRingEnd ℂ)) = D.spiralField M n 0 x := by
      simpa only [DomainSequence.spiralField,cutoffSpiral_zero_wavevector] using
        planar_cutoff (D.cutoff n) hM.positive.isHermitian
    obtain ⟨Λ,hΛ,hk,hw,hj⟩ := s.val.zero_currents_of_planar s.property hp
    exact ⟨⟨Λ,hΛ⟩,by simp [SpiralState.value,hk,hw],by simp [MixedState.momentum,hj],by simp [MixedState.axialCurrent,hj]⟩
  boost := MixedState.boostEquiv _
  boost_energy k s := s.boost_energy k
  boost_momentum k s := (s.val.momentum_boost k).trans (by rw [s.charge_spinNumber])
  boost_current k s := (s.val.axialCurrent_boost k).trans (by rw [s.axial_spinNumber])
  aligned := by
    rintro rfl s
    exact MixedState.spinMomentum_of_polarized_spiral _ hM n s.property

/-- The three finite spin comparisons precede the thermodynamic limit. Each
requires only representability of the unrotated cutoff density. -/
theorem coulomb_finite_spin_bounds (D : DomainSequence) {M : SpinMatrix} {ζ θ : ℝ}
    (hM : SpinParameters M ζ θ)
    (rep : ∀ n, Nonempty (SpiralState D M n 0)) :
    FiniteSpinBounds M ζ θ D.vol
      (fun n A q => D.totalEnergy energy A n q) := by
  apply finiteSpinBounds_of_laws hM D.vol_pos
  intro n
  let s : SpiralKinematics D M n ζ θ :=
    { coulombSpiralTransport D M ζ θ hM n with represented := rep n }
  exact s.finiteSpinLaws

/-- The SSW gas theorem for the Coulomb model from finite localization and
cutoff representability. All finite spin comparisons are proved on the balls. -/
theorem coulomb_sswGas_of_localization (η : Mollifier)
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) :
    SSWGasTheorem (referenceEnergies energy η) :=
  coulomb_sswGas η loc (ballSpiralKinematics H sob (coulombSpiralTransport (DomainSequence.balls unitBallMollifier)))

/-- Assemble the finite gas inputs from the tiling estimates and the reduced
Fock traces of a spin contraction. -/
def CoulombGasInputs.of_reduced {η : Mollifier} {K : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (rate : FiniteRateTiling energy η K) (red : FockSpinCurrentTraces) : CoulombGasInputs η K where
  localization := loc
  rate := rate
  transport := coulombSpiralTransport (DomainSequence.balls unitBallMollifier)
  frames _ hℓ _ hδ _ q := ordered_tetrahedral_frames red η hℓ hδ q

/-- The two signed tile comparisons for each of the three estimates. -/
structure CoulombGasInputs.TileTrials {η : Mollifier} {K : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (diff : SobolevDifferenceQuotients) : Prop where
  general : ∀ p θ : ℝ, ∀ hp : 3 < p, ∀ hθ : 0 < θ, θ < 1 → 2 ≤ p*θ →
    CoulombTileTrials H L.rate (L.generalModulus H diff hp.le hθ) .general 0 p θ
  minority : ∀ p θ ν : ℝ, ∀ hp : 3 < p, ∀ hθ : 0 < θ, ∀ hθ' : θ < 1, 2 ≤ p*θ →
    ∀ hν : 0 < ν, ∀ hν' : ν ≤ 1/2,
    CoulombTileTrials H L.rate (L.minorityModulus H diff hp.le hθ hθ'.le (div_pos hν (by norm_num : (0:ℝ) < 16)) (by linarith))
      .minority ν p θ
  sharp : ∀ p : ℝ, ∀ hp : 3 < p,
    CoulombTileTrials H L.rate (L.rootModulus H diff hp.le) .globalRoot 0 p (2/p)

/-- Theorem 3.3 with finite spin kinematics derived from the Coulomb
Hamiltonian. The finite tilings, Fock traces and local comparisons are explicit. -/
theorem levyLieb_tsga_of_reduced_traces {η : Mollifier} {K : ℝ}
    (H : FiniteEnergyInputs) (chain : WeakPhaseProduct) (sob : SobolevLipschitzComposition)
    (diff : SobolevDifferenceQuotients)
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (rate : FiniteRateTiling energy η K) (red : FockSpinCurrentTraces)
    (tiles : (CoulombGasInputs.of_reduced loc rate red).TileTrials H diff) :
    MainExtendedTSGAEstimate (referenceEnergies energy η) :=
  levyLieb_tsga_of_coulomb_tiles H _ chain sob diff tiles.general tiles.minority tiles.sharp

end TSGA.ManyBody
