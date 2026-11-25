import TSGA.CoulombSpiral
import TSGA.RadialMollifier
import TSGA.BallSequence
import TSGA.GasConvexity
import TSGA.WavevectorRegularity

/-! # The SSW gas of the Coulomb constrained search

The vacuum, the trial ensembles, their greatest lower bounds and diagonal
spin averaging are fixed by the Coulomb model. The remaining finite-spin
inputs are the momentum, spin current and their transformation laws.
-/

noncomputable section

namespace TSGA.ManyBody

open SSW MeasureTheory
open scoped InnerProductSpace ComplexOrder

abbrev SpiralState (D : DomainSequence) (M : SpinMatrix) (n : ℕ) (q : Position) :=
  {Γ : MixedState // feasible (D.spiralField M n q) Γ}

def SpiralState.value {D : DomainSequence} {M : SpinMatrix} {n : ℕ} {q : Position}
    (s : SpiralState D M n q) : ℝ :=
  s.val.kinetic + s.val.interaction - hartree (fun x => (D.spiralField M n q x).trace.re)

theorem SpiralState.diagonalize {D : DomainSequence} {M : SpinMatrix} {n : ℕ} {q : Position}
    (s : SpiralState D M n q) : ∃ t : SpiralState D (diagonalSpin M) n 0, t.value = s.value := by
  obtain ⟨Λ, hk, hw, hd⟩ := s.val.exists_diagonal
  have h : feasible (D.spiralField (diagonalSpin M) n 0) Λ := by
    apply hd.trans
    filter_upwards [s.property] with x hx
    rw [hx, diagonal_spiral]
  refine ⟨⟨Λ, h⟩, ?_⟩
  simp only [value, hk, hw, ← diagonal_spiral D M n q, trace_diagonalSpin]

section

attribute [local irreducible] DomainSequence.spiralField feasible

/-- The remaining finite kinematics act on mixed states of the indicated
density. Energies below are the kinetic plus Coulomb expectations less the
direct term. The total charge and axial magnetization include the volume. -/
structure SpiralTransport (D : DomainSequence) (M : SpinMatrix) (n : ℕ) (ζ θ : ℝ) where
  momentum : SpiralState D M n 0 → Position
  spinCurrent : SpiralState D M n 0 → Position
  rotation : ∀ q, SpiralState D M n 0 ≃ SpiralState D M n q
  rotation_energy : ∀ q s, (rotation q s).value = s.value - ⟪q, spinCurrent s⟫_ℝ +
    ‖q‖^2 / 4 * (M.trace.re * D.vol n)
  planar : ∀ s : SpiralState D M n 0, ∃ t : SpiralState D M n 0,
    t.value = s.value ∧ momentum t = 0 ∧ spinCurrent t = 0
  boost : Position → SpiralState D M n 0 ≃ SpiralState D M n 0
  boost_energy : ∀ k s, (boost k s).value =
    s.value + 2 * ⟪k, momentum s⟫_ℝ + ‖k‖^2 * (M.trace.re * D.vol n)
  boost_momentum : ∀ k s, momentum (boost k s) = momentum s + (M.trace.re * D.vol n) • k
  boost_current : ∀ k s, spinCurrent (boost k s) = spinCurrent s + (thirdMagnetization M * D.vol n) • k
  aligned : ζ = 1 → ∀ s, spinCurrent s = Real.cos θ • momentum s

/-- The transport laws and one starting state determine the finite variational laws. -/
structure SpiralKinematics (D : DomainSequence) (M : SpinMatrix) (n : ℕ) (ζ θ : ℝ)
    extends SpiralTransport D M n ζ θ where
  represented : Nonempty (SpiralState D M n 0)

end

def SpiralKinematics.finiteSpinLaws {D : DomainSequence} {M : SpinMatrix} {n : ℕ} {ζ θ : ℝ}
    (H : SpiralKinematics D M n ζ θ) :
    FiniteSpinLaws M ζ θ (D.vol n) (fun A k => D.totalEnergy energy A n k) where
  State := SpiralState D M n 0
  stateEnergy := SpiralState.value
  momentum := H.momentum
  spinCurrent := H.spinCurrent
  RotatedState := SpiralState D M n
  rotatedEnergy _ := SpiralState.value
  search q := by
    obtain ⟨s⟩ := H.represented
    exact energy_isGLB ⟨_, (H.rotation q s).property⟩
  rotation := H.rotation
  rotationLaw := H.rotation_energy
  DiagonalState := SpiralState D (diagonalSpin M) n 0
  diagonalEnergy := SpiralState.value
  diagonalSearch := by
    obtain ⟨s⟩ := H.represented
    obtain ⟨t, _⟩ := s.diagonalize
    exact energy_isGLB ⟨_, t.property⟩
  average _ s := Classical.choose s.diagonalize
  averageLaw _ s := Classical.choose_spec s.diagonalize
  planarSymmetry := H.planar
  boost := H.boost
  boostEnergy := H.boost_energy
  boostMomentum := H.boost_momentum
  boostCurrent := H.boost_current
  aligned := H.aligned

theorem SpiralKinematics.representable {D : DomainSequence}
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ → ∀ n, SpiralKinematics D M n ζ θ)
    (M : SpinMatrix) (hM : M.PosSemidef) (n : ℕ) (q : Position) :
    ∃ Γ, feasible (D.spiralField M n q) Γ := by
  by_cases hr : 0 < M.trace.re
  · obtain ⟨ζ, θ, h⟩ := exists_spinParameters hM hr
    let H := states M ζ θ h n
    obtain ⟨s⟩ := H.represented
    exact ⟨_, (H.rotation q s).property⟩
  · have ht := RCLike.nonneg_iff.mp hM.trace_nonneg
    have hz := hM.trace_eq_zero_iff.mp (Complex.ext (le_antisymm (le_of_not_gt hr) ht.1) ht.2)
    refine ⟨MixedState.vacuum, ae_of_all _ fun x => ?_⟩
    ext i j
    simp [hz, DomainSequence.spiralField, MixedState.vacuum, MixedState.matrixDensity, PureState.matrixDensity]

/-- Theorem 3.1 for the Coulomb energy. It suffices to establish the spin
kinematics along the specific sequence of balls of radius n+1 and width one.
The resulting limit applies to every admissible domain sequence. -/
theorem coulomb_sswGas (η : Mollifier)
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ) :
    SSWGasTheorem (referenceEnergies energy η) :=
  sswGas_theorem η energy_vacuum loc (DomainSequence.balls unitBallMollifier)
    (fun M ζ θ h n => (states M ζ θ h n).finiteSpinLaws)

/-- The same finite inputs as the physical SSW gas theorem suffice for
fixed-charge convexity. They produce the trial states on the common balls. -/
theorem coulomb_ssw_convex_fixed_charge (η : Mollifier)
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    {ρ : ℝ} (hρ : 0 < ρ) (q : Position) :
    ConvexOn ℝ (fixedCharge ρ) (fun M => sswEnergy energy η M q) := by
  apply ssw_convex_fixed_charge (coulomb_sswGas η loc states) (DomainSequence.balls unitBallMollifier) q hρ
  intro M hM n
  exact SpiralKinematics.representable states M hM.1 n q

end TSGA.ManyBody
