import TSGA.CoulombGas
import TSGA.CutoffFisher
import TSGA.CutoffRepresentability
import TSGA.TetrahedronCoulomb

/-! # Finite Coulomb states on the reference balls

The square root of the smoothed indicator has an L² weak gradient. The cutoff
representability theorem hence constructs a state at zero wavevector, also
when the constant spin matrix has a zero eigenvalue.
-/

noncomputable section
namespace TSGA.ManyBody
open SSW MeasureTheory
open scoped ComplexOrder

/-- Every bounded open domain in an admissible sequence supplies a starting
state for spin transport at the smoothing width of that domain. -/
theorem SpiralState.nonempty_of_cutoff (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (D : SSW.DomainSequence) {M : SpinMatrix} (hM : M.PosSemidef) (n : ℕ) :
    Nonempty (SpiralState D M n 0) := by
  have hi : Integrable (D.cutoff n) := Integrable.of_integral_ne_zero ((D.cutoff_mass n).trans_ne (D.vol_pos n).ne')
  obtain ⟨g, hw, hg⟩ := smoothedIndicator_sqrt_sobolev sob (D.region_open n).measurableSet
    (D.region_bounded n).measure_lt_top.ne D.mollifier (D.delta_pos n)
  obtain ⟨Γ, hΓ⟩ := H.representable_cutoff
    (f := D.cutoff n) (fun x => (smoothedIndicator_bounds _ D.mollifier (D.delta_pos n) x).1) hi g hw hg hM
  refine ⟨⟨Γ,hΓ.trans (ae_of_all _ fun x => ?_)⟩⟩
  rw [SSW.DomainSequence.spiralField, cutoffSpiral_zero_wavevector]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- On the balls of radius n+1 and smoothing width one the transport family
alone suffices to recover all the finite spin kinematics. -/
def ballSpiralKinematics (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients)
    (transport : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralTransport (SSW.DomainSequence.balls unitBallMollifier) M n ζ θ)
    (M : SpinMatrix) (ζ θ : ℝ) (hM : SpinParameters M ζ θ) (n : ℕ) :
    SpiralKinematics (SSW.DomainSequence.balls unitBallMollifier) M n ζ θ :=
  { transport M ζ θ hM n with
    represented := SpiralState.nonempty_of_cutoff H sob _ hM.positive n }

end TSGA.ManyBody
