import TSGA.SpinMomentumEnsemble

/-! # Fourier spin density of a finite-sector wave

Momenta are angular frequencies, so the weak derivative has symbol `i p`.
The scalar Plancherel theorem and its first-derivative form are used in
`SectorPlancherelMoments`, independently of any localization of states.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

/-- The spatial or momentum spin matrix tested on a measurable set. -/
def positionProbe (E : Set Position) (P : Position → SpinMatrix) : SpinMatrix :=
  fun i j => ∫ x in E, P x i j

/-- The unitary scalar Fourier transform on configuration space. The kernel
fixes both its normalization and the sign of the current on the dense
subspace of integrable square-integrable functions. -/
structure SectorFourierTransform where
  transform (n : ℕ) : Lp ℂ 2 (volume : Measure (Space n)) ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (Space n))
  kernel (n : ℕ) (u : Space n → ℂ) (h₂ : MemLp u 2 volume) (h₁ : Integrable u) :
    (transform n (h₂.toLp u) : Space n → ℂ) =ᵐ[volume] fun p =>
      (((2 * Real.pi) ^ (-((3 * n : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ∫ x, Complex.exp (-(∑ i, (⟪p i, x i⟫_ℝ : ℂ)) * Complex.I) * u x

def SectorFourierTransform.amplitude (F : SectorFourierTransform) {n : ℕ} (ψ : Wave n)
    (s : Spins n) : Space n → ℂ := F.transform n ((ψ.square_integrable s).toLp (ψ.value s))

/-- Spin marginal in the first Fourier variable. Antisymmetry supplies the
sector particle-number factor, as in `Wave.matrixDensity`. -/
def SectorFourierTransform.profile (F : SectorFourierTransform) : PureState → Position → SpinMatrix
  | .vacuum => 0
  | .occupied (n := n) ψ => fun p i j => (n+1 : ℕ) * ∑ s : Spins n, ∫ y : Space n,
      F.amplitude ψ (Fin.cons i s) (Fin.cons p y) * conj (F.amplitude ψ (Fin.cons j s) (Fin.cons p y))

/-- Sectorwise Plancherel in marginal form. The zeroth, signed first and
second moments represent mass, momentum and the weak-derivative energy of
the original wave. This input refers only to an individual occupied wave. -/
def SectorPlancherelMoments (F : SectorFourierTransform) : Prop := ∀ {n : ℕ} (ψ : Wave (n+1)),
  PureSpinMomentumDistribution (.occupied ψ) (F.profile (.occupied ψ))

theorem SectorPlancherelMoments.pure {F : SectorFourierTransform} (h : SectorPlancherelMoments F)
    (s : PureState) : PureSpinMomentumDistribution s (F.profile s) := by
  cases s with
  | occupied ψ => exact h ψ
  | vacuum =>
    constructor <;> simp [SectorFourierTransform.profile,PureState.matrixDensity,PureState.kinetic,
      PureState.spinMomentum,momentumKinetic,momentumMoment,momentumAxial,axialTest]
    exact Matrix.PosSemidef.zero

end TSGA.ManyBody
