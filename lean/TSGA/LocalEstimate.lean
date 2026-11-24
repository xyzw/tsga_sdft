import TSGA.Sobolev

/-! # The TSGA bound and its zero-phase specialization

The main localization inequality is a named proposition. The implication to
the LSDA is proved here for every density class, exponent and constant. The
statements use real integrals and cover the finite-error case of the manuscript.
-/

namespace TSGA

open MeasureTheory
open scoped ComplexOrder

/-- The energy functional and the two reference energy densities. The identity
at zero wavevector is the thermodynamic input to the LSDA corollary. -/
structure GasEnergies where
  energy : (Position → SpinMatrix) → ℝ
  ssw : SpinMatrix → Position → ℝ
  ueg : SpinMatrix → ℝ
  zero_mode : ∀ M : SpinMatrix, M.PosSemidef → ssw M 0 = ueg M

noncomputable def lsdaError (D : Density) (S T : MatrixGradient) (p b C ε : ℝ) : ℝ :=
  ε * (∫ x, D.charge x + D.charge x ^ 2) +
    C * (1 + ε) / ε * (∫ x, matrixGradNorm S x ^ 2) +
    C / ε ^ b * (∫ x, matrixGradNorm T x ^ p)

/-- The final integral uses the weak gradient of the `1/p` power only on the
region where the phase gradient is nonzero. -/
noncomputable def tsgaError (D : Density) (φ : Phase) (S T G : MatrixGradient)
    (p b C ε : ℝ) : ℝ :=
  ε * (∫ x, D.charge x + D.charge x ^ 2 + D.charge x * ‖φ.grad x‖ ^ 2) +
    C * (1 + ε) / ε * (∫ x, matrixGradNorm S x ^ 2) +
    C / ε ^ b * (∫ x, matrixGradNorm T x ^ p) +
    C / ε ^ (2 * p - 1) * ((∫ x, D.charge x * φ.hessianNorm x ^ p) +
      ∫ x in φ.active, ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p)

@[simp] theorem tsgaError_zero (D : Density) (S T G : MatrixGradient) {p : ℝ}
    (hp : 0 < p) (b C ε : ℝ) :
    tsgaError D Phase.zero S T G p b C ε = lsdaError D S T p b C ε := by
  simp [tsgaError, lsdaError, Phase.zero, Phase.hessianNorm, Phase.active,
    Real.zero_rpow hp.ne']

/-- The additional phase hypotheses in the finite-error case. The last two
conditions make explicit when the nonnegative remainder integrals are finite. -/
structure PhaseAdmissible (D : Density) (p : ℝ) (φ : Phase) (G : MatrixGradient) : Prop where
  regular : φ.Regular p
  root_regular : RootRegularOn φ.active D p G
  kinetic : Integrable (fun x => D.charge x * ‖φ.grad x‖ ^ 2)
  curvature : Integrable (fun x => D.charge x * φ.hessianNorm x ^ p)
  root_weighted : IntegrableOn (fun x => ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p) φ.active

@[simp] theorem phaseAdmissible_zero (D : Density) {p : ℝ} (hp : 0 < p)
    (G : MatrixGradient) : PhaseAdmissible D p Phase.zero G := by
  refine ⟨regular_zero p, ?_, ?_, ?_, ?_⟩
  · rw [active_zero]
    exact rootRegularOn_empty D p G
  · simp [Phase.zero]
  · simp [Phase.hessianNorm, Phase.zero, Real.zero_rpow hp.ne']
  · simp [Phase.zero, Phase.active]

/-- Finite-error statement of the principal TSGA inequality, for a fixed
density class and a constant uniform over that class and all phases and ε. -/
def TSGAEstimate (F : GasEnergies) (classOf : Density → Prop) (p θ b C : ℝ) : Prop :=
  ∀ (D : Density) (S T : MatrixGradient), classOf D → DensityRegular D p θ S T →
    ∀ (φ : Phase) (G : MatrixGradient), PhaseAdmissible D p φ G → ∀ ε : ℝ, 0 < ε →
      Integrable (fun x => F.ssw (D.matrix x) (φ.grad x)) ∧
      |F.energy (fun x => rotate (φ.value x) (D.matrix x)) -
        ∫ x, F.ssw (D.matrix x) (φ.grad x)| ≤ tsgaError D φ S T G p b C ε

/-- The LSDA inequality with the same constant and no hypothesis on the
`1/p` density power. -/
def LSDAEstimate (F : GasEnergies) (classOf : Density → Prop) (p θ b C : ℝ) : Prop :=
  ∀ (D : Density) (S T : MatrixGradient), classOf D → DensityRegular D p θ S T →
    ∀ ε : ℝ, 0 < ε → Integrable (fun x => F.ueg (D.matrix x)) ∧
      |F.energy D.matrix - ∫ x, F.ueg (D.matrix x)| ≤ lsdaError D S T p b C ε

/-- Corollary `cor:LSDA` from `thm:LSSWA`. The proof chooses the zero field
as a gradient witness on the empty active set. -/
theorem lsda_of_tsga {F : GasEnergies} {classOf : Density → Prop} {p θ b C : ℝ}
    (hp : 0 < p) (h : TSGAEstimate F classOf p θ b C) : LSDAEstimate F classOf p θ b C := by
  intro D S T hclass hregular ε hε
  have hz := h D S T hclass hregular Phase.zero 0 (phaseAdmissible_zero D hp 0) ε hε
  rw [tsgaError_zero D S T 0 hp] at hz
  simpa [Phase.zero, F.zero_mode _ (D.positive _)] using hz

/-- The polarization condition of the improved estimate, in the matrix order. -/
def MinorityBound (ν : ℝ) (D : Density) : Prop :=
  ∀ᵐ x ∂volume, (D.matrix x - ((ν * D.charge x : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef

end TSGA
