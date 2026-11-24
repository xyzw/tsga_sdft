import TSGA.KineticEnergy

/-! # Local spin rotations of the many-body energy

The state map for a local unitary is sectorwise multiplication by its tensor
power. It preserves the interaction and has a quadratic kinetic cross term.
The constrained-search proof does not require the existence of a minimizer.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory
open scoped ComplexOrder

/-- The trace and positivity of a spin density are preserved under conjugation
by a spatially dependent unitary. -/
def conjugatedDensity (D : Density) (U : Position → unitary SpinMatrix) : Density where
  matrix x := (U x : SpinMatrix) * D.matrix x * star (U x : SpinMatrix)
  positive x := (D.positive x).mul_mul_conjTranspose_same _

@[simp] theorem conjugated_charge (D : Density) (U : Position → unitary SpinMatrix) (x : Position) :
    (conjugatedDensity D U).charge x = D.charge x := by
  simp [Density.charge, conjugatedDensity, Matrix.trace_mul_cycle]

/-- Single-state formulas for the tensor-power rotation. `rotationCost`
is a common upper bound on the squared gradient acting on the state, such as
∫ρ‖∇U‖². The mixed term satisfies the kinetic Cauchy–Schwarz inequality. -/
def RotationLaw (D : Density) (U : Position → unitary SpinMatrix) (rotationCost : ℝ) : Prop :=
  ∀ Γ : MixedState, feasible D.matrix Γ → ∃ Γ' : MixedState,
    feasible (conjugatedDensity D U).matrix Γ' ∧ Γ'.interaction = Γ.interaction ∧
    ∃ g j : ℝ, 0 ≤ g ∧ g ≤ rotationCost ∧ j^2 ≤ Γ.kinetic * g ∧
      Γ'.kinetic = Γ.kinetic + 2*j + g

/-- ε-Young bound on the kinetic cross term; the bound applies to either sign. -/
theorem gauge_cross {k g j ε : ℝ} (hk : 0 ≤ k) (hg : 0 ≤ g) (hj : j^2 ≤ k*g) (hε : 0 < ε) :
    2*j ≤ ε*k + g/ε := by
  apply (le_of_sq_le_sq _ (add_nonneg (mul_nonneg hε.le hk) (div_nonneg hg hε.le)))
  have hz := sq_nonneg (ε*k - g/ε)
  have hcancel : ε*k*(g/ε) = k*g := by field_simp
  nlinarith only [hz, hj, hcancel]

/-- Lemma on local spin rotations for the Coulomb Levy–Lieb functional. -/
theorem local_rotation_bound {D : Density} {U : Position → unitary SpinMatrix} {W ε L : ℝ}
    (hε : 0 < ε) (rep : ∃ Γ, feasible D.matrix Γ) (rot : RotationLaw D U W)
    (lo : ∀ Γ, feasible D.matrix Γ → hartree D.charge - L * chargeMoment D (4/3) ≤ Γ.interaction) :
    energy (conjugatedDensity D U).matrix ≤ (1+ε)*energy D.matrix +
      ε*L*chargeMoment D (4/3) + (1+1/ε)*W := by
  let D' := conjugatedDensity D U
  let d := hartree D.charge
  let cost := ε*L*chargeMoment D (4/3) + (1+1/ε)*W
  have hpos : 0 < 1 + ε := by linarith
  have hLower : (energy D'.matrix - cost) / (1+ε) + d ≤ levyLieb D.matrix := by
    apply le_levyLieb rep
    intro Γ hΓ
    obtain ⟨Γ', hΓ', hW, g, j, hg, hgW, hj, hk⟩ := rot Γ hΓ
    have hq := gauge_cross Γ.kinetic_nonneg hg hj hε
    have hab := levyLieb_le hΓ'
    rw [hk, hW] at hab
    have hi := lo Γ hΓ
    have hg' := mul_le_mul_of_nonneg_left hgW (show 0 ≤ 1+1/ε by positivity)
    have he : energy D'.matrix = levyLieb D'.matrix - d := by
      unfold energy d
      congr 1
      exact congrArg hartree (funext (conjugated_charge D U))
    rw [he, ← le_sub_iff_add_le, div_le_iff₀ hpos]
    change _ - (ε*L*chargeMoment D (4/3) + (1+1/ε)*W) ≤ _
    dsimp [d] at *
    change levyLieb D'.matrix ≤ _ at hab
    simp only [div_eq_mul_inv] at hq hg' ⊢
    linarith only [hab, hq, hg', mul_le_mul_of_nonneg_left hi hε.le]
  have h := (div_le_iff₀ hpos).mp ((le_sub_iff_add_le).mpr hLower)
  change energy D'.matrix ≤ (1+ε) * (levyLieb D.matrix - d) + _ + _
  dsimp only [cost] at h
  linarith only [h]

end TSGA.ManyBody
