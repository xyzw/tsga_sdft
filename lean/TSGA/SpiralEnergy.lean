import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite-system spin spirals

This module proves the variational claims of the theorem labelled `thm:spirals` in
`tsga.tex`. For a fixed spin density matrix, `State` indexes the admissible
finite-kinetic-energy states having this density matrix. The constrained
search, spin rotations, averaging operations, and Galilean boosts enter
through their stated actions on energies and currents.
-/

namespace TSGA.FiniteSpiral

open scoped InnerProductSpace

abbrev Wavevector := EuclideanSpace ℝ (Fin 3)

variable {State : Type*}

/-- Equation `eq:spiral_formula`, expressed as a greatest lower bound in ℝ.
Here `particles` is the integral of the charge density and `energy q` is the
constrained energy of its spin spiral at wavevector `q`. -/
def VariationalFormula (stateEnergy : State → ℝ) (spinCurrent : State → Wavevector)
    (particles : ℝ) (energy : Wavevector → ℝ) : Prop :=
  ∀ q, IsGLB (Set.range fun s => stateEnergy s - ⟪q, spinCurrent s⟫_ℝ)
    (energy q - ‖q‖ ^ 2 / 4 * particles)

/-- The constrained-search definition and the change of energy under the
spin-rotation bijection imply equation `eq:spiral_formula`. -/
theorem variationalFormula_of_rotation {RotatedState : Wavevector → Type*}
    {stateEnergy : State → ℝ} {rotatedEnergy : (q : Wavevector) → RotatedState q → ℝ}
    {spinCurrent : State → Wavevector} {particles : ℝ} {energy : Wavevector → ℝ}
    (hsearch : ∀ q, IsGLB (Set.range (rotatedEnergy q)) (energy q))
    (rotate : (q : Wavevector) → State ≃ RotatedState q)
    (hrotate : ∀ q s, rotatedEnergy q (rotate q s) =
      stateEnergy s - ⟪q, spinCurrent s⟫_ℝ + ‖q‖ ^ 2 / 4 * particles) :
    VariationalFormula stateEnergy spinCurrent particles energy := by
  intro q
  constructor
  · rintro _ ⟨s, rfl⟩
    have hs := (hsearch q).1 (Set.mem_range_self (rotate q s))
    rw [hrotate] at hs
    exact sub_le_iff_le_add.mpr hs
  · intro z hz
    apply le_sub_iff_add_le.mpr
    apply (hsearch q).2
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := (rotate q).surjective t
    rw [hrotate]
    exact add_le_add_left (hz (Set.mem_range_self s)) _

/-- Part (i). Subtracting the quadratic energy of the rotation leaves a
concave function of the wavevector. -/
theorem correctedEnergy_concave {stateEnergy : State → ℝ}
    {spinCurrent : State → Wavevector} {particles : ℝ} {energy : Wavevector → ℝ}
    (hvar : VariationalFormula stateEnergy spinCurrent particles energy) :
    ConcaveOn ℝ Set.univ (fun q => energy q - ‖q‖ ^ 2 / 4 * particles) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply (hvar (a • x + b • y)).2
  rintro _ ⟨s, rfl⟩
  have hx := (hvar x).1 (Set.mem_range_self s)
  have hy := (hvar y).1 (Set.mem_range_self s)
  simp only [smul_eq_mul, inner_add_left, real_inner_smul_left]
  calc
    _ ≤ a * (stateEnergy s - ⟪x, spinCurrent s⟫_ℝ) +
        b * (stateEnergy s - ⟪y, spinCurrent s⟫_ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = _ := by linear_combination (stateEnergy s) * hab

/-- The lower bound in part (ii). Averaging a spiral state with its rotation
by a half turn about the third axis gives a state of the diagonal density
with the same energy. Here both state types are for a fixed wavevector. -/
theorem diagonalEnergy_le {SpiralState DiagonalState : Type*}
    {spiral : SpiralState → ℝ} {diagonal : DiagonalState → ℝ}
    {spiralEnergy diagonalEnergy : ℝ}
    (hspiral : IsGLB (Set.range spiral) spiralEnergy)
    (hdiagonal : IsGLB (Set.range diagonal) diagonalEnergy)
    (average : SpiralState → DiagonalState)
    (haverage : ∀ s, diagonal (average s) = spiral s) :
    diagonalEnergy ≤ spiralEnergy := by
  apply hspiral.2
  rintro _ ⟨s, rfl⟩
  rw [← haverage]
  exact hdiagonal.1 (Set.mem_range_self _)

/-- The upper bound in part (ii). For magnetization in a fixed plane through
the third axis, complex conjugation and averaging in suitable spin coordinates
provide the state in `hsymmetric`.
A scalar Galilean boost changes the spin current by the integrated third
magnetization times the boost wavevector. -/
theorem planar_energy_le {stateEnergy : State → ℝ} {momentum spinCurrent : State → Wavevector}
    {particles magnetization : ℝ} {energy : Wavevector → ℝ}
    (hvar : VariationalFormula stateEnergy spinCurrent particles energy)
    (hparticles : 0 < particles)
    (hsymmetric : ∀ s, ∃ t, stateEnergy t = stateEnergy s ∧ momentum t = 0 ∧ spinCurrent t = 0)
    (boost : Wavevector → State → State)
    (henergy : ∀ k s, stateEnergy (boost k s) =
      stateEnergy s + 2 * ⟪k, momentum s⟫_ℝ + ‖k‖ ^ 2 * particles)
    (hcurrent : ∀ k s, spinCurrent (boost k s) = spinCurrent s + magnetization • k)
    (q : Wavevector) :
    energy q ≤ energy 0 + ‖q‖ ^ 2 / 4 * (particles - magnetization ^ 2 / particles) := by
  let a := magnetization / (2 * particles)
  let k := a • q
  let correction := ‖q‖ ^ 2 / 4 * (particles - magnetization ^ 2 / particles)
  have hzero : IsGLB (Set.range stateEnergy) (energy 0) := by simpa using hvar 0
  suffices energy q - correction ≤ energy 0 by
    dsimp [correction] at this
    linarith
  apply hzero.2
  rintro _ ⟨s, rfl⟩
  obtain ⟨t, ht, hp, hj⟩ := hsymmetric s
  have hs := (hvar q).1 (Set.mem_range_self (boost k t))
  change energy q - ‖q‖ ^ 2 / 4 * particles ≤ stateEnergy (boost k t) -
    ⟪q, spinCurrent (boost k t)⟫_ℝ at hs
  rw [henergy, hcurrent, hp, hj, ht] at hs
  simp only [inner_zero_right, mul_zero, add_zero, zero_add, k, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right, real_inner_self_eq_norm_sq] at hs
  have hcorr : correction = ‖q‖ ^ 2 / 4 * particles + a ^ 2 * ‖q‖ ^ 2 * particles -
      magnetization * (a * ‖q‖ ^ 2) := by
    dsimp [correction, a]
    field_simp [ne_of_gt hparticles]
    ring
  linarith only [hs, hcorr]

/-- Part (iii). For full polarization the spin current is the scalar multiple
`c` of the total momentum, where physically `c = n₀ · e₃`. A boost is a
bijection on the constrained states. Its two transformation laws are the
zero-spin-rotation case of `eq:kinetic_spiral` and the associated momentum shift. -/
theorem fullyPolarized_energy {stateEnergy : State → ℝ}
    {momentum spinCurrent : State → Wavevector} {particles c : ℝ}
    {energy : Wavevector → ℝ}
    (hvar : VariationalFormula stateEnergy spinCurrent particles energy)
    (haligned : ∀ s, spinCurrent s = c • momentum s)
    (boost : Wavevector → State ≃ State)
    (henergy : ∀ k s, stateEnergy (boost k s) =
      stateEnergy s + 2 * ⟪k, momentum s⟫_ℝ + ‖k‖ ^ 2 * particles)
    (hmomentum : ∀ k s, momentum (boost k s) = momentum s + particles • k)
    (q : Wavevector) :
    energy q = energy 0 + ‖q‖ ^ 2 / 4 * (1 - c ^ 2) * particles := by
  let k := (c / 2) • q
  let shift := c ^ 2 * ‖q‖ ^ 2 / 4 * particles
  have shifted (s : State) :
      stateEnergy (boost k s) - ⟪q, spinCurrent (boost k s)⟫_ℝ = stateEnergy s - shift := by
    rw [henergy, haligned, hmomentum]
    simp only [k, shift, inner_add_right, real_inner_smul_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hzero : IsGLB (Set.range stateEnergy) (energy 0) := by simpa using hvar 0
  let corrected := energy q - ‖q‖ ^ 2 / 4 * particles
  have lower : energy 0 - shift ≤ corrected := by
    apply (hvar q).2
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := (boost k).surjective t
    change energy 0 - shift ≤ stateEnergy (boost k s) - ⟪q, spinCurrent (boost k s)⟫_ℝ
    rw [shifted]
    exact sub_le_sub_right (hzero.1 (Set.mem_range_self s)) shift
  have upper : corrected + shift ≤ energy 0 := by
    apply hzero.2
    rintro _ ⟨s, rfl⟩
    have hs := (hvar q).1 (Set.mem_range_self (boost k s))
    change corrected ≤ stateEnergy (boost k s) - ⟪q, spinCurrent (boost k s)⟫_ℝ at hs
    rw [shifted] at hs
    linarith
  dsimp [corrected, shift] at lower upper
  linarith only [lower, upper]

end TSGA.FiniteSpiral
