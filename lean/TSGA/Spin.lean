import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Spin density matrices and rotations about the third axis

This file formalizes the spin matrix of the introduction and the rotations in
`eq:def_U_q` and `eq:def_U_phi` in `tsga.tex`. The phase is real and measured
in radians. The lower off-diagonal entry represents the positive azimuthal
phase in the convention of the manuscript.
-/

namespace TSGA

open scoped Matrix ComplexOrder

abbrev SpinMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Pointwise spin density matrix in terms of charge and the three real
components of magnetization. Physical admissibility also requires positivity. -/
noncomputable def spinDensity (ρ mx my mz : ℝ) : SpinMatrix :=
  !![((ρ + mz : ℝ) : ℂ) / 2, ((mx : ℂ) - Complex.I * (my : ℂ)) / 2;
     ((mx : ℂ) + Complex.I * (my : ℂ)) / 2, ((ρ - mz : ℝ) : ℂ) / 2]

/-- The complex transverse magnetization, with real part `m₁` and imaginary part `m₂`. -/
def transverseMagnetization (M : SpinMatrix) : ℂ := 2 * M 1 0

/-- The complex scalar `exp(iφ)`. -/
noncomputable def phaseFactor (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * Complex.I)

@[simp] theorem phaseFactor_zero : phaseFactor 0 = 1 := by simp [phaseFactor]

theorem phaseFactor_add (φ ψ : ℝ) :
    phaseFactor (φ + ψ) = phaseFactor φ * phaseFactor ψ := by
  simp [phaseFactor, add_mul, Complex.exp_add]

@[simp] theorem star_phaseFactor (φ : ℝ) : star (phaseFactor φ) = phaseFactor (-φ) := by
  change (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  simp

private noncomputable def spinAngle (φ : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then -(φ / 2) else φ / 2

/-- The diagonal spin rotation with phases `−φ/2` and `φ/2`. -/
noncomputable def spinRotation (φ : ℝ) : SpinMatrix :=
  Matrix.diagonal (fun i => phaseFactor (spinAngle φ i))

/-- Rotate a spin density matrix by unitary conjugation about the third axis. -/
noncomputable def rotate (φ : ℝ) (M : SpinMatrix) : SpinMatrix :=
  spinRotation φ * M * (spinRotation φ)ᴴ

private theorem rotate_entry (φ : ℝ) (M : SpinMatrix) (i j : Fin 2) :
    rotate φ M i j = phaseFactor (spinAngle φ i - spinAngle φ j) * M i j := by
  simp only [rotate, spinRotation, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.star_apply, star_phaseFactor, sub_eq_add_neg, phaseFactor_add]
  ring

@[simp] theorem rotate_zero (M : SpinMatrix) : rotate 0 M = M := by
  ext i j
  simp [rotate_entry, spinAngle]

/-- The two opposite half phases give a rotation in SU(2). -/
theorem spinRotation_mem_specialUnitaryGroup (φ : ℝ) :
    spinRotation φ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · have h : rotate φ 1 = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [rotate_entry, Matrix.one_apply, hij]
    simpa [rotate, Matrix.star_eq_conjTranspose] using h
  · simp [spinRotation, Matrix.det_diagonal, Fin.prod_univ_two, spinAngle, ← phaseFactor_add]

@[simp] theorem rotate_diag (φ : ℝ) (M : SpinMatrix) (i : Fin 2) :
    rotate φ M i i = M i i := by simp [rotate_entry]

@[simp] theorem trace_rotate (φ : ℝ) (M : SpinMatrix) :
    (rotate φ M).trace = M.trace := by simp [Matrix.trace_fin_two]

theorem rotate_posSemidef (φ : ℝ) {M : SpinMatrix} (h : M.PosSemidef) :
    (rotate φ M).PosSemidef :=
  h.mul_mul_conjTranspose_same (spinRotation φ)

/-- A rotation through `φ` multiplies the transverse magnetization by `exp(iφ)`. -/
theorem transverseMagnetization_rotate (φ : ℝ) (M : SpinMatrix) :
    transverseMagnetization (rotate φ M) = phaseFactor φ * transverseMagnetization M := by
  have h : spinAngle φ 1 - spinAngle φ 0 = φ := by simp [spinAngle]
  rw [transverseMagnetization, rotate_entry, h, transverseMagnetization]
  ring

@[simp] theorem trace_spinDensity (ρ mx my mz : ℝ) :
    (spinDensity ρ mx my mz).trace = (ρ : ℂ) := by
  simp [Matrix.trace_fin_two, spinDensity]
  ring

theorem spinDensity_isHermitian (ρ mx my mz : ℝ) :
    (spinDensity ρ mx my mz).IsHermitian := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.conjTranspose_apply, spinDensity]
  all_goals ring

@[simp] theorem transverseMagnetization_spinDensity (ρ mx my mz : ℝ) :
    transverseMagnetization (spinDensity ρ mx my mz) = (mx : ℂ) + Complex.I * (my : ℂ) := by
  simp [transverseMagnetization, spinDensity]
  ring

end TSGA
