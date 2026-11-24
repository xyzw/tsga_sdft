import TSGA.SSWDomain
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Spatial covariance of finite spin spirals

Equation `eq:covariance_spiral` expresses a translated spiral cutoff as a
translation followed by a constant spin rotation. A rotation of the cutoff
rotates the wavevector in the opposite coordinate change.
-/

namespace TSGA.SSW

open scoped Matrix InnerProductSpace

theorem spinRotation_add (a b : ℝ) : spinRotation (a + b) = spinRotation a * spinRotation b := by
  unfold spinRotation
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  rw [← phaseFactor_add]
  apply congrArg phaseFactor
  change (if i = 0 then -((a + b) / 2) else (a + b) / 2) =
    (if i = 0 then -(a / 2) else a / 2) + (if i = 0 then -(b / 2) else b / 2)
  split_ifs <;> ring

theorem rotate_add (a b : ℝ) (M : SpinMatrix) : rotate (a + b) M = rotate a (rotate b M) := by
  simp only [rotate, spinRotation_add, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem rotate_smul (a : ℝ) (c : ℂ) (M : SpinMatrix) : rotate a (c • M) = c • rotate a M := by
  simp only [rotate, Matrix.mul_smul, Matrix.smul_mul]

/-- Pointwise identity for translation of the cutoff by `τ`. -/
theorem cutoffSpiral_translate (f : Position → ℝ) (M : SpinMatrix) (q τ x : Position) :
    cutoffSpiral (fun y => f (y - τ)) M q x =
      rotate (⟪q, τ⟫_ℝ) (cutoffSpiral f M q (x - τ)) := by
  have hphase : ⟪q, τ⟫_ℝ + (⟪q, x⟫_ℝ - ⟪q, τ⟫_ℝ) = ⟪q, x⟫_ℝ := by ring
  simp only [cutoffSpiral, rotate_smul, ← rotate_add, inner_sub_right, hphase]

/-- Covariance under a real linear isometry, in particular under any rotation. -/
theorem cutoffSpiral_isometry (f : Position → ℝ) (M : SpinMatrix) (q x : Position)
    (R : Position ≃ₗᵢ[ℝ] Position) :
    cutoffSpiral (fun y => f (R y)) M q x = cutoffSpiral f M (R q) (R x) := by
  simp only [cutoffSpiral, R.inner_map_map]

/-- Translation invariance of the spiral energy with a translated cutoff, from
translation invariance of the functional and invariance under global spin rotations. -/
theorem spiralEnergy_translate (E : (Position → SpinMatrix) → ℝ)
    (hshift : ∀ (F : Position → SpinMatrix) (τ : Position), E (fun x => F (x - τ)) = E F)
    (hspin : ∀ (F : Position → SpinMatrix) (a : ℝ), E (fun x => rotate a (F x)) = E F)
    (f : Position → ℝ) (M : SpinMatrix) (q τ : Position) :
    E (cutoffSpiral (fun x => f (x - τ)) M q) = E (cutoffSpiral f M q) := by
  have hfield := funext (cutoffSpiral_translate f M q τ)
  rw [hfield, hspin, hshift]

/-- Energy covariance for every spatial rotation preserving the functional. -/
theorem spiralEnergy_isometry (E : (Position → SpinMatrix) → ℝ) (R : Position ≃ₗᵢ[ℝ] Position)
    (hspace : ∀ F : Position → SpinMatrix, E (fun x => F (R x)) = E F)
    (f : Position → ℝ) (M : SpinMatrix) (q : Position) :
    E (cutoffSpiral (fun x => f (R x)) M q) = E (cutoffSpiral f M (R q)) := by
  have hfield := funext (fun x => cutoffSpiral_isometry f M q x R)
  rw [hfield, hspace]

end TSGA.SSW
