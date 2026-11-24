import TSGA.Spin
import Mathlib.Analysis.Matrix.Order

/-! # Removal of spin density by a contraction

The spectral inverse of the positive square root is taken to be zero on its
kernel. Domination in the positive semidefinite order implies that the smaller
square root vanishes there as well.
-/

noncomputable section

namespace TSGA

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

private theorem hermitian_generalizedInverse {Y : SpinMatrix} (hY : Y.IsHermitian) :
    ∃ P : SpinMatrix, star P = P ∧ Y * P = P * Y ∧ Y * P * Y = Y := by
  let e := Unitary.conjStarAlgAut ℂ SpinMatrix hY.eigenvectorUnitary
  let d : Fin 2 → ℂ := fun i => (hY.eigenvalues i : ℂ)
  let D : SpinMatrix := diagonal d
  let J : SpinMatrix := diagonal (fun i => (d i)⁻¹)
  have hdiag : Y = e D := hY.spectral_theorem
  have hj : star J = J := by
    apply isHermitian_diagonal_iff.mpr
    intro i
    change star ((hY.eigenvalues i : ℂ)⁻¹) = _
    simp [d]
  have hcomm : D * J = J * D := by
    simp only [D, J, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hinv : D * J * D = D := by
    simp only [D, J, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_inv_mul_cancel (d i)
  refine ⟨e J, ?_, ?_, ?_⟩
  · rw [← map_star, hj]
  · rw [hdiag, ← map_mul, ← map_mul, hcomm]
  · rw [hdiag, ← map_mul, ← map_mul, hinv]

private theorem spin_sandwich_mono {A B : SpinMatrix} (h : A ≤ B) (C : SpinMatrix) :
    star C * A * C ≤ star C * B * C := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.star_eq_conjTranspose, mul_sub, sub_mul] using
    (Matrix.le_iff.mp h).conjTranspose_mul_mul_same C

/-- Every spin subdensity A of B arises by applying a contraction S. The
same S intertwines their positive square roots, including at singular B. -/
theorem exists_spinContraction {A B : SpinMatrix} (hA : A.PosSemidef)
    (hAB : (B - A).PosSemidef) :
    ∃ S : SpinMatrix, (1 - star S * S).PosSemidef ∧
      S * CFC.sqrt B = CFC.sqrt A ∧ S * B * star S = A := by
  let X := CFC.sqrt A
  let Y := CFC.sqrt B
  have hle := Matrix.le_iff.mpr hAB
  have hXX : X * X = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hYY : Y * Y = B := CFC.sqrt_mul_sqrt_self B (hA.nonneg.trans hle)
  have hX : star X = X := (CFC.sqrt_nonneg A).posSemidef.1
  have hY : star Y = Y := (CFC.sqrt_nonneg B).posSemidef.1
  obtain ⟨P, hP, hcomm, hYPY⟩ := hermitian_generalizedInverse hY
  let Q := P * Y
  have hQ : star Q = Q := by
    change star (P * Y) = P * Y
    rw [star_mul, hY, hP, hcomm]
  have hYQ : Y * Q = Y := by
    change Y * (P * Y) = Y
    rw [← mul_assoc, hYPY]
  have hQQ : Q * Q = Q := by
    change (P * Y) * Q = P * Y
    rw [mul_assoc, hYQ]
  let C := 1 - Q
  have hC : star C = C := by
    change star (1 - Q) = 1 - Q
    rw [star_sub, star_one, hQ]
  have hYC : Y * C = 0 := by
    change Y * (1 - Q) = 0
    rw [mul_sub, mul_one, hYQ, sub_self]
  have hCC : star C * C = C := by
    rw [hC]
    change (1 - Q) * (1 - Q) = 1 - Q
    rw [sub_mul, one_mul, mul_sub, mul_one, hQQ, sub_self, sub_zero]
  have hQle : Q ≤ 1 := by
    apply Matrix.le_iff.mpr
    change C.PosSemidef
    rw [← hCC]
    exact posSemidef_conjTranspose_mul_self C
  have hXC : X * C = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    apply le_antisymm _ (posSemidef_conjTranspose_mul_self (X * C)).nonneg
    calc
      star (X * C) * (X * C) = star C * A * C := by
        rw [star_mul, hX, ← hXX]
        simp only [mul_assoc]
      _ ≤ star C * B * C := spin_sandwich_mono hle C
      _ = 0 := by
        rw [← hYY]
        simp only [mul_assoc, hYC, mul_zero]
  have hXQ : X * Q = X := by
    change X * (1 - Q) = 0 at hXC
    rw [mul_sub, mul_one, sub_eq_zero] at hXC
    exact hXC.symm
  let S := X * P
  have hSY : S * Y = X := by
    change (X * P) * Y = X
    rw [mul_assoc]
    exact hXQ
  refine ⟨S, Matrix.le_iff.mp (?_ : star S * S ≤ 1), hSY, ?_⟩
  · calc
      star S * S = star P * A * P := by
        change star (X * P) * (X * P) = star P * A * P
        rw [star_mul, hX, ← hXX]
        simp only [mul_assoc]
      _ ≤ star P * B * P := spin_sandwich_mono hle P
      _ = Q * (Y * P) := by
        change star P * B * P = (P * Y) * (Y * P)
        rw [hP, ← hYY]
        simp only [mul_assoc]
      _ = Q * Q := by rw [hcomm]
      _ = Q := hQQ
      _ ≤ 1 := hQle
  · calc
      S * B * star S = (S * Y) * star (S * Y) := by
        rw [star_mul S Y, hY, ← hYY]
        simp only [mul_assoc]
      _ = A := by rw [hSY, hX, hXX]

end TSGA
