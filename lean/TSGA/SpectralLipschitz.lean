import TSGA.Sobolev

/-! # Hilbert–Schmidt Lipschitz comparison in two spectral bases

The left and right eigenvectors may differ. In these bases an entry of
`f(A) − f(B)` is the scalar difference of the two eigenvalues of the
functional calculus times their eigenvector overlap.
-/

noncomputable section

namespace TSGA.Localization

open Matrix Unitary
open scoped ComplexOrder

/-- The Hilbert–Schmidt norm for spin matrices. -/
def hilbertSchmidt (M : SpinMatrix) : ℝ := √(∑ i, ∑ j, ‖M i j‖ ^ 2)

theorem hs_trace (M : SpinMatrix) :
    (∑ i, ∑ j, ‖M i j‖ ^ 2) = (M * star M).trace.re := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.sq_norm, Complex.mul_conj]

theorem hs_unitary (M : SpinMatrix) (U V : unitary SpinMatrix) :
    hilbertSchmidt ((star U : SpinMatrix) * M * V) = hilbertSchmidt M := by
  simp only [hilbertSchmidt, hs_trace]
  congr 2
  let S : SpinMatrix := star U
  have hv : (V : SpinMatrix) * star (V : SpinMatrix) = 1 := Unitary.coe_mul_star_self V
  have hu : star S * S = 1 := Unitary.coe_star_mul_self (star U)
  change ((S * M * V) * star (S * M * V)).trace = _
  rw [star_mul, star_mul]
  calc
    _ = (S * (M * ((V : SpinMatrix) * star (V : SpinMatrix)) * star M) * star S).trace := by
      simp only [mul_assoc]
    _ = (S * (M * star M) * star S).trace := by rw [hv, mul_one]
    _ = _ := by rw [trace_mul_cycle, hu, one_mul]

theorem mixed_cfc {A B : SpinMatrix} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) (i j : Fin 2) :
    ((star hA.eigenvectorUnitary : SpinMatrix) * (hA.cfc f - hB.cfc f) * hB.eigenvectorUnitary) i j =
      ((f (hA.eigenvalues i) - f (hB.eigenvalues j) : ℝ) : ℂ) *
        ((star hA.eigenvectorUnitary : SpinMatrix) * hB.eigenvectorUnitary) i j := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let P : SpinMatrix := diagonal (fun i => (f (hA.eigenvalues i) : ℂ))
  let Q : SpinMatrix := diagonal (fun j => (f (hB.eigenvalues j) : ℂ))
  change ((star U : SpinMatrix) * (↑U * P * (star U : SpinMatrix) - ↑V * Q * (star V : SpinMatrix)) *
    (V : SpinMatrix)) i j = _
  have hh : (star U : SpinMatrix) * (↑U * P * (star U : SpinMatrix) - ↑V * Q * (star V : SpinMatrix)) *
      (V : SpinMatrix) = P * ((star U : SpinMatrix) * V) - ((star U : SpinMatrix) * V) * Q := by
    rw [mul_sub, sub_mul]
    congr 1
    · calc
        _ = ((star U : SpinMatrix) * U) * P * ((star U : SpinMatrix) * V) := by simp only [mul_assoc]
        _ = _ := by rw [Unitary.coe_star_mul_self, one_mul]
    · calc
        _ = ((star U : SpinMatrix) * V) * Q * ((star V : SpinMatrix) * V) := by simp only [mul_assoc]
        _ = _ := by rw [Unitary.coe_star_mul_self, mul_one]
  rw [hh, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_sub]
  change _ = _ * ((star U : SpinMatrix) * V) i j
  ring

/-- The squared Hilbert–Schmidt distance is a weighted sum of scalar
differences, with the overlaps of the two eigenbases as weights. -/
theorem spectral_square {A B : SpinMatrix} (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    hilbertSchmidt (hA.cfc f - hB.cfc f)^2 = ∑ i, ∑ j, (f (hA.eigenvalues i) - f (hB.eigenvalues j))^2 *
      ‖((star hA.eigenvectorUnitary : SpinMatrix) * hB.eigenvectorUnitary) i j‖^2 := by
  rw [← hs_unitary _ hA.eigenvectorUnitary hB.eigenvectorUnitary, hilbertSchmidt, Real.sq_sqrt (by positivity)]
  simp only [mixed_cfc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Only cross-pairs from the two spectra enter the Hilbert–Schmidt comparison. -/
theorem spectral_lipschitz_of_eigenvalues {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (f g : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (lip : ∀ i j, |f (hA.1.eigenvalues i) - f (hB.1.eigenvalues j)| ≤
      L * |g (hA.1.eigenvalues i) - g (hB.1.eigenvalues j)|) :
    hilbertSchmidt (hA.isHermitian.cfc f - hB.isHermitian.cfc f) ≤
      L * hilbertSchmidt (hA.isHermitian.cfc g - hB.isHermitian.cfc g) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let V := hB.isHermitian.eigenvectorUnitary
  let mixed := fun (h : ℝ → ℝ) => (star U : SpinMatrix) *
    (hA.isHermitian.cfc h - hB.isHermitian.cfc h) * V
  have entry (i j : Fin 2) : ‖mixed f i j‖ ≤ L * ‖mixed g i j‖ := by
    simp only [mixed, U, V, mixed_cfc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (lip i j) (norm_nonneg _)
  rw [← hs_unitary _ U V, ← hs_unitary (hA.isHermitian.cfc g - _) U V]
  change hilbertSchmidt (mixed f) ≤ L * hilbertSchmidt (mixed g)
  rw [hilbertSchmidt, hilbertSchmidt, ← Real.sqrt_sq hL, ← Real.sqrt_mul (sq_nonneg L)]
  apply Real.sqrt_le_sqrt
  simp_rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    (sq_le_sq' (by linarith [norm_nonneg (mixed f i j), mul_nonneg hL (norm_nonneg (mixed g i j))])
      (entry i j)).trans_eq (mul_pow ..)

/-- A scalar Lipschitz comparison on the positive half-line transfers with the
same constant to the Hilbert–Schmidt distance of the two functional calculi. -/
theorem spectral_lipschitz {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (f g : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (lip : ∀ s t, 0 ≤ s → 0 ≤ t → |f s - f t| ≤ L * |g s - g t|) :
    hilbertSchmidt (hA.isHermitian.cfc f - hB.isHermitian.cfc f) ≤
      L * hilbertSchmidt (hA.isHermitian.cfc g - hB.isHermitian.cfc g) :=
  spectral_lipschitz_of_eigenvalues hA hB f g hL fun i j =>
    lip _ _ (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j)

end TSGA.Localization
