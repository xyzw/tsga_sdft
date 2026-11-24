import TSGA.SpinComparison
import TSGA.ComparisonMatrices

/-! # The spin direction and spectral gap of a Hermitian spin matrix

The ordering of Mathlib's two eigenvalues depends on a fixed equivalence
of finite types. Their absolute difference is the majority-minus-minority
gap for every indexing.
-/

noncomputable section
namespace TSGA
open Matrix
open scoped ComplexOrder

/-- Twice the coefficients of the three Pauli matrices in a Hermitian spin matrix. -/
def blochVector (S : SpinMatrix) : Fin 3 → ℝ :=
  ![2*(S 1 0).re, 2*(S 1 0).im, (S 0 0).re-(S 1 1).re]

def blochGap (S : SpinMatrix) : ℝ := Real.sqrt (spinDot (blochVector S) (blochVector S))

def blochAxis (S : SpinMatrix) : Fin 3 → ℝ := (blochGap S)⁻¹ • blochVector S

private theorem diag_im {S : SpinMatrix} (hS : S.IsHermitian) (i : Fin 2) : (S i i).im = 0 := by
  have h := congrArg Complex.im (hS.apply i i)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

private theorem upper_re {S : SpinMatrix} (hS : S.IsHermitian) : (S 0 1).re = (S 1 0).re := by
  simpa only [Complex.star_def, Complex.conj_re] using congrArg Complex.re (hS.apply 0 1).symm

private theorem upper_im {S : SpinMatrix} (hS : S.IsHermitian) : (S 0 1).im = -(S 1 0).im := by
  simpa only [Complex.star_def, Complex.conj_im] using congrArg Complex.im (hS.apply 0 1).symm

theorem pauli_blochVector {S : SpinMatrix} (hS : S.IsHermitian) :
    pauli (blochVector S) = (2:ℝ) • S - S.trace.re • (1 : SpinMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [pauli, blochVector, Matrix.smul_apply, Matrix.trace_fin_two, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, diag_im hS, upper_re hS, upper_im hS] <;> ring

private theorem dot_self_nonneg (v : Fin 3 → ℝ) : 0 ≤ spinDot v v :=
  add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

theorem blochGap_sq (S : SpinMatrix) : (blochGap S)^2 = spinDot (blochVector S) (blochVector S) :=
  Real.sq_sqrt (dot_self_nonneg _)

theorem blochGap_eq_eigenvalue_gap {S : SpinMatrix} (hS : S.IsHermitian) :
    blochGap S = |hS.eigenvalues 0-hS.eigenvalues 1| := by
  have htr := congrArg Complex.re hS.trace_eq_sum_eigenvalues
  simp only [Matrix.trace_fin_two, Fin.sum_univ_two, Complex.add_re] at htr
  change (S 0 0).re + (S 1 1).re = hS.eigenvalues 0 + hS.eigenvalues 1 at htr
  have hdet := congrArg Complex.re hS.det_eq_prod_eigenvalues
  simp [Matrix.det_fin_two, Fin.prod_univ_two, Complex.mul_re, diag_im hS, upper_re hS, upper_im hS] at hdet
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs]
  change (blochGap S)^2 = _
  rw [blochGap_sq]
  simp [blochVector, spinDot]
  have hsquare : ((S 0 0).re + (S 1 1).re)^2 = (hS.eigenvalues 0 + hS.eigenvalues 1)^2 :=
    congrArg (fun x : ℝ => x^2) htr
  nlinarith only [hsquare, hdet]

theorem blochAxis_unit {S : SpinMatrix} (hg : 0 < blochGap S) :
    spinDot (blochAxis S) (blochAxis S) = 1 := by
  have h : spinDot (blochAxis S) (blochAxis S) = (blochGap S)⁻¹^2 * spinDot (blochVector S) (blochVector S) := by
    simp only [spinDot, blochAxis, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, ← blochGap_sq, ← mul_pow, inv_mul_cancel₀ hg.ne', one_pow]

theorem pauli_real_smul (a : ℝ) (v : Fin 3 → ℝ) : pauli (a • v) = a • pauli v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.smul_apply, Complex.real_smul] <;> ring

theorem blochGap_smul_pauli {S : SpinMatrix} (hS : S.IsHermitian) (hg : 0 < blochGap S) :
    blochGap S • pauli (blochAxis S) = (2:ℝ) • S - S.trace.re • (1 : SpinMatrix) := by
  rw [blochAxis, pauli_real_smul, smul_smul, mul_inv_cancel₀ hg.ne', one_smul, pauli_blochVector hS]

/-- The square-root gap on the polarized branch is at least √r/4 even if
the minority occupancy is zero. -/
theorem sqrt_gap_of_half_trace {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r)
    (ha' : a ≤ r) (hb' : b ≤ r) (hg : r/2 ≤ |a-b|) :
    Real.sqrt r/4 ≤ |Real.sqrt a-Real.sqrt b| := by
  have hf : |a-b| = |Real.sqrt a-Real.sqrt b| * (Real.sqrt a+Real.sqrt b) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
    congr 1
    nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hsum : Real.sqrt a+Real.sqrt b ≤ 2*Real.sqrt r := by
    linarith only [Real.sqrt_le_sqrt ha', Real.sqrt_le_sqrt hb']
  rw [hf] at hg
  have h := hg.trans (mul_le_mul_of_nonneg_left hsum (abs_nonneg _))
  apply (mul_le_mul_iff_left₀ (Real.sqrt_pos.2 hr)).mp
  nlinarith only [h, Real.sq_sqrt hr.le]

/-- The trace-free part of the Hilbert–Schmidt norm gives the squared gap. -/
theorem blochGap_sq_eq_trace_free {S : SpinMatrix} (hS : S.IsHermitian) :
    (blochGap S)^2 = 2*(Localization.hilbertSchmidt S)^2-S.trace.re^2 := by
  have spec : Localization.inSpinFrame hS.eigenvectorUnitary hS.eigenvalues = S := hS.spectral_theorem.symm
  have hnorm := Localization.inSpinFrame_hs hS.eigenvectorUnitary hS.eigenvalues
  have ht := Localization.inSpinFrame_trace hS.eigenvectorUnitary hS.eigenvalues
  rw [spec] at hnorm ht
  rw [blochGap_eq_eigenvalue_gap hS, sq_abs, hnorm, ht]
  ring

theorem blochGap_frame (U : unitary SpinMatrix) (v : Fin 2 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    blochGap (Localization.inSpinFrame U v) = |v 0-v 1| := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (abs_nonneg _)).mp
  change (blochGap (Localization.inSpinFrame U v))^2 = _
  rw [blochGap_sq_eq_trace_free (Localization.inSpinFrame_pos U hv).1, sq_abs,
    Localization.inSpinFrame_hs, Localization.inSpinFrame_trace]
  ring

/-- The actual square-root matrix satisfies the quantitative spectral gap used
in the Sobolev estimate for the local aligning rotation. -/
theorem blochGap_sqrt_lower {S : SpinMatrix} (hS : S.PosSemidef) {r : ℝ} (hr : 0 < r)
    (hcap : ∀ i, hS.1.eigenvalues i ≤ r) (hg : r/2 ≤ blochGap S) :
    Real.sqrt r/4 ≤ blochGap (hS.1.cfc Real.sqrt) := by
  change Real.sqrt r/4 ≤ blochGap (Localization.inSpinFrame hS.1.eigenvectorUnitary
    (fun i => Real.sqrt (hS.1.eigenvalues i)))
  rw [blochGap_frame _ _ fun _ => Real.sqrt_nonneg _]
  rw [blochGap_eq_eigenvalue_gap hS.1] at hg
  exact sqrt_gap_of_half_trace (hS.eigenvalues_nonneg 0) (hS.eigenvalues_nonneg 1)
    hr (hcap 0) (hcap 1) hg

theorem sqrt_matrix_blochGap {M : SpinMatrix} (hM : M.PosSemidef) {r : ℝ} (hr : 0 < r)
    (htrace : M.trace.re ≤ r) (hg : r/2 ≤ blochGap M) :
    Real.sqrt r/4 ≤ blochGap (hM.1.cfc (fun t : ℝ => t^(1/2:ℝ))) := by
  have hcap (i : Fin 2) : hM.1.eigenvalues i ≤ r := by
    have h := congrArg Complex.re hM.1.trace_eq_sum_eigenvalues
    simp only [Fin.sum_univ_two, Complex.add_re] at h
    change M.trace.re = hM.1.eigenvalues 0 + hM.1.eigenvalues 1 at h
    fin_cases i
    · change hM.1.eigenvalues 0 ≤ r
      linarith only [h, htrace, hM.eigenvalues_nonneg 1]
    · change hM.1.eigenvalues 1 ≤ r
      linarith only [h, htrace, hM.eigenvalues_nonneg 0]
  have he : (fun t : ℝ => t^(1/2:ℝ)) = Real.sqrt := funext fun t => (Real.sqrt_eq_rpow t).symm
  rw [he]
  exact blochGap_sqrt_lower hM hr hcap hg

/-- Squaring a Hermitian matrix multiplies its Bloch vector by the trace. -/
theorem blochVector_square {S : SpinMatrix} (hS : S.IsHermitian) :
    blochVector (S*S) = S.trace.re • blochVector S := by
  funext i
  fin_cases i <;> simp [blochVector, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Complex.mul_re, Complex.mul_im, diag_im hS, upper_re hS, upper_im hS] <;> ring

private theorem spinDot_smul (c d : ℝ) (v w : Fin 3 → ℝ) : spinDot (c • v) (d • w) = c*d*spinDot v w := by
  simp only [spinDot, Pi.smul_apply, smul_eq_mul]; ring

theorem blochAxis_square {S : SpinMatrix} (hS : S.IsHermitian) (ht : 0 < S.trace.re) :
    blochAxis (S*S) = blochAxis S := by
  have hg : blochGap (S*S) = S.trace.re * blochGap S := by
    change Real.sqrt _ = _
    rw [blochVector_square hS, spinDot_smul, Real.sqrt_mul (mul_nonneg ht.le ht.le),
      Real.sqrt_mul_self ht.le]
    rfl
  unfold blochAxis
  rw [hg, blochVector_square hS, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

private theorem blochVector_sub (S T : SpinMatrix) : blochVector (S-T) = blochVector S - blochVector T := by
  funext i
  fin_cases i <;> simp [blochVector] <;> ring

/-- A raw oscillation below half the spectral gap keeps the reference axis
in the same hemisphere. The estimate is in the Hilbert–Schmidt norm. -/
theorem blochAxis_dot_nonneg_of_close {S T : SpinMatrix} (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hd : Localization.hilbertSchmidt (S-T) ≤ blochGap S/2) : 0 ≤ spinDot (blochAxis S) (blochAxis T) := by
  let v := blochVector S
  let w := blochVector T
  have hv : spinDot v v = (blochGap S)^2 := (blochGap_sq S).symm
  have hw : 0 ≤ spinDot w w := dot_self_nonneg _
  have hdiff : spinDot (v-w) (v-w) ≤ 2*(Localization.hilbertSchmidt (S-T))^2 := by
    change spinDot (blochVector S-blochVector T) _ ≤ _
    rw [← blochVector_sub, ← blochGap_sq, blochGap_sq_eq_trace_free (hS.sub hT)]
    linarith only [sq_nonneg (S-T).trace.re]
  have split : spinDot (v-w) (v-w) = spinDot v v + spinDot w w - 2*spinDot v w := by
    simp only [spinDot, Pi.sub_apply]; ring
  rw [split, hv] at hdiff
  have hdist := (sq_le_sq₀ (show 0 ≤ Localization.hilbertSchmidt (S-T) from Real.sqrt_nonneg _)
    (show 0 ≤ blochGap S/2 from div_nonneg (Real.sqrt_nonneg _) (by norm_num))).2 hd
  have hdots : 0 ≤ spinDot v w := by nlinarith only [hdiff, hdist, hw, sq_nonneg (blochGap S)]
  rw [blochAxis, blochAxis, spinDot_smul]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hdots

/-- A positive spin density and its matrix square root have the same normalized axis. -/
theorem blochAxis_matrix_sqrt {M : SpinMatrix} (hM : M.PosSemidef) :
    blochAxis (hM.1.cfc (fun t : ℝ => t^(1/2:ℝ))) = blochAxis M := by
  let v := fun i => Real.sqrt (hM.1.eigenvalues i)
  let U := hM.1.eigenvectorUnitary
  let S := Localization.inSpinFrame U v
  have hs : S.PosSemidef := Localization.inSpinFrame_pos U fun _ => Real.sqrt_nonneg _
  have sq : S*S = M := by
    have hh : S*S = Localization.inSpinFrame U (fun i => (v i)^2) := by
      simp only [S, Localization.inSpinFrame, ← map_mul, Matrix.diagonal_mul_diagonal, pow_two, Complex.ofReal_mul]
    have he : (fun i => (v i)^2) = hM.1.eigenvalues := funext fun i => Real.sq_sqrt (hM.eigenvalues_nonneg i)
    rw [hh, he]
    exact hM.1.spectral_theorem.symm
  simp only [← Real.sqrt_eq_rpow]
  change blochAxis S = blochAxis M
  by_cases ht : 0 < S.trace.re
  · calc
      _ = blochAxis (S*S) := (blochAxis_square hs.1 ht).symm
      _ = _ := congrArg blochAxis sq
  · have htr := RCLike.nonneg_iff.mp hs.trace_nonneg
    have hz : S = 0 := hs.trace_eq_zero_iff.mp (Complex.ext (le_antisymm (le_of_not_gt ht) htr.1) htr.2)
    rw [← sq, hz, zero_mul]

end TSGA
