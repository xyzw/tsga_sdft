import TSGA.BlochAxis

/-! # The aligning rotation for the frozen spin eigenframe -/

noncomputable section
namespace TSGA.Localization
open Matrix
open scoped ComplexOrder

private theorem frame_smul (U : unitary SpinMatrix) (s : ℝ) (v : Fin 2 → ℝ) :
    inSpinFrame U (s • v) = s • inSpinFrame U v := by
  have hd : diagonal (fun i => (((s • v) i : ℝ) : ℂ)) = s • diagonal (fun i => (v i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.smul_apply, Complex.real_smul]
    · simp [Matrix.smul_apply, diagonal_apply_ne, hij]
  change (U : SpinMatrix) * diagonal _ * (star U : SpinMatrix) = _
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- The sign of the difference of the indexed eigenvalues is kept here.
It is the same for all spin matrices under Mathlib's spectral indexing. -/
private theorem frame_traceless (U : unitary SpinMatrix) (v : Fin 2 → ℝ) :
    (2:ℝ) • inSpinFrame U v - (inSpinFrame U v).trace.re • (1 : SpinMatrix) =
      (v 0-v 1) • inSpinFrame U ![1,-1] := by
  rw [inSpinFrame_trace, ← inSpinFrame_const U, ← frame_smul U, inSpinFrame_sub, ← frame_smul U]
  apply congrArg (inSpinFrame U)
  funext i
  fin_cases i <;> simp <;> ring

/-- Conjugating the matrix with X's eigenvalues in C's spin basis by the
canonical aligning rotation recovers X, including at full polarization. -/
theorem alignSpin_frozen_matrix {C X : SpinMatrix} (hC : C.PosSemidef) (hX : X.PosSemidef)
    (hc : 0 < blochGap C) (hx : 0 < blochGap X)
    (hh : -1 < spinDot (blochAxis X) (blochAxis C)) :
    let V := alignSpin (blochAxis X) (blochAxis C)
    V * inSpinFrame hC.1.eigenvectorUnitary hX.1.eigenvalues * star V = X := by
  intro V
  let U := hC.1.eigenvectorUnitary
  let x := hX.1.eigenvalues
  let c := hC.1.eigenvalues
  let R := inSpinFrame U x
  let Z := inSpinFrame U ![1,-1]
  have sc : inSpinFrame U c = C := hC.1.spectral_theorem.symm
  have hbase : blochGap C • pauli (blochAxis C) = (c 0-c 1) • Z := by
    have h := frame_traceless U c
    rw [sc] at h
    exact (blochGap_smul_pauli hC.1 hc).trans h
  have hcoef : blochGap C*(x 0-x 1) = blochGap X*(c 0-c 1) := by
    rw [blochGap_eq_eigenvalue_gap hC.1, blochGap_eq_eigenvalue_gap hX.1]
    change |c 0-c 1| * (x 0-x 1) = |x 0-x 1| * (c 0-c 1)
    rcases spin_indices_same_order hC.1 hX.1 with ⟨h,k⟩ | ⟨h,k⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr k), mul_comm]
    · rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (sub_nonpos.mpr k)]
      ring
  have hcenter : (2:ℝ) • R-R.trace.re • (1 : SpinMatrix) = blochGap X • pauli (blochAxis C) := by
    change (2:ℝ) • inSpinFrame U x-_ = _
    rw [frame_traceless U x]
    apply (smul_right_injective SpinMatrix hc.ne')
    calc
      _ = (blochGap C*(x 0-x 1)) • Z := smul_smul .. 
      _ = (blochGap X*(c 0-c 1)) • Z := by rw [hcoef]
      _ = blochGap X • (blochGap C • pauli (blochAxis C)) := by rw [hbase, smul_smul]
      _ = _ := smul_comm ..
  have hxspec : inSpinFrame hX.1.eigenvectorUnitary x = X := hX.1.spectral_theorem.symm
  have ht : R.trace.re = X.trace.re := calc
    _ = x 0+x 1 := inSpinFrame_trace U x
    _ = _ := (inSpinFrame_trace hX.1.eigenvectorUnitary x).symm.trans (congrArg (fun A : SpinMatrix => A.trace.re) hxspec)
  have hunit : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp
    (alignSpin_unitary (blochAxis_unit hx) (blochAxis_unit hc) hh)
  have hpa : V * pauli (blochAxis C) * star V = pauli (blochAxis X) :=
    alignSpin_conjugates (blochAxis_unit hx) (blochAxis_unit hc) hh
  have he := congrArg (fun M : SpinMatrix => V*M*star V) hcenter
  change V*((2:ℝ) • R - R.trace.re • 1)*star V = V*(blochGap X • pauli (blochAxis C))*star V at he
  rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, mul_one,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, hunit, ht, hpa, blochGap_smul_pauli hX.1 hx] at he
  exact (smul_right_injective SpinMatrix (by norm_num : (2:ℝ) ≠ 0)) (sub_left_inj.mp he)

theorem alignSpin_referenceFrame (D : Density) (c x : Position)
    (hc : 0 < blochGap (D.matrix c)) (hx : 0 < blochGap (D.matrix x))
    (hh : -1 < spinDot (blochAxis (D.matrix x)) (blochAxis (D.matrix c))) :
    let V := alignSpin (blochAxis (D.matrix x)) (blochAxis (D.matrix c))
    V * SpectralExtrema.referenceFrame D c x * star V = D.matrix x :=
  alignSpin_frozen_matrix (D.positive c) (D.positive x) hc hx hh

end TSGA.Localization
