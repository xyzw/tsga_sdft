import TSGA.SpectralLipschitz
import Mathlib.Analysis.Matrix.Order

/-! # The aligning spin rotation in the constant-matrix comparison

The gapped case of the local replacement uses a unitary taking the reference
spin direction to the local one. Its denominator is nonzero whenever the two
directions are not antipodal.
-/

noncomputable section

namespace TSGA

open Matrix
open scoped Matrix ComplexOrder

/-- Pauli matrix n·σ. -/
def pauli (n : Fin 3 → ℝ) : SpinMatrix :=
  !![(n 2 : ℂ), (n 0 : ℂ) - Complex.I * (n 1 : ℂ);
     (n 0 : ℂ) + Complex.I * (n 1 : ℂ), -(n 2 : ℂ)]

def spinDot (n m : Fin 3 → ℝ) : ℝ := n 0*m 0 + n 1*m 1 + n 2*m 2

@[simp] theorem pauli_star (n : Fin 3 → ℝ) : star (pauli n) = pauli n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli]
  all_goals ring

theorem pauli_anticommute (n m : Fin 3 → ℝ) :
    pauli n * pauli m + pauli m * pauli n = ((2 * spinDot n m : ℝ) : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [pauli, spinDot]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem pauli_sq {n : Fin 3 → ℝ} (hn : spinDot n n = 1) : pauli n * pauli n = 1 := by
  have h := pauli_anticommute n n
  rw [hn] at h
  ext i j
  have hh := congrArg (fun A : SpinMatrix => A i j) h
  change (pauli n * pauli n) i j + (pauli n * pauli n) i j = _ at hh
  norm_num at hh
  linear_combination hh / 2

/-- The numerator of the normalized aligning rotation intertwines the two
Pauli matrices. -/
theorem pauli_intertwine {n m : Fin 3 → ℝ} (hn : spinDot n n = 1) (hm : spinDot m m = 1) :
    (1 + pauli n * pauli m) * pauli m = pauli n * (1 + pauli n * pauli m) := by
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.mul_assoc, pauli_sq hm, mul_one,
    ← Matrix.mul_assoc, pauli_sq hn, one_mul, add_comm]

private theorem align_sandwich {n m : Fin 3 → ℝ} (hn : spinDot n n = 1) (hm : spinDot m m = 1) :
    (1 + pauli n * pauli m) * star (1 + pauli n * pauli m) =
      ((2 * (1 + spinDot n m) : ℝ) : ℂ) • 1 := by
  simp only [star_add, star_one, star_mul, pauli_star]
  have hc : (pauli n * pauli m) * (pauli m * pauli n) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pauli m), pauli_sq hm, one_mul, pauli_sq hn]
  simp only [add_mul, mul_add, one_mul, mul_one, hc]
  have h := pauli_anticommute n m
  calc
    _ = 1 + 1 + (pauli n * pauli m + pauli m * pauli n) := by abel
    _ = _ := by rw [h]; push_cast; module

/-- Explicit rotation aligning two unit directions. -/
def alignSpin (n m : Fin 3 → ℝ) : SpinMatrix :=
  ((Real.sqrt (2 * (1 + spinDot n m)))⁻¹ : ℝ) • (1 + pauli n * pauli m)

theorem alignSpin_unitary {n m : Fin 3 → ℝ} (hn : spinDot n n = 1) (hm : spinDot m m = 1)
    (hd : -1 < spinDot n m) : alignSpin n m ∈ unitary SpinMatrix := by
  have ht : 0 < 2 * (1 + spinDot n m) := by linarith
  let a := Real.sqrt (2 * (1 + spinDot n m))
  have ha : 0 < a := Real.sqrt_pos.2 ht
  have ha₂ : a^2 = 2 * (1 + spinDot n m) := Real.sq_sqrt ht.le
  apply Matrix.mem_unitaryGroup_iff.mpr
  change (a⁻¹ • (1 + pauli n * pauli m)) * star (a⁻¹ • (1 + pauli n * pauli m)) = 1
  rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, align_sandwich hn hm]
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
  rw [← ha₂, Complex.ofReal_pow]
  field_simp [ha.ne']

theorem alignSpin_conjugates {n m : Fin 3 → ℝ} (hn : spinDot n n = 1) (hm : spinDot m m = 1)
    (hd : -1 < spinDot n m) : alignSpin n m * pauli m * star (alignSpin n m) = pauli n := by
  have hU := Matrix.mem_unitaryGroup_iff.mp (alignSpin_unitary hn hm hd)
  have hv : alignSpin n m * pauli m = pauli n * alignSpin n m := by
    unfold alignSpin
    rw [smul_mul_assoc, mul_smul_comm, pauli_intertwine hn hm]
  rw [hv, Matrix.mul_assoc, hU, mul_one]

/-- The rank-one spectral projector associated with the direction n. -/
def spinProjector (n : Fin 3 → ℝ) : SpinMatrix := (1/2 : ℝ) • (1 + pauli n)

theorem alignSpin_projector {n m : Fin 3 → ℝ} (hn : spinDot n n = 1) (hm : spinDot m m = 1)
    (hd : -1 < spinDot n m) :
    alignSpin n m * spinProjector m * star (alignSpin n m) = spinProjector n := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (alignSpin_unitary hn hm hd)
  simp only [spinProjector, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one,
    hu, alignSpin_conjugates hn hm hd]

private theorem pauli_trace_mul (n m : Fin 3 → ℝ) : (pauli n * pauli m).trace.re = 2 * spinDot n m := by
  simp [pauli, Matrix.trace_fin_two, spinDot]
  ring

/-- The aligning unitary is close to the identity when the two polarization
axes are close. Both sides are squared Euclidean or Hilbert–Schmidt norms. -/
theorem alignSpin_near_one {n m : Fin 3 → ℝ} (hn : spinDot n n = 1) (hm : spinDot m m = 1)
    (hd : -1 < spinDot n m) :
    Localization.hilbertSchmidt (alignSpin n m - 1)^2 ≤ spinDot (n - m) (n - m) := by
  let U := alignSpin n m
  let a := Real.sqrt (2 * (1 + spinDot n m))
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have ha₂ : a^2 = 2 * (1 + spinDot n m) := Real.sq_sqrt (by linarith)
  have hdiff : spinDot (n-m) (n-m) = 2 - 2*spinDot n m := by
    dsimp [spinDot] at hn hm ⊢
    linarith only [hn, hm]
  have hnn : 0 ≤ spinDot (n-m) (n-m) :=
    add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
  have ha' : a ≤ 2 := by nlinarith
  have hu : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp (alignSpin_unitary hn hm hd)
  have htr : U.trace.re = a := by
    change ((a⁻¹ : ℝ) • (1 + pauli n * pauli m)).trace.re = _
    rw [Matrix.trace_smul, Matrix.trace_add, Complex.real_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re,
      pauli_trace_mul, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]
    norm_num
    field_simp [ha.ne']
    linarith only [ha₂]
  have energy (B : SpinMatrix) : Localization.hilbertSchmidt B ^ 2 = (B * star B).trace.re := by
    rw [Localization.hilbertSchmidt, Real.sq_sqrt (by positivity)]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Complex.sq_norm, Complex.mul_conj]
  change Localization.hilbertSchmidt (U - 1)^2 ≤ _
  rw [energy, star_sub, star_one, sub_mul, mul_sub, hu, mul_one, one_mul, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub]
  simp only [Complex.sub_re, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
    Complex.star_def, Complex.conj_re, htr, Matrix.trace_one, Fintype.card_fin,
    Nat.cast_ofNat, hdiff]
  norm_num
  nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha')]

end TSGA
