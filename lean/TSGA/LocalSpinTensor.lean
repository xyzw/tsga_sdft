import TSGA.SpinFockWave
import Mathlib.Analysis.Matrix.Order

/-! # Tensor products of local spin multipliers in a fermionic sector -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped ComplexConjugate MatrixOrder ComplexOrder

def sectorLocalUnitary {n : ℕ} (U : Position → unitary SpinMatrix) (x : Space n) :=
  sectorSpinTensor n (fun k => (U (x k) : SpinMatrix))

def sectorLocalPartial {n : ℕ} (U : Position → unitary SpinMatrix) (H : MatrixGradient)
    (x : Space n) (i : Fin n) (j : Fin 3) :=
  sectorSpinTensor n (Function.update (fun k => (U (x k) : SpinMatrix)) i (H (x i) j))

theorem sectorLocalUnitary_isometry {n : ℕ} (U : Position → unitary SpinMatrix) (x : Space n) :
    (sectorLocalUnitary U x).conjTranspose * sectorLocalUnitary U x = 1 := by
  unfold sectorLocalUnitary
  rw [sectorSpinTensor_adjoint, ← sectorSpinTensor_mul]
  simpa only [← Matrix.star_eq_conjTranspose,Unitary.coe_star_mul_self] using sectorSpinTensor_one (a := Fin 2) n

private theorem dot_norm {a : Type*} [Fintype a] (v : a → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖^2 : ℝ) : ℂ) := by simp [dotProduct,Complex.conj_mul']

theorem sectorLocalUnitary_norm {n : ℕ} (U : Position → unitary SpinMatrix) (x : Space n) (v : Spins n → ℂ) :
    (∑ t, ‖(sectorLocalUnitary U x *ᵥ v) t‖^2) = ∑ t, ‖v t‖^2 := by
  apply Complex.ofReal_injective
  rw [← dot_norm, ← dot_norm,Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,
    sectorLocalUnitary_isometry,Matrix.vecMul_one]

/-- Apply a single spin matrix in one specified slot. -/
private def slot {n : ℕ} (i : Fin n) (A : SpinMatrix) :=
  sectorSpinTensor n (Function.update (fun _ => (1 : SpinMatrix)) i A)

private theorem slot_factor {n : ℕ} (i : Fin n) (A : SpinMatrix) (s t : Spins n) :
    slot i A s t = (∏ k ∈ Finset.univ.erase i, (1 : SpinMatrix) (s k) (t k)) * A (s i) (t i) := by
  classical
  unfold slot sectorSpinTensor
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

private theorem slot_adjoint_mul {n : ℕ} (i : Fin n) (A : SpinMatrix) :
    (slot i A).conjTranspose * slot i A = slot i (star A * A) := by
  unfold slot
  rw [sectorSpinTensor_adjoint,← sectorSpinTensor_mul]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k
    simp [Matrix.star_eq_conjTranspose]
  · simp [Function.update_of_ne hk]

private theorem slot_gram {n : ℕ} (U : Position → unitary SpinMatrix) (H : MatrixGradient)
    (x : Space n) (i : Fin n) (j : Fin 3) :
    (sectorLocalPartial U H x i j).conjTranspose * sectorLocalPartial U H x i j =
      slot i (star (H (x i) j) * H (x i) j) := by
  unfold sectorLocalPartial slot
  rw [sectorSpinTensor_adjoint,← sectorSpinTensor_mul]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k
    simp [Matrix.star_eq_conjTranspose]
  · simp [Function.update_of_ne hk,← Matrix.star_eq_conjTranspose]

private theorem slot_scalar {n : ℕ} (i : Fin n) (b : ℂ) :
    slot i (b • (1 : SpinMatrix)) = b • 1 := by
  have h1 : slot i 1 = 1 := by simpa [slot] using sectorSpinTensor_one (a := Fin 2) n
  rw [← h1]
  ext s t
  simp only [Matrix.smul_apply, smul_eq_mul,slot_factor]
  ring

theorem sectorLocalPartial_le {n : ℕ} (U : Position → unitary SpinMatrix) (H : MatrixGradient)
    (x : Space n) (i : Fin n) (v : Spins n → ℂ) {b : ℝ}
    (h : (∑ j, star (H (x i) j)*H (x i) j) ≤ (b : ℂ) • (1 : SpinMatrix)) :
    (∑ j, ∑ t, ‖(sectorLocalPartial U H x i j *ᵥ v) t‖^2) ≤ b * ∑ t, ‖v t‖^2 := by
  let A := (b : ℂ) • (1 : SpinMatrix) - ∑ j, star (H (x i) j)*H (x i) j
  have ha : 0 ≤ A := sub_nonneg.mpr h
  have hs : (CFC.sqrt A).conjTranspose * CFC.sqrt A = A := by
    rw [show (CFC.sqrt A).conjTranspose = CFC.sqrt A from (CFC.sqrt_nonneg _).isSelfAdjoint,
      CFC.sqrt_mul_sqrt_self A ha]
  have pos : (slot i A).PosSemidef := by
    rw [← hs,← Matrix.star_eq_conjTranspose,← slot_adjoint_mul]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hlin : slot i A = (b : ℂ) • 1 - ∑ j, (sectorLocalPartial U H x i j).conjTranspose * sectorLocalPartial U H x i j := by
    simp_rw [slot_gram]
    rw [← slot_scalar i]
    ext s t
    simp [A,slot_factor,Matrix.sum_apply,Finset.mul_sum,mul_sub]
  have form := pos.re_dotProduct_nonneg v
  rw [hlin, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,
    Matrix.sum_mulVec, dotProduct_sum] at form
  have pull (j : Fin 3) := spin_form_pullback (sectorLocalPartial U H x i j) 1 v
  simp only [Matrix.one_mulVec,Matrix.mul_one, dot_norm] at pull
  simp_rw [← pull] at form
  simp only [dot_norm,smul_eq_mul, RCLike.re_to_complex, Complex.sub_re, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re, sub_nonneg] at form
  exact form


/-- Coefficients with the first spin as row and all spectator spins as column. -/
private def front {n : ℕ} (v : Spins (n+1) → ℂ) : Matrix (Fin 2) (Spins n) ℂ :=
  fun a s => v (Fin.cons a s)

private theorem front_rotate {n : ℕ} (U : Position → unitary SpinMatrix) (x : Position) (y : Space n)
    (v : Spins (n+1) → ℂ) :
    front (sectorLocalUnitary U (Fin.cons x y) *ᵥ v) = (U x : SpinMatrix)*front v*(sectorLocalUnitary U y).transpose := by
  ext a s
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)
  change ∑ t, sectorLocalUnitary U (Fin.cons x y) (Fin.cons a s) t * v t = _
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro b _
  change (∏ k, (U ((Fin.cons x y : Space (n+1)) k) : SpinMatrix)
    ((Fin.cons a s : Spins (n+1)) k) ((Fin.cons b t : Spins (n+1)) k)) * v (Fin.cons b t) = _
  simp [Fin.prod_univ_succ,sectorLocalUnitary,sectorSpinTensor,front,mul_right_comm]

private def spinSlice {n : ℕ} (ψ : Wave (n+1)) (x : Position) (y : Space n) :=
  front (fun s => ψ.value s (Fin.cons x y))

private theorem slice_cross_integrable {n : ℕ} (ψ : Wave (n+1)) :
    ∀ᵐ x : Position, ∀ i j s, Integrable (fun y : Space n =>
      spinSlice ψ x y i s * conj (spinSlice ψ x y j s)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Position) 0
  have he : (fun p : Position × Space n => Fin.cons p.1 p.2) = e.symm := by
    funext p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hp : MeasurePreserving (fun p : Position × Space n => Fin.cons p.1 p.2)
      (volume.prod volume) (volume : Measure (Space (n+1))) := he ▸ (volume_preserving_piFinSuccAbove (fun _ => Position) 0).symm
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro s
  have f := (ψ.square_integrable (Fin.cons i s)).comp_measurePreserving hp
  have g := (ψ.square_integrable (Fin.cons j s)).comp_measurePreserving hp
  exact (f.integrable_mul (q := 2) (g.of_le (Complex.continuous_conj.comp_aestronglyMeasurable g.1)
    (ae_of_all _ fun z => (Complex.norm_conj _).le))).prod_right_ae

private theorem slice_density {n : ℕ} (ψ : Wave (n+1)) {x : Position}
    (hx : ∀ i j s, Integrable (fun y : Space n => spinSlice ψ x y i s * conj (spinSlice ψ x y j s)))
    (i j : Fin 2) :
    ψ.matrixDensity x i j = (n+1 : ℕ) * ∫ y, (spinSlice ψ x y * (spinSlice ψ x y).conjTranspose) i j := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,integral_finsetSum _ (fun s _ => hx i j s)]
  rfl

/-- At fixed particle positions the spectator rotations cancel in the one-spin
marginal. Fubini then gives conjugation of the actual spatial density. -/
theorem Wave.localUnitary_matrixDensity {n : ℕ} (ψ χ : Wave (n+1)) (U : Position → unitary SpinMatrix)
    (hv : ∀ s x, χ.value s x = (sectorLocalUnitary U x *ᵥ (fun a => ψ.value a x)) s) :
    χ.matrixDensity =ᵐ[volume] fun x => (U x : SpinMatrix)*ψ.matrixDensity x*star (U x : SpinMatrix) := by
  filter_upwards [slice_cross_integrable ψ, slice_cross_integrable χ] with x hψ hχ
  let R := spinSlice ψ x
  let V := (U x : SpinMatrix)
  have hR (y : Space n) : spinSlice χ x y = V * R y * (sectorLocalUnitary U y).transpose := by
    unfold spinSlice
    simp_rw [hv]
    exact front_rotate U x y _
  have hG (y : Space n) : spinSlice χ x y * (spinSlice χ x y).conjTranspose =
      V * (R y*(R y).conjTranspose) * star V := by
    let T := sectorLocalUnitary U y
    have cancel : T.transpose * T.transpose.conjTranspose = 1 := by
      rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,← Matrix.transpose_mul,sectorLocalUnitary_isometry, Matrix.transpose_one]
    rw [hR]
    change (V*R y*T.transpose)*(V*R y*T.transpose).conjTranspose = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose]
    simp only [Matrix.star_eq_conjTranspose]
    rw [← Matrix.mul_assoc T.transpose, cancel, Matrix.one_mul]
  have integr (i j : Fin 2) : Integrable (fun y => (R y*(R y).conjTranspose) i j) :=
    integrable_finsetSum _ (fun s _ => hψ i j s)
  ext i j
  rw [slice_density χ hχ]
  simp_rw [hG]
  change _ = (V * ψ.matrixDensity x * star V) i j
  have sandwich (A : SpinMatrix) : (V*A*star V) i j =
      ∑ a, ∑ b, V i b * A b a * star V a j := by simp only [Matrix.mul_apply,Finset.sum_mul]
  simp_rw [sandwich]
  have hi (a b : Fin 2) := ((integr b a).const_mul (V i b)).mul_const ((star V) a j)
  simp only [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hi a b),
    integral_finsetSum _ (fun b _ => hi _ b), integral_mul_const, integral_const_mul,
    slice_density ψ hψ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end TSGA.ManyBody
