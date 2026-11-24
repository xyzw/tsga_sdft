import TSGA.ErrorDensity
import TSGA.SpectralLipschitz
import Mathlib.MeasureTheory.Function.L2Space

/-! # Kinetic energy under an axial spin rotation -/

noncomputable section

namespace TSGA.Localization

open MeasureTheory Matrix Unitary
open scoped ComplexOrder

def rotatedDensity (D : Density) (φ : Phase) : Density :=
  ⟨fun x => rotate (φ.value x) (D.matrix x), fun x => rotate_posSemidef _ (D.positive x)⟩

@[simp] theorem rotated_charge (D : Density) (φ : Phase) (x : Position) :
    (rotatedDensity D φ).charge x = D.charge x := by simp [Density.charge, rotatedDensity]

theorem rotated_power (D : Density) (φ : Phase) {a : ℝ} (ha : 0 ≤ a) (x : Position) :
    (rotatedDensity D φ).power a x = rotate (φ.value x) (D.power a x) := by
  let U : unitary SpinMatrix := ⟨spinRotation (φ.value x),
    (Matrix.mem_specialUnitaryGroup_iff.mp (spinRotation_mem_specialUnitaryGroup _)).1⟩
  let e := Unitary.conjStarAlgAut ℂ SpinMatrix U
  have he : Continuous e := by
    change Continuous (fun m : SpinMatrix => (U : SpinMatrix) * m * star (U : SpinMatrix))
    fun_prop
  have H := StarAlgHomClass.map_cfc (S := ℂ) e (fun t : ℝ => t^a) (D.matrix x)
    (Real.continuous_rpow_const ha).continuousOn he (D.positive x).isHermitian.isSelfAdjoint
    ((rotatedDensity D φ).positive x).isHermitian.isSelfAdjoint
  unfold Density.power
  rw [← Matrix.IsHermitian.cfc_eq, ← Matrix.IsHermitian.cfc_eq]
  exact H.symm

/-- The squared Hilbert–Schmidt norm of the positive square root is the charge. -/
theorem sqrt_hilbertSchmidt_sq (D : Density) (x : Position) :
    (∑ j, ∑ k, ‖D.power (1/2) x j k‖ ^ 2) = D.charge x := by
  let h := (D.positive x).isHermitian
  let e := Unitary.conjStarAlgAut ℂ SpinMatrix h.eigenvectorUnitary
  let d : Fin 2 → ℂ := fun i => (Real.sqrt (h.eigenvalues i) : ℂ)
  have hroot : D.power (1/2) x = e (diagonal d) := by
    simp only [Density.power, Matrix.IsHermitian.cfc, Real.sqrt_eq_rpow, d, e]
    rfl
  have hstar : star (diagonal d) = diagonal d := by
    simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Pi.star_def, d]
  have hs : D.power (1/2) x * star (D.power (1/2) x) = D.matrix x := by
    rw [hroot, ← map_star, hstar, ← map_mul, Matrix.diagonal_mul_diagonal]
    conv_rhs => rw [h.spectral_theorem]
    apply congrArg e
    apply congrArg Matrix.diagonal
    funext i
    simp [d, ← Complex.ofReal_mul, Real.mul_self_sqrt (D.positive x |>.eigenvalues_nonneg i)]
  have ht := congrArg (fun M : SpinMatrix => M.trace.re) hs
  simpa [Density.charge, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.sq_norm, Complex.mul_conj] using ht

/-- The two off-diagonal entries acquire opposite phases. -/
def axialWeight (j k : Fin 2) : ℝ :=
  (if j = 0 then -(1/2) else 1/2) - (if k = 0 then -(1/2) else 1/2)

private theorem axialWeight_le (j k : Fin 2) : |axialWeight j k| ≤ 1 := by
  fin_cases j <;> fin_cases k <;> norm_num [axialWeight]

theorem rotate_by_entry (s : ℝ) (M : SpinMatrix) (j k : Fin 2) :
    rotate s M j k = phaseFactor (axialWeight j k * s) * M j k := by
  let angle := fun i : Fin 2 => if i = 0 then -(s/2) else s/2
  have hr : spinRotation s = Matrix.diagonal (fun i => phaseFactor (angle i)) := rfl
  have ha : axialWeight j k * s = angle j + -(angle k) := by
    simp only [axialWeight, angle]
    split_ifs <;> ring
  simp only [rotate, hr, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply, star_phaseFactor, ha, phaseFactor_add]
  ring

/-- Scalar weak product/chain rule for multiplication by a phase with
continuous first derivative. The coefficient can have either sign. -/
def WeakPhaseProduct : Prop :=
  ∀ {p : ℝ} (φ : Phase), φ.Regular p → ∀ (b : ℝ) (i : Fin 3) (f g : Position → ℂ),
    WeakPartialOn Set.univ i f g →
    WeakPartialOn Set.univ i (fun x => phaseFactor (b * φ.value x) * f x)
      (fun x => phaseFactor (b * φ.value x) *
        (g x + Complex.I * (b : ℂ) * (φ.grad x i : ℂ) * f x))

def axialGradient (D : Density) (φ : Phase) (S : MatrixGradient) : MatrixGradient :=
  fun x i j k => phaseFactor (axialWeight j k * φ.value x) *
    (S x i j k + Complex.I * (axialWeight j k : ℂ) * (φ.grad x i : ℂ) * D.power (1/2) x j k)

private theorem axial_weak (chain : WeakPhaseProduct) {D : Density} {φ : Phase} {p : ℝ}
    {S : MatrixGradient} (hφ : φ.Regular p) (hS : IsMatrixGradientOn Set.univ (D.power (1/2)) S) :
    IsMatrixGradientOn Set.univ ((rotatedDensity D φ).power (1/2)) (axialGradient D φ S) := by
  intro i j k
  simpa only [rotated_power D φ (by norm_num : 0 ≤ (1/2 : ℝ)), rotate_by_entry, axialGradient]
    using chain φ hφ (axialWeight j k) i _ _ (hS i j k)

theorem axial_kinetic_pointwise (D : Density) (φ : Phase) (S : MatrixGradient) (x : Position) :
    kineticDensity (axialGradient D φ S) x ≤ 2 * kineticDensity S x + 2 * (D.charge x * ‖φ.grad x‖^2) := by
  have hs (W : MatrixGradient) : kineticDensity W x = ∑ i, ∑ j, ∑ k, ‖W x i j k‖^2 :=
    Real.sq_sqrt (by positivity)
  have hnorm (s : ℝ) : ‖phaseFactor s‖ = 1 := by simp [phaseFactor, Complex.norm_exp]
  have hentry (i : Fin 3) (j k : Fin 2) : ‖axialGradient D φ S x i j k‖ ^ 2 ≤
      2 * ‖S x i j k‖ ^ 2 + 2 * ‖φ.grad x i‖ ^ 2 * ‖D.power (1/2) x j k‖ ^ 2 := by
    let m := D.power (1/2) x j k
    have hcorr : ‖Complex.I * (axialWeight j k : ℂ) * (φ.grad x i : ℂ) * m‖ ≤ ‖φ.grad x i‖ * ‖m‖ := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) (axialWeight_le j k))
        (norm_nonneg _)
    have htri := (norm_add_le (S x i j k) _).trans (add_le_add (le_refl _) hcorr)
    simp only [axialGradient, norm_mul, hnorm, one_mul]
    change ‖S x i j k + Complex.I * (axialWeight j k : ℂ) * (φ.grad x i : ℂ) * m‖^2 ≤ _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    change _ ≤ 2 * ‖S x i j k‖ ^ 2 + 2 * ‖φ.grad x i‖ ^ 2 * ‖m‖ ^ 2
    nlinarith only [hsq, sq_nonneg (‖S x i j k‖ - ‖φ.grad x i‖ * ‖m‖)]
  rw [hs, hs, PiLp.norm_sq_eq_of_L2]
  apply (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    Finset.sum_le_sum fun k _ => hentry i j k).trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sqrt_hilbertSchmidt_sq, ← Finset.sum_mul]
  ring

/-- The rotated square root has an L² weak gradient. Its kinetic cost is at
most twice the original cost plus twice the phase kinetic energy. -/
theorem rotated_sqrt_kinetic_of_weak (chain : WeakPhaseProduct) {D : Density} {φ : Phase} {p : ℝ}
    {S : MatrixGradient} (hS : IsMatrixGradientOn Set.univ (D.power (1/2)) S)
    (hLp : MemLp (matrixGradNorm S) 2) (hφ : φ.Regular p)
    (hkin : Integrable fun x => D.charge x * ‖φ.grad x‖ ^ 2) :
    ∃ Z : MatrixGradient, IsMatrixGradientOn Set.univ ((rotatedDensity D φ).power (1/2)) Z ∧
      MemLp (matrixGradNorm Z) 2 ∧
      (∫ x, kineticDensity Z x) ≤ 2 * (∫ x, kineticDensity S x) + 2 * ∫ x, D.charge x * ‖φ.grad x‖^2 := by
  let Z := axialGradient D φ S
  have hw := axial_weak chain hφ hS
  have hm (i j k) : AEMeasurable (fun x => Z x i j k) volume :=
    (locallyIntegrableOn_univ.mp (hw i j k).2.1).aestronglyMeasurable.aemeasurable
  have hs : AEMeasurable (matrixGradNorm Z) volume := by
    apply Real.continuous_sqrt.measurable.comp_aemeasurable
    exact Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      Finset.aemeasurable_fun_sum _ fun k _ => (hm i j k).norm.pow_const 2
  have hS_int : Integrable (kineticDensity S) := hLp.integrable_sq
  have hmajor := (hS_int.const_mul 2).add (hkin.const_mul 2)
  have hbound := axial_kinetic_pointwise D φ S
  have hi : Integrable (kineticDensity Z) := hmajor.mono' (hs.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (show 0 ≤ kineticDensity Z x from sq_nonneg _)]
      exact hbound x)
  refine ⟨Z, hw, (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).2 hi, ?_⟩
  have hint := integral_mono hi hmajor hbound
  simpa only [Pi.add_apply, integral_add (hS_int.const_mul 2) (hkin.const_mul 2),
    integral_const_mul] using hint

theorem rotated_sqrt_kinetic (chain : WeakPhaseProduct) {D : Density} {φ : Phase} {p θ : ℝ}
    {S T : MatrixGradient} (hD : DensityRegular D p θ S T) (hφ : φ.Regular p)
    (hkin : Integrable fun x => D.charge x * ‖φ.grad x‖ ^ 2) :
    ∃ Z : MatrixGradient, IsMatrixGradientOn Set.univ ((rotatedDensity D φ).power (1/2)) Z ∧
      MemLp (matrixGradNorm Z) 2 ∧
      (∫ x, kineticDensity Z x) ≤ 2 * (∫ x, kineticDensity S x) + 2 * ∫ x, D.charge x * ‖φ.grad x‖^2 :=
  rotated_sqrt_kinetic_of_weak chain hD.sqrt_gradient hD.sqrt_L2 hφ hkin

end TSGA.Localization
