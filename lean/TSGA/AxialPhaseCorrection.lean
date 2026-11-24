import TSGA.CoulombReplacement
import TSGA.AxialKinetic
import TSGA.GradientForm
import TSGA.SpiralCovariance
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The axial unitary that removes the variation of the wavevector on a tile -/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization
open scoped ComplexOrder MatrixOrder InnerProductSpace ContDiff

private def halfSpin (k : Fin 2) : ℝ := if k = 0 then -(1/2) else 1/2

/-- The residual angle includes a constant axial rotation, whose gradient vanishes. -/
def phaseCorrection (φ : Phase) (q : Position) (x : Position) : unitary SpinMatrix :=
  ⟨spinRotation (φ.value x - ⟪q,x⟫_ℝ),
    (Matrix.mem_specialUnitaryGroup_iff.mp (spinRotation_mem_specialUnitaryGroup _)).1⟩

def phaseCorrectionGradient (φ : Phase) (q : Position) : MatrixGradient := fun x i =>
  Matrix.diagonal fun k => phaseFactor (halfSpin k * (φ.value x - ⟪q,x⟫_ℝ)) *
    (Complex.I * (halfSpin k : ℂ) * ((φ.grad x i - q i : ℝ) : ℂ))

def phaseCorrectionWeight (φ : Phase) (q : Position) (x : Position) : ℝ :=
  ‖φ.grad x - q‖ ^ 2 / 4

private theorem plane_weak (q : Position) (b : ℝ) (i : Fin 3) :
    WeakPartialOn Set.univ i (fun x => phaseFactor (-b * ⟪q,x⟫_ℝ))
      (fun x => phaseFactor (-b * ⟪q,x⟫_ℝ) * (Complex.I * ((-b*q i : ℝ) : ℂ))) := by
  let L : Position →L[ℝ] ℝ := -b • innerSL ℝ q
  let f := fun x : Position => Complex.exp (((L x : ℝ) : ℂ) * Complex.I)
  let v : Position := PiLp.single 2 i 1
  have hf : ContDiff ℝ ∞ f :=
    ((Complex.ofRealCLM.contDiff.comp L.contDiff).mul contDiff_const).cexp
  have he (x : Position) : L x = -b * ⟪q,x⟫_ℝ := rfl
  have hev : L v = -b*q i := by simp [he, v, EuclideanSpace.inner_single_right]
  have df (x : Position) : fderiv ℝ f x v = f x * (Complex.I * ((-b*q i : ℝ) : ℂ)) := by
    have h := (((Complex.ofRealCLM.hasFDerivAt.comp x L.hasFDerivAt).mul_const Complex.I).cexp).fderiv
    change fderiv ℝ (fun x => Complex.exp (((Complex.ofRealCLM ∘ L) x) * Complex.I)) x _ = _
    rw [h]
    change f x * (Complex.I * ((L v : ℝ) : ℂ)) = _
    rw [hev]
  change WeakPartialOn _ _ f (fun x => f x * (Complex.I * ((-b*q i : ℝ) : ℂ)))
  have hc := hf.continuous
  have hcd : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨hc.locallyIntegrable.locallyIntegrableOn _,
    (hc.mul continuous_const).locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro ψ hψ hs _
  have hψd := (hψ.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  have ibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := ψ) (g := f) (v := v)
    ((hψd.smul hc).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ v).smul_right)
    ((hψ.continuous.smul hcd).integrable_of_hasCompactSupport hs.smul_right)
    ((hψ.continuous.smul hc).integrable_of_hasCompactSupport hs.smul_right)
    (fun x _ => hψ.differentiable (by simp) x) (fun x _ => hf.differentiable (by simp) x)
  simp only [Measure.restrict_univ]
  simpa only [df, neg_neg] using congrArg Neg.neg ibp.symm

private theorem residual_phase_weak (chain : WeakPhaseProduct) {φ : Phase} {p : ℝ}
    (hφ : φ.Regular p) (q : Position) (b : ℝ) (i : Fin 3) :
    WeakPartialOn Set.univ i (fun x => phaseFactor (b * (φ.value x - ⟪q,x⟫_ℝ)))
      (fun x => phaseFactor (b * (φ.value x - ⟪q,x⟫_ℝ)) *
        (Complex.I * (b : ℂ) * ((φ.grad x i - q i : ℝ) : ℂ))) := by
  have h := chain φ hφ b i _ _ (plane_weak q b i)
  have factor (x : Position) : phaseFactor (b * (φ.value x - ⟪q,x⟫_ℝ)) =
      phaseFactor (b * φ.value x) * phaseFactor (-b * ⟪q,x⟫_ℝ) := by
    rw [← phaseFactor_add]
    congr 1
    ring
  simp_rw [factor]
  convert h using 2
  push_cast
  ring

private theorem correction_diagonal (φ : Phase) (q x : Position) :
    (phaseCorrection φ q x : SpinMatrix) =
      Matrix.diagonal (fun k => phaseFactor (halfSpin k * (φ.value x - ⟪q,x⟫_ℝ))) := by
  apply congrArg Matrix.diagonal
  funext k
  apply congrArg phaseFactor
  change (if k = 0 then -((φ.value x - ⟪q,x⟫_ℝ)/2) else (φ.value x - ⟪q,x⟫_ℝ)/2) = _
  unfold halfSpin
  split_ifs <;> ring

theorem phaseCorrection_weak (chain : WeakPhaseProduct) {φ : Phase} {p : ℝ}
    (hφ : φ.Regular p) (q : Position) :
    IsMatrixGradientOn Set.univ (fun x => (phaseCorrection φ q x : SpinMatrix))
      (phaseCorrectionGradient φ q) := by
  intro i j k
  by_cases e : j = k
  · subst k
    simpa only [correction_diagonal, phaseCorrectionGradient, Matrix.diagonal_apply_eq] using
      residual_phase_weak chain hφ q (halfSpin j) i
  · simpa only [correction_diagonal, phaseCorrectionGradient, Matrix.diagonal_apply_ne _ e] using
      (weakPartialOn_zero (F := ℂ) Set.univ i)

theorem phaseCorrection_adjoint_weak (chain : WeakPhaseProduct) {φ : Phase} {p : ℝ}
    (hφ : φ.Regular p) (q : Position) :
    IsMatrixGradientOn Set.univ (fun x => ((star (phaseCorrection φ q x) : unitary SpinMatrix) : SpinMatrix))
      (fun x i => star (phaseCorrectionGradient φ q x i)) :=
  fun i j k => (phaseCorrection_weak chain hφ q i k j).conjugate

private theorem phaseCoefficient (b a d : ℝ) :
    star (phaseFactor a * (Complex.I * (b:ℂ) * (d:ℂ))) *
      (phaseFactor a * (Complex.I * (b:ℂ) * (d:ℂ))) = ((b^2*d^2 : ℝ) : ℂ) := by
  change (starRingEnd ℂ) _ * _ = _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [← Complex.sq_norm, phaseFactor, Complex.norm_exp, mul_pow, sq_abs]

/-- For this diagonal unitary the kinetic matrix is exactly scalar, including
the factor one quarter from the two opposite half spin phases. -/
theorem phaseCorrection_square (φ : Phase) (q x : Position) :
    (∑ i, star (phaseCorrectionGradient φ q x i) * phaseCorrectionGradient φ q x i) =
      (phaseCorrectionWeight φ q x : ℂ) • (1 : SpinMatrix) := by
  classical
  have hspin (j : Fin 2) : (halfSpin j)^2 = 1/4 := by
    unfold halfSpin
    split_ifs <;> norm_num
  ext j k
  simp only [Matrix.sum_apply, phaseCorrectionGradient, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.smul_apply, Matrix.one_apply]
  by_cases e : j = k
  · subst k
    simp only [Matrix.diagonal_apply_eq, Pi.star_apply, phaseCoefficient, hspin, ite_true, smul_eq_mul,
      mul_one]
    unfold phaseCorrectionWeight
    rw [EuclideanSpace.real_norm_sq_eq]
    push_cast
    simp only [PiLp.sub_apply, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  · simp [e]

theorem phaseCorrection_adjoint_square (φ : Phase) (q x : Position) :
    (∑ i, star (star (phaseCorrectionGradient φ q x i)) * star (phaseCorrectionGradient φ q x i)) =
      (phaseCorrectionWeight φ q x : ℂ) • (1 : SpinMatrix) := by
  rw [← phaseCorrection_square]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_star, phaseCorrectionGradient, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext j
  exact mul_comm _ _

variable {K : Set Position}

theorem SpiralTaper.phaseCorrection_target (t : SpiralTaper K) (M : Density) (φ : Phase) :
    (conjugatedDensity (t.field M) (phaseCorrection φ t.wavevector)).matrix = (t.phaseField M φ).matrix := by
  funext x
  change rotate (φ.value x - ⟪t.wavevector,x⟫_ℝ)
      ((t.shape x : ℂ) • rotate ⟪t.wavevector,x⟫_ℝ (M.matrix x)) = _
  rw [SSW.rotate_smul, ← SSW.rotate_add, sub_add_cancel]
  rfl

@[simp] theorem SpiralTaper.field_charge (t : SpiralTaper K) (M : Density) (x : Position) :
    (t.field M).charge x = t.shape x * M.charge x := by
  change ((t.shape x : ℂ) • rotate _ _).trace.re = _
  rw [Matrix.trace_smul, trace_rotate, smul_eq_mul, Complex.re_ofReal_mul]
  rfl

@[simp] theorem SpiralTaper.phaseField_charge (t : SpiralTaper K) (M : Density) (φ : Phase) (x : Position) :
    (t.phaseField M φ).charge x = t.shape x * M.charge x := by
  change ((t.shape x : ℂ) • rotate _ _).trace.re = _
  rw [Matrix.trace_smul, trace_rotate, smul_eq_mul, Complex.re_ofReal_mul]
  rfl

end TSGA.ManyBody
