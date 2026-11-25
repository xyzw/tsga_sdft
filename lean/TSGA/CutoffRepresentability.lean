import TSGA.PhysicalTSGA
import Mathlib.Analysis.Matrix.Order

/-! # Representability of scalar cutoffs of a fixed spin density

The square root of fA is √f times the constant matrix √A. This identifies
its weak gradient entry by entry and gives its exact kinetic cost.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem density_root_nonneg (D : Density) (x : Position) : 0 ≤ D.power (1/2) x := by
  let h := (D.positive x).isHermitian
  let P := Matrix.diagonal fun i => ((h.eigenvalues i ^ (1/2:ℝ) : ℝ) : ℂ)
  have hP : P.PosSemidef := Matrix.PosSemidef.diagonal fun i =>
    RCLike.nonneg_iff.mpr ⟨Real.rpow_nonneg ((D.positive x).eigenvalues_nonneg i) _, rfl⟩
  exact (hP.mul_mul_conjTranspose_same (h.eigenvectorUnitary : SpinMatrix)).nonneg

private theorem scalar_times_entry {i : Fin 3} {f g : Position → ℝ}
    (h : WeakPartialOn Set.univ i f g) (z : ℂ) :
    WeakPartialOn Set.univ i (fun x => f x • z) (fun x => g x • z) := by
  have hloc {v : Position → ℝ} (hv : LocallyIntegrableOn v Set.univ) :
      LocallyIntegrableOn (fun x => v x • z) Set.univ := by
    intro x hx
    obtain ⟨s, hs, hi⟩ := hv x hx
    exact ⟨s, hs, ((1 : ℝ →L[ℝ] ℝ).smulRight z).integrable_comp hi⟩
  refine ⟨hloc h.1, hloc h.2.1, ?_⟩
  intro ψ hψ hc hU
  have he := h.2.2 ψ hψ hc hU
  simp only [smul_eq_mul] at he
  simp only [smul_smul, integral_smul_const, he, neg_smul]

/-- The scalar Sobolev hypothesis is sufficient for a tapered spin matrix
of arbitrary trace and rank. The gradient identity also applies at vacuum. -/
theorem sqrtRegular_cutoff {f : Position → ℝ} (hf : ∀ x, 0 ≤ f x) (hi : Integrable f)
    (g : Position → Position) (hw : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i))
    (hg : MemLp g 2) {A : SpinMatrix} (ha : A.PosSemidef) :
    let D : Density := ⟨fun x => f x • A, fun x => ha.smul (hf x)⟩
    ∃ S, SqrtRegular D S ∧ sqrtKinetic S = A.trace.re * ∫ x, ‖g x‖^2 := by
  let D : Density := ⟨fun x => f x • A, fun x => ha.smul (hf x)⟩
  let P : Density := ⟨fun _ => A, fun _ => ha⟩
  let Q := P.power (1/2) 0
  let S : MatrixGradient := fun x i => g x i • Q
  have ht : 0 ≤ A.trace.re := (RCLike.nonneg_iff.mp ha.trace_nonneg).1
  have hq : Q*Q=A := P.sqrt_mul_self 0
  have root (x) : D.power (1/2) x = √(f x) • Q := by
    apply (CFC.mul_self_eq_mul_self_iff _ _ (density_root_nonneg D x)
      ((Matrix.nonneg_iff_posSemidef.mp (density_root_nonneg P 0)).smul (Real.sqrt_nonneg (f x))).nonneg).mp
    rw [D.sqrt_mul_self, Matrix.smul_mul, Matrix.mul_smul, hq, smul_smul, Real.mul_self_sqrt (hf x)]
  have norm_sq (x : Position) : matrixGradNorm S x ^ 2 = ‖g x‖^2*A.trace.re := by
    unfold matrixGradNorm
    rw [Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2]
    simp only [S, Matrix.smul_apply, norm_smul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul,
      show (∑ j, ∑ k, ‖Q j k‖^2) = A.trace.re from sqrt_hilbertSchmidt_sq P 0]
  have norm_eq (x : Position) : matrixGradNorm S x = ‖g x‖ * √A.trace.re := by
    apply (sq_eq_sq₀ (show 0 ≤ matrixGradNorm S x from Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [norm_sq, mul_pow, Real.sq_sqrt ht]
  change ∃ S, SqrtRegular D S ∧ _
  refine ⟨S, ⟨?_, ?_, ?_⟩, ?_⟩
  · change Integrable (fun x => (f x • A).trace.re)
    simpa only [Density.charge, D, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul] using
      hi.mul_const A.trace.re
  · intro i j k
    simp only [root, S, Matrix.smul_apply]
    exact scalar_times_entry (hw i) (Q j k)
  · rw [show matrixGradNorm S = (fun x => ‖g x‖ * √A.trace.re) from funext norm_eq]
    exact hg.norm.mul_const (√A.trace.re)
  · simp only [sqrtKinetic, kineticDensity, norm_sq, integral_mul_const, mul_comm A.trace.re]

theorem FiniteEnergyInputs.representable_cutoff (H : FiniteEnergyInputs) {f : Position → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hi : Integrable f) (g : Position → Position)
    (hw : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i))
    (hg : MemLp g 2) {A : SpinMatrix} (ha : A.PosSemidef) :
    ∃ Γ : MixedState, feasible (fun x => f x • A) Γ := by
  let D : Density := ⟨fun x => f x • A, fun x => ha.smul (hf x)⟩
  obtain ⟨S, hS, _⟩ := sqrtRegular_cutoff hf hi g hw hg ha
  exact H.representable (D := D) (S := S) hS

end TSGA.ManyBody
