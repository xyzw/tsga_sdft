import TSGA.LevyLieb
import TSGA.SpectralLipschitz
import TSGA.SpinContraction
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! # Spin-dependent removal of particles

Geometric localization acts on the one- and two-particle reduced densities.
Their spin traces show that a constant contraction can only decrease the
kinetic and Coulomb expectations. Subtracting the direct energy accounts
for the explicit correction in Lemma E.1.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Matrix TSGA.Localization
open scoped MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

theorem trace_product_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  obtain ⟨P, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [← Matrix.trace_mul_cycle P B (star P)]
  exact (RCLike.nonneg_iff.mp (hB.mul_mul_conjTranspose_same P).trace_nonneg).1

theorem contraction_trace_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X T : Matrix ι ι ℂ}
    (h : X ≤ 1) (hT : T.PosSemidef) : (X*T).trace.re ≤ T.trace.re := by
  have hu := trace_product_nonneg (Matrix.le_iff.mp h) hT
  simpa [sub_mul, Matrix.trace_sub] using hu

theorem contraction_pair_le_one {X : SpinMatrix} (hX : X.PosSemidef) (h : X ≤ 1) : X ⊗ₖ X ≤ 1 := by
  have hs := Matrix.le_iff.mp h
  calc
    X ⊗ₖ X ≤ X ⊗ₖ X + X ⊗ₖ (1-X) := le_add_of_nonneg_right (hX.kronecker hs).nonneg
    _ = X ⊗ₖ 1 := by rw [← Matrix.kronecker_add, add_sub_cancel]
    _ ≤ X ⊗ₖ 1 + (1-X) ⊗ₖ 1 := le_add_of_nonneg_right (hs.kronecker Matrix.PosSemidef.one).nonneg
    _ = 1 := by rw [← Matrix.add_kronecker, add_sub_cancel, Matrix.one_kronecker_one]

/-- The standard Fock-space geometric localization law tested on the
one- and two-particle spin observables. The positive spin traces K and W
are taken before removing particles. -/
def FockSpinLocalization : Prop :=
  ∀ Γ : MixedState, ∃ (K : SpinMatrix) (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    K.PosSemidef ∧ W.PosSemidef ∧ K.trace.re = Γ.kinetic ∧ W.trace.re = Γ.interaction ∧
    ∀ B : SpinMatrix, star B * B ≤ 1 →
      ∃ Λ : MixedState, (Λ.matrixDensity =ᵐ[volume] fun x => B * Γ.matrixDensity x * star B) ∧
        Λ.kinetic = ((star B * B) * K).trace.re ∧
        Λ.interaction = (((star B * B) ⊗ₖ (star B * B)) * W).trace.re

/-- The first inequality of Lemma E.1, for arbitrary representable fields. -/
theorem levyLieb_spin_removal (loc : FockSpinLocalization) {M : Position → SpinMatrix}
    (rep : ∃ Γ, feasible M Γ) (B : SpinMatrix) (hB : star B * B ≤ 1) :
    levyLieb (fun x => B * M x * star B) ≤ levyLieb M := by
  apply le_levyLieb rep
  intro Γ hΓ
  obtain ⟨K, W, hK, hW, hk, hw, map⟩ := loc Γ
  obtain ⟨Λ, hΛ, ht, hv⟩ := map B hB
  have hf : feasible (fun x => B * M x * star B) Λ :=
    hΛ.trans (hΓ.mono fun x hx => congrArg (fun P => B * P * star B) hx)
  apply (levyLieb_le hf).trans
  rw [ht, hv, ← hk, ← hw]
  exact add_le_add (contraction_trace_le hB hK)
    (contraction_trace_le (contraction_pair_le_one (star_mul_self_nonneg B).posSemidef hB) hW)

theorem hartree_const_mul (a : ℝ) (f : Position → ℝ) :
    hartree (fun x => a * f x) = a^2 * hartree f := by
  have h (x y : Position) : a*f x*(a*f y)/‖x-y‖ = a^2 * (f x*f y/‖x-y‖) := by ring
  simp only [hartree, h, integral_const_mul]
  ring

theorem energy_cutoff_removal_of_factor (loc : FockSpinLocalization) {M N S : SpinMatrix}
    (hS : star S * S ≤ 1) (hN : S * M * star S = N) (f : Position → ℝ)
    (rep : ∃ Γ, feasible (fun x => f x • M) Γ) :
    energy (fun x => f x • N) ≤ energy (fun x => f x • M) +
      (M.trace.re^2 - N.trace.re^2) * hartree f := by
  have h := levyLieb_spin_removal loc rep S hS
  simp only [Matrix.mul_smul, Matrix.smul_mul, hN] at h
  have ht (A : SpinMatrix) : (fun x => (f x • A).trace.re) = fun x => A.trace.re * f x := by
    ext x
    simp [Matrix.trace_smul, Complex.real_smul, mul_comm]
  simp only [energy, ht, hartree_const_mul]
  linarith only [h]

/-- The ordered-matrix conclusion of Lemma E.1. The spin contraction
exists even if the parent matrix has a zero eigenvalue. -/
theorem energy_ordered_cutoff (loc : FockSpinLocalization) {A B : SpinMatrix}
    (hA : A.PosSemidef) (hAB : A ≤ B) (f : Position → ℝ)
    (rep : ∃ Γ, feasible (fun x => f x • B) Γ) :
    energy (fun x => f x • A) ≤ energy (fun x => f x • B) +
      (B.trace.re^2 - A.trace.re^2) * hartree f := by
  obtain ⟨S, hS, _, h⟩ := exists_spinContraction hA (Matrix.le_iff.mp hAB)
  exact energy_cutoff_removal_of_factor loc (Matrix.le_iff.mpr hS) h f rep

/-- The squared change of the spin square root is bounded by the charge
removed, including when the original spin density is singular. -/
theorem sqrt_charge_deficit {A B : SpinMatrix} (hA : A.PosSemidef) (hAB : A ≤ B) :
    hilbertSchmidt (CFC.sqrt B - CFC.sqrt A)^2 ≤ B.trace.re - A.trace.re := by
  have hb := hA.nonneg.trans hAB
  let U := CFC.sqrt A
  let V := CFC.sqrt B
  have hu : U*U = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hv : V*V = B := CFC.sqrt_mul_sqrt_self B hb
  have hU : star U = U := (CFC.sqrt_nonneg A).star_eq
  have hV : star V = V := (CFC.sqrt_nonneg B).star_eq
  have hc := trace_product_nonneg (CFC.sqrt_nonneg A).posSemidef
    (Matrix.le_iff.mp (CFC.sqrt_le_sqrt A B hAB))
  change 0 ≤ (U*(V-U)).trace.re at hc
  simp only [mul_sub, hu, Matrix.trace_sub, Complex.sub_re] at hc
  change hilbertSchmidt (V-U)^2 ≤ _
  rw [hilbertSchmidt, Real.sq_sqrt (by positivity), hs_trace, star_sub, hV, hU]
  simp only [sub_mul, mul_sub, hv, hu, Matrix.trace_sub, Complex.sub_re, Matrix.trace_mul_comm V U]
  linarith only [hc]

theorem exists_spinContraction_charge_deficit {A B : SpinMatrix} (hA : A.PosSemidef) (hAB : A ≤ B) :
    ∃ S : SpinMatrix, star S * S ≤ 1 ∧ S * B * star S = A ∧
      hilbertSchmidt ((1 - S) * CFC.sqrt B)^2 ≤ B.trace.re - A.trace.re := by
  obtain ⟨S, hS, hs, h⟩ := exists_spinContraction hA (Matrix.le_iff.mp hAB)
  refine ⟨S, Matrix.le_iff.mpr hS, h, ?_⟩
  simpa only [sub_mul, one_mul, hs] using sqrt_charge_deficit hA hAB

end TSGA.ManyBody
