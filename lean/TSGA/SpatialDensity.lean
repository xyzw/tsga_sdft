import TSGA.KineticEnergy

/-! # Finite-dimensional space for the kinetic estimates of Section 4.4

The Coulomb model uses three spatial coordinates. These definitions let the
one-particle kinetic estimates use the same two spin components on `ℝᵈ`.
-/

noncomputable section

namespace TSGA.ManyBody.Spatial

open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate ComplexOrder

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Gradient (d : ℕ) := Point d → Fin d → SpinMatrix

variable {d : ℕ}

def WeakPartial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (i : Fin d) (f g : Point d → F) : Prop :=
  LocallyIntegrable f volume ∧ LocallyIntegrable g volume ∧
    ∀ ψ : Point d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, (fderiv ℝ ψ x (PiLp.single 2 i 1)) • f x) = -(∫ x, ψ x • g x)

structure Density (d : ℕ) where
  matrix : Point d → SpinMatrix
  positive : ∀ x, (matrix x).PosSemidef

def Density.charge (D : Density d) (x : Point d) : ℝ := (D.matrix x).trace.re

theorem Density.charge_nonneg (D : Density d) (x : Point d) : 0 ≤ D.charge x :=
  (RCLike.nonneg_iff.mp (D.positive x).trace_nonneg).1

def Density.power (D : Density d) (a : ℝ) (x : Point d) : SpinMatrix :=
  (D.positive x).isHermitian.cfc (fun t => t ^ a)

def IsMatrixGradient (M : Point d → SpinMatrix) (S : Gradient d) : Prop :=
  ∀ i j k, WeakPartial i (fun x => M x j k) (fun x => S x i j k)

def kineticDensity (S : Gradient d) (x : Point d) : ℝ := ∑ i, ∑ j, ∑ k, ‖S x i j k‖ ^ 2

theorem kineticDensity_nonneg (S : Gradient d) (x : Point d) : 0 ≤ kineticDensity S x := by
  unfold kineticDensity
  positivity

def sqrtKinetic (S : Gradient d) : ℝ := ∫ x, kineticDensity S x

structure SqrtRegular (D : Density d) (S : Gradient d) : Prop where
  charge : Integrable D.charge
  weak : IsMatrixGradient (D.power (1/2)) S
  grad : MemLp (fun x => Real.sqrt (kineticDensity S x)) 2

/-- Natural orbitals of a trace-class contraction with finite kinetic energy. -/
structure OneBody (d : ℕ) where
  occupation : ℕ → ℝ
  occupation_mem : ∀ k, occupation k ∈ Set.Icc 0 1
  finite_trace : Summable occupation
  orbital : ℕ → Fin 2 → Point d → ℂ
  orbital_L2 : ∀ k s, MemLp (orbital k s) 2 volume
  orthonormal : ∀ k l, (∑ s, ∫ x, conj (orbital k s x) * orbital l s x) = if k = l then 1 else 0
  gradient : ℕ → Fin 2 → Fin d → Point d → ℂ
  weak : ∀ k s i, WeakPartial i (orbital k s) (gradient k s i)
  gradient_L2 : ∀ k s i, MemLp (gradient k s i) 2 volume
  finite_kinetic : Summable fun k => occupation k * ∑ s, ∑ i, ∫ x, ‖gradient k s i x‖ ^ 2

def OneBody.kernel (γ : OneBody d) (x y : Point d) : SpinMatrix := fun i j =>
  ∑' k, (γ.occupation k : ℂ) * γ.orbital k i x * conj (γ.orbital k j y)

def OneBody.matrixDensity (γ : OneBody d) (x : Point d) : SpinMatrix := γ.kernel x x

def OneBody.kinetic (γ : OneBody d) : ℝ :=
  ∑' k, γ.occupation k * ∑ s, ∑ i, ∫ x, ‖γ.gradient k s i x‖ ^ 2

theorem OneBody.kinetic_nonneg (γ : OneBody d) : 0 ≤ γ.kinetic :=
  tsum_nonneg fun k => mul_nonneg (γ.occupation_mem k).1
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

def bestKinetic (M : Point d → SpinMatrix) : ℝ :=
  sInf {t | ∃ γ : OneBody d, γ.matrixDensity =ᵐ[volume] M ∧ t = γ.kinetic}

theorem bestKinetic_le {D : Density d} {γ : OneBody d} (hd : γ.matrixDensity =ᵐ[volume] D.matrix) :
    bestKinetic D.matrix ≤ γ.kinetic :=
  csInf_le ⟨0, fun _ ⟨g, _, ht⟩ => ht ▸ g.kinetic_nonneg⟩ ⟨γ, hd, rfl⟩

end TSGA.ManyBody.Spatial
