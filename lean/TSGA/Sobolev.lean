import TSGA.Spin
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! # Density and phase fields on three-dimensional space

Weak derivatives are specified by integration against smooth compactly supported
test functions. All fields are representatives, so the phase gradient can be
evaluated pointwise to specify the open region used in the local estimate.
-/

namespace TSGA

open MeasureTheory
open scoped ContDiff ComplexOrder

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev MatrixGradient := Position → Fin 3 → SpinMatrix

/-- Distributional partial derivative in coordinate direction `i` on an open set. -/
def WeakPartialOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (U : Set Position) (i : Fin 3) (f g : Position → F) : Prop :=
  LocallyIntegrableOn f U ∧ LocallyIntegrableOn g U ∧
  ∀ ψ : Position → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    (∫ x in U, (fderiv ℝ ψ x (PiLp.single 2 i 1)) • f x) = -(∫ x in U, ψ x • g x)

@[simp] theorem weakPartialOn_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (U : Set Position) (i : Fin 3) :
    WeakPartialOn U i (fun _ => (0 : F)) (fun _ => 0) := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  intros
  simp

/-- Local `Lᵖ` on an open set, using balls contained in that set. -/
def LocalLpOn {F : Type*} [NormedAddCommGroup F] (U : Set Position)
    (p : ℝ) (f : Position → F) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∧
    MemLp f (ENNReal.ofReal p) (volume.restrict (Metric.ball x r))

/-- A positive semidefinite spin density matrix field. -/
structure Density where
  matrix : Position → SpinMatrix
  positive : ∀ x, (matrix x).PosSemidef

noncomputable def Density.charge (D : Density) (x : Position) : ℝ := (D.matrix x).trace.re

theorem Density.charge_nonneg (D : Density) (x : Position) : 0 ≤ D.charge x :=
  (RCLike.nonneg_iff.mp (D.positive x).trace_nonneg).1

/-- Spectral power of a positive semidefinite spin matrix. -/
noncomputable def Density.power (D : Density) (a : ℝ) (x : Position) : SpinMatrix :=
  (D.positive x).isHermitian.cfc (fun t => t ^ a)

/-- Euclidean norm of a gradient with Hilbert–Schmidt norm in the matrix indices. -/
noncomputable def matrixGradNorm (G : MatrixGradient) (x : Position) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ∑ k, ‖G x i j k‖ ^ 2)

def IsMatrixGradientOn (U : Set Position) (M : Position → SpinMatrix) (G : MatrixGradient) :
    Prop := ∀ i j k, WeakPartialOn U i (fun x => M x j k) (fun x => G x i j k)

/-- The density hypotheses common to the TSGA and LSDA. The two gradient
representatives are for the square root and the `θ` power, respectively. -/
structure DensityRegular (D : Density) (p θ : ℝ) (S T : MatrixGradient) : Prop where
  charge_L1 : Integrable D.charge
  charge_L2 : MemLp D.charge 2
  sqrt_gradient : IsMatrixGradientOn Set.univ (D.power (1 / 2)) S
  sqrt_L2 : MemLp (matrixGradNorm S) 2
  theta_gradient : IsMatrixGradientOn Set.univ (D.power θ) T
  theta_Lp : MemLp (matrixGradNorm T) (ENNReal.ofReal p)

/-- The local `W¹ᵖ` assumption for a supplied representative of the gradient.
Every requirement is local to `U`, including identification of the derivative. -/
def RootRegularOn (U : Set Position) (D : Density) (p : ℝ) (G : MatrixGradient) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∧
    IsMatrixGradientOn (Metric.ball x r) (D.power (1 / p)) G ∧
    (∀ j k, MemLp (fun y => D.power (1 / p) y j k) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x r))) ∧
    MemLp (matrixGradNorm G) (ENNReal.ofReal p) (volume.restrict (Metric.ball x r))

@[simp] theorem rootRegularOn_empty (D : Density) (p : ℝ) (G : MatrixGradient) :
    RootRegularOn ∅ D p G := by simp [RootRegularOn]

structure Phase where
  value : Position → ℝ
  grad : Position → Position
  hessian : Position → Fin 3 → Fin 3 → ℝ

def Phase.zero : Phase := ⟨fun _ => 0, fun _ => 0, fun _ _ _ => 0⟩

def Phase.active (φ : Phase) : Set Position := {x | φ.grad x ≠ 0}

@[simp] theorem active_zero : Phase.zero.active = ∅ := by ext x; simp [Phase.active, Phase.zero]

noncomputable def Phase.hessianNorm (φ : Phase) (x : Position) : ℝ :=
  Real.sqrt (∑ i, ∑ j, φ.hessian x i j ^ 2)

/-- A local `W²ᵖ` phase together with its continuous gradient representative. -/
structure Phase.Regular (φ : Phase) (p : ℝ) : Prop where
  continuous_grad : Continuous φ.grad
  value_Lp : LocalLpOn Set.univ p φ.value
  grad_Lp : ∀ i, LocalLpOn Set.univ p fun x => φ.grad x i
  hessian_Lp : ∀ i j, LocalLpOn Set.univ p fun x => φ.hessian x i j
  weak_grad : ∀ i, WeakPartialOn Set.univ i φ.value fun x => φ.grad x i
  weak_hessian : ∀ i j, WeakPartialOn Set.univ i (fun x => φ.grad x j) fun x => φ.hessian x i j

theorem Phase.Regular.isOpen_active {φ : Phase} {p : ℝ} (h : φ.Regular p) :
    IsOpen φ.active := isOpen_ne_fun h.continuous_grad continuous_const

private theorem localLpOn_univ_zero (p : ℝ) :
    LocalLpOn Set.univ p (fun _ => (0 : ℝ)) := by
  intro x _
  exact ⟨1, zero_lt_one, Set.subset_univ _, MemLp.zero⟩

@[simp] theorem regular_zero (p : ℝ) : Phase.zero.Regular p := by
  exact ⟨continuous_const, localLpOn_univ_zero p, fun _ => localLpOn_univ_zero p,
    fun _ _ => localLpOn_univ_zero p, fun i => weakPartialOn_zero _ i,
    fun i _ => weakPartialOn_zero _ i⟩

end TSGA
