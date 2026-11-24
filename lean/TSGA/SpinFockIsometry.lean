import TSGA.SpinContraction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The one-particle isometry for spin removal

The retained and discarded spinors occupy two copies of the spin Hilbert
space. A retained laboratory observable is extended by zero on the second
copy, then compressed by the isometry. This also works for arbitrary
two-spin observables on the ordered pair of retained particles.
-/

noncomputable section
namespace TSGA.ManyBody

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

abbrev SplitSpin := Fin 2 ⊕ Fin 2
abbrev SpinSplitter := Matrix SplitSpin (Fin 2) ℂ

def SpinSplitter.active (U : SpinSplitter) : SpinMatrix := fun i a => U (.inl i) a

def SpinSplitter.Isometry (U : SpinSplitter) : Prop := U.conjTranspose * U = 1

def spinDilation (S : SpinMatrix) : SpinSplitter :=
  Sum.elim S (CFC.sqrt (1-star S*S) : SpinMatrix)

@[simp] theorem spinDilation_active (S : SpinMatrix) : (spinDilation S).active = S := rfl

theorem spinDilation_isometry {S : SpinMatrix} (hs : star S * S ≤ 1) :
    (spinDilation S).Isometry := by
  let D : SpinMatrix := CFC.sqrt (1-star S*S)
  have hd : D.conjTranspose = D := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hD : D*D = 1-star S*S := CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hs)
  have he : (spinDilation S).conjTranspose * spinDilation S = star S*S+D.conjTranspose*D := by
    ext i j
    change (∑ k : SplitSpin, star (spinDilation S k i) * spinDilation S k j) = _
    simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Fintype.sum_sum_type,spinDilation,D]
    rfl
  unfold SpinSplitter.Isometry
  rw [he,hd,hD]
  abel

/-- Project the two-copy spinor onto its retained part. -/
def retainedSpinProjection : Matrix (Fin 2) SplitSpin ℂ :=
  fun i => Sum.elim (fun j => (1 : SpinMatrix) i j) (fun _ => 0)

theorem retainedSpinProjection_mul (U : SpinSplitter) :
    retainedSpinProjection * U = U.active := by
  ext i j
  simp [retainedSpinProjection,SpinSplitter.active,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]

def retainedSpinTest (A : SpinMatrix) : Matrix SplitSpin SplitSpin ℂ :=
  retainedSpinProjection.conjTranspose * A * retainedSpinProjection

theorem SpinSplitter.compress_one (U : SpinSplitter) (A : SpinMatrix) :
    U.conjTranspose * retainedSpinTest A * U = star U.active * A * U.active := by
  rw [retainedSpinTest, ← retainedSpinProjection_mul,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

abbrev PairSpin := Fin 2 × Fin 2

def retainedPairTest (A : Matrix PairSpin PairSpin ℂ) : Matrix (SplitSpin × SplitSpin) (SplitSpin × SplitSpin) ℂ :=
  (retainedSpinProjection ⊗ₖ retainedSpinProjection).conjTranspose * A * (retainedSpinProjection ⊗ₖ retainedSpinProjection)

theorem SpinSplitter.compress_two (U : SpinSplitter) (A : Matrix PairSpin PairSpin ℂ) :
    (U ⊗ₖ U).conjTranspose * retainedPairTest A * (U ⊗ₖ U) =
      star (U.active ⊗ₖ U.active) * A * (U.active ⊗ₖ U.active) := by
  let P := retainedSpinProjection ⊗ₖ retainedSpinProjection
  have hp : P * (U ⊗ₖ U) = U.active ⊗ₖ U.active := by
    rw [show P = _ from rfl, ← Matrix.mul_kronecker_mul,retainedSpinProjection_mul]
  rw [← hp, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  simp only [retainedPairTest,P,Matrix.mul_assoc]

/-- On a fixed sector the Fock map applies the spin isometry to every
slot, before tracing out the discarded copy. -/
def sectorSpinTensor {a b : Type*} (n : ℕ) (A : Fin n → Matrix a b ℂ) :
    Matrix (Fin n → a) (Fin n → b) ℂ := fun u v => ∏ i, A i (u i) (v i)

theorem sectorSpinTensor_mul {a b c : Type*} [Fintype b] (n : ℕ)
    (A : Fin n → Matrix a b ℂ) (B : Fin n → Matrix b c ℂ) :
    sectorSpinTensor n (fun i => A i*B i) = sectorSpinTensor n A * sectorSpinTensor n B := by
  classical
  ext s t
  simpa only [sectorSpinTensor,Matrix.mul_apply,Finset.prod_mul_distrib] using
    Fintype.prod_sum (fun i : Fin n => fun k : b => A i (s i) k * B i k (t i))

theorem sectorSpinTensor_one {a : Type*} [DecidableEq a] (n : ℕ) :
    sectorSpinTensor n (fun _ => (1 : Matrix a a ℂ)) = 1 := by
  classical
  ext u v
  by_cases h : u = v
  · subst v
    simp only [sectorSpinTensor,Matrix.one_apply_eq,Finset.prod_const_one]
  · obtain ⟨i,hi⟩ : ∃ i, u i ≠ v i := by
      by_contra! hn
      exact h (funext hn)
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem sectorSpinTensor_adjoint {a b : Type*} (n : ℕ) (A : Fin n → Matrix a b ℂ) :
    (sectorSpinTensor n A).conjTranspose = sectorSpinTensor n (fun i => (A i).conjTranspose) := by
  ext i j
  simp [sectorSpinTensor,Matrix.conjTranspose_apply]

theorem SpinSplitter.sector_isometry (U : SpinSplitter) (hU : U.Isometry) (n : ℕ) :
    (sectorSpinTensor n (fun _ => U)).conjTranspose * (sectorSpinTensor n (fun _ => U)) = 1 := by
  rw [sectorSpinTensor_adjoint, ← sectorSpinTensor_mul]
  exact (congrArg (sectorSpinTensor n) (funext (fun _ => hU))).trans (sectorSpinTensor_one n)

/-- Pullback of an arbitrary product of spin observables through the fixed-sector
isometry. An untested particle contributes the identity under an isometry. -/
theorem SpinSplitter.sector_compress (U : SpinSplitter) (n : ℕ)
    (A : Fin n → Matrix SplitSpin SplitSpin ℂ) :
    (sectorSpinTensor n (fun _ => U)).conjTranspose * sectorSpinTensor n A * sectorSpinTensor n (fun _ => U) =
      sectorSpinTensor n (fun i => U.conjTranspose * A i * U) := by
  rw [sectorSpinTensor_adjoint,← sectorSpinTensor_mul,← sectorSpinTensor_mul]

theorem SpinSplitter.sector_permute (U : SpinSplitter) {n : ℕ} (π : Equiv.Perm (Fin n))
    (s : Fin n → SplitSpin) (t : Fin n → Fin 2) :
    sectorSpinTensor n (fun _ => U) (s ∘ π) (t ∘ π) = sectorSpinTensor n (fun _ => U) s t :=
  Equiv.prod_comp π (fun i => U (s i) (t i))

end TSGA.ManyBody
