import TSGA.LevyLieb
import TSGA.ErrorDensity
import Mathlib.Analysis.MeanInequalitiesPow

/-! # The kinetic constrained search and the quasi-free upper bound

Natural orbitals describe a positive one-body contraction of finite trace.
The lower and upper energy estimates use the same grand-canonical search as
`ManyBody.energy`. Quasi-free realization and the Lieb–Oxford inequality are
explicit physical inputs.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization
open scoped ComplexConjugate ComplexOrder

/-- A one-body density matrix in its natural orbital decomposition. -/
structure OneBody where
  occupation : ℕ → ℝ
  occupation_mem : ∀ k, occupation k ∈ Set.Icc 0 1
  finite_trace : Summable occupation
  orbital : ℕ → Fin 2 → Position → ℂ
  orbital_L2 : ∀ k s, MemLp (orbital k s) 2 volume
  orthonormal : ∀ k l, (∑ s, ∫ x, conj (orbital k s x) * orbital l s x) = if k = l then 1 else 0
  gradient : ℕ → Fin 2 → Fin 3 → Position → ℂ
  weak : ∀ k s i, WeakPartialOn Set.univ i (orbital k s) (gradient k s i)
  gradient_L2 : ∀ k s i, MemLp (gradient k s i) 2 volume
  finite_kinetic : Summable fun k => occupation k * ∑ s, ∑ i, ∫ x, ‖gradient k s i x‖ ^ 2

/-- The integral kernel of the spin density operator in its natural orbitals. -/
def OneBody.kernel (γ : OneBody) (x y : Position) : SpinMatrix := fun i j =>
  ∑' k, (γ.occupation k : ℂ) * γ.orbital k i x * conj (γ.orbital k j y)

def OneBody.matrixDensity (γ : OneBody) (x : Position) : SpinMatrix := γ.kernel x x

def OneBody.kinetic (γ : OneBody) : ℝ :=
  ∑' k, γ.occupation k * ∑ s, ∑ i, ∫ x, ‖γ.gradient k s i x‖ ^ 2

def OneBody.exchange (γ : OneBody) : ℝ :=
  (∫ x, ∫ y, (∑ i, ∑ j, ‖γ.kernel x y i j‖ ^ 2) / ‖x-y‖) / 2

theorem OneBody.kinetic_nonneg (γ : OneBody) : 0 ≤ γ.kinetic := by
  exact tsum_nonneg fun k => mul_nonneg (γ.occupation_mem k).1
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

theorem OneBody.exchange_nonneg (γ : OneBody) : 0 ≤ γ.exchange := by
  unfold OneBody.exchange
  apply div_nonneg _ (by norm_num)
  exact integral_nonneg fun x => integral_nonneg fun y => div_nonneg
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (norm_nonneg _)

def bestKinetic (M : Position → SpinMatrix) : ℝ :=
  sInf {t | ∃ γ : OneBody, γ.matrixDensity =ᵐ[volume] M ∧ t = γ.kinetic}

theorem bestKinetic_le {D : Density} {γ : OneBody} (hd : γ.matrixDensity =ᵐ[volume] D.matrix) :
    bestKinetic D.matrix ≤ γ.kinetic :=
  csInf_le ⟨0, fun _ ⟨g, _, ht⟩ => ht ▸ g.kinetic_nonneg⟩ ⟨γ, hd, rfl⟩

/-- The quasi-free mixed state with prescribed one-body density operator.
Its interaction expectation is the direct energy minus exchange. -/
def QuasiFreeRealization : Prop := ∀ γ : OneBody, ∃ Γ : MixedState,
  Γ.matrixDensity =ᵐ[volume] γ.matrixDensity ∧ Γ.kinetic = γ.kinetic ∧
  Γ.interaction = hartree (fun x => (γ.matrixDensity x).trace.re) - γ.exchange

theorem energy_le_bestKinetic (qf : QuasiFreeRealization) {D : Density}
    (hD : ∃ γ : OneBody, γ.matrixDensity =ᵐ[volume] D.matrix) : energy D.matrix ≤ bestKinetic D.matrix := by
  obtain ⟨g, hg⟩ := hD
  unfold bestKinetic
  refine le_csInf (s := {t : ℝ | ∃ γ : OneBody, γ.matrixDensity =ᵐ[volume] D.matrix ∧ t = γ.kinetic})
    ⟨g.kinetic, g, hg, rfl⟩ ?_
  rintro _ ⟨γ, hd, rfl⟩
  obtain ⟨Γ, heq, hκ, hW⟩ := qf γ
  have h := levyLieb_le (heq.trans hd : feasible D.matrix Γ)
  have hj := hartree_congr (hd.mono fun x hx => congrArg (fun M : SpinMatrix => M.trace.re) hx)
  unfold energy
  rw [hκ, hW, hj] at h
  linarith [γ.exchange_nonneg]

/-- The hypotheses on an unrotated density needed by the finite-energy trial construction. -/
structure SqrtRegular (D : Density) (S : MatrixGradient) : Prop where
  charge : Integrable D.charge
  weak : IsMatrixGradientOn Set.univ (D.power (1/2)) S
  grad : MemLp (matrixGradNorm S) 2

def chargeMoment (D : Density) (a : ℝ) : ℝ := ∫ x, D.charge x ^ a

def traceMoment (D : Density) (a : ℝ) : ℝ := ∫ x, (D.power a x).trace.re

def sqrtKinetic (S : MatrixGradient) : ℝ := ∫ x, kineticDensity S x

theorem tracePower_eq_sum {D : Density} (x : Position) (a : ℝ) :
    (D.power a x).trace.re = ∑ i, (D.positive x).isHermitian.eigenvalues i ^ a := by
  rw [Density.power, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal, Fin.sum_univ_two]

theorem tracePower_nonneg (D : Density) (x : Position) (a : ℝ) : 0 ≤ (D.power a x).trace.re := by
  rw [tracePower_eq_sum]
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg ((D.positive x).eigenvalues_nonneg i) _

theorem tracePower_le_charge (D : Density) (x : Position) {a : ℝ} (ha : 1 ≤ a) :
    (D.power a x).trace.re ≤ D.charge x ^ a := by
  rw [tracePower_eq_sum, Fin.sum_univ_two, Density.charge, (D.positive x).1.trace_eq_sum_eigenvalues,
    Fin.sum_univ_two, Complex.add_re]
  exact Real.add_rpow_le_rpow_add ((D.positive x).eigenvalues_nonneg _) ((D.positive x).eigenvalues_nonneg _) ha

/-- The lower energy estimate before passing from the mixed-state spectrum
through the constrained infimum. `ltCoeff` includes the spin degeneracy. -/
structure LowerStateLaws (ltCoeff loCoeff : ℝ) : Prop where
  indirect : ∀ D : Density, ∀ Γ : MixedState, feasible D.matrix Γ →
    hartree D.charge - loCoeff * chargeMoment D (4/3) ≤ Γ.interaction
  lieb_thirring : ∀ D : Density, ∀ Γ : MixedState, feasible D.matrix Γ →
    ltCoeff * chargeMoment D (5/3) ≤ Γ.kinetic
  hoffmann_ostenhof : ∀ D : Density, ∀ S : MatrixGradient, SqrtRegular D S →
    ∀ Γ : MixedState, feasible D.matrix Γ → sqrtKinetic S / 2 ≤ Γ.kinetic

theorem lower_energy {ltCoeff loCoeff : ℝ} (H : LowerStateLaws ltCoeff loCoeff)
    {D : Density} {S : MatrixGradient} (hD : SqrtRegular D S) (rep : ∃ Γ, feasible D.matrix Γ) :
    max (ltCoeff * chargeMoment D (5/3)) (sqrtKinetic S / 2) - loCoeff * chargeMoment D (4/3) ≤
      energy D.matrix := by
  unfold energy
  apply (le_sub_iff_add_le).2 (le_levyLieb rep ?_)
  intro Γ hΓ
  have hk := max_le (H.lieb_thirring D Γ hΓ) (H.hoffmann_ostenhof D S hD Γ hΓ)
  have hw := H.indirect D Γ hΓ
  change _ + hartree D.charge ≤ _
  linarith

end TSGA.ManyBody
