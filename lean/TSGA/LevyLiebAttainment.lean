import TSGA.LayerGradient
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Order.IsLUB

/-! # Attainment of the grand-canonical Levy–Lieb infimum

At fixed integrable total charge, the Fock-space compactness argument of
Lewin–Lieb–Seiringer gives a subsequence with trace-norm convergence of its
one-particle marginals and lower semicontinuity of the many-body energy.
Only convergence in measure of the four spin-density entries is needed here.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Filter
open scoped Topology

/-- The consequences of fixed-charge compactness used in Theorem 2.2.
The sequence is only constrained by its scalar charge and an energy bound.
The matrix entries can vary along the sequence. -/
def FixedChargeCompactness : Prop :=
  ∀ (ρ : Position → ℝ), Integrable ρ → ∀ u : ℕ → MixedState,
    (∀ n, (fun x => ((u n).matrixDensity x).trace.re) =ᵐ[volume] ρ) →
    (∃ C : ℝ, ∀ n, (u n).kinetic + (u n).interaction ≤ C) →
    ∃ (Γ : MixedState) (s : ℕ → ℕ), StrictMono s ∧
      (∀ i j, TendstoInMeasure volume (fun n x => (u (s n)).matrixDensity x i j)
        atTop (fun x => Γ.matrixDensity x i j)) ∧
      Γ.kinetic + Γ.interaction ≤ liminf (fun n => (u (s n)).kinetic + (u (s n)).interaction) atTop

/-- Entrywise convergence in measure preserves the complete spin-density
constraint, including its off-diagonal entries. -/
theorem feasible_of_tendstoInMeasure {M : Position → SpinMatrix} {u : ℕ → MixedState}
    {Γ : MixedState} (hu : ∀ n, feasible M (u n))
    (h : ∀ i j, TendstoInMeasure volume (fun n x => (u n).matrixDensity x i j)
      atTop (fun x => Γ.matrixDensity x i j)) : feasible M Γ := by
  have entries (i j : Fin 2) : (fun x => Γ.matrixDensity x i j) =ᵐ[volume] fun x => M x i j := by
    apply tendstoInMeasure_ae_unique (h i j)
    apply TendstoInMeasure.congr_left (f := fun (_ : ℕ) x => M x i j)
      (fun n => (hu n).symm.mono fun x hx => congrArg (fun A : SpinMatrix => A i j) hx)
    intro ε hε
    simp [not_le_of_gt hε]
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (entries i)] with x hx
  exact Matrix.ext fun i j => hx i j

/-- The direct method on the feasible set. Nonnegativity gives a decreasing
minimizing sequence. Compactness preserves its density and bounds the energy
of the limit by the constrained infimum. -/
theorem levyLieb_attained_of_feasible (compact : FixedChargeCompactness)
    {M : Position → SpinMatrix} (charge : Integrable (fun x => (M x).trace.re))
    (rep : ∃ Γ, feasible M Γ) : ∃ Γ, feasible M Γ ∧ Γ.kinetic + Γ.interaction = levyLieb M := by
  let E : Set ℝ := {e | ∃ Γ : MixedState, feasible M Γ ∧ e = Γ.kinetic + Γ.interaction}
  obtain ⟨trial, htrial⟩ := rep
  have lower : BddBelow E := ⟨0, fun _ ⟨Γ, _, he⟩ =>
    he ▸ add_nonneg Γ.kinetic_nonneg Γ.interaction_nonneg⟩
  obtain ⟨v, mono, limit, values⟩ := exists_seq_tendsto_sInf
    (show E.Nonempty from ⟨_, trial, htrial, rfl⟩) lower
  choose u hu hval using values
  have fixed (n : ℕ) := (hu n).mono fun x hx => congrArg (fun A : SpinMatrix => A.trace.re) hx
  obtain ⟨Γ, s, hs, entries, bound⟩ := compact _ charge u fixed
    ⟨v 0, fun n => (hval n).symm.le.trans (mono (Nat.zero_le n))⟩
  have hΓ := feasible_of_tendstoInMeasure (fun n => hu (s n)) entries
  refine ⟨Γ, hΓ, le_antisymm ?_ (levyLieb_le hΓ)⟩
  simp only [← hval] at bound
  exact bound.trans_eq (limit.comp hs.tendsto_atTop).liminf_eq

/-- Theorem 2.2 for every positive density with finite charge and H¹ square
root. The one-body trial and its quasi-free realization supply feasibility. -/
theorem levyLieb_attained {cTF κ₁ κ₂ : ℝ} (trial : LayerConstruction cTF κ₁ κ₂)
    (qf : QuasiFreeRealization) (compact : FixedChargeCompactness)
    {D : Density} {S : MatrixGradient} (regular : SqrtRegular D S) :
    ∃ Γ, feasible D.matrix Γ ∧ Γ.kinetic + Γ.interaction = levyLieb D.matrix := by
  obtain ⟨w, _, _⟩ := trial D S regular 1 zero_lt_one
  obtain ⟨Γ, hΓ, _, _⟩ := qf w.gamma
  exact levyLieb_attained_of_feasible compact regular.charge ⟨Γ, hΓ.trans w.density⟩

end TSGA.ManyBody
