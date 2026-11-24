import TSGA.LevyLieb
import TSGA.SSWGas
import Mathlib.Logic.Equiv.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Mixing grand-canonical states at fixed charge

At equal charge the Hartree energy is common to both states. Convexity of
the Levy–Lieb energy then passes to each finite spiral and its gas limit.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Filter SSW
open scoped Topology ComplexOrder

private def interleave {α : Type*} (f g : ℕ → α) (n : ℕ) : α :=
  (Equiv.natSumNatEquivNat.symm n).elim f g

private theorem interleave_sum {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    {f g : ℕ → E} {a b : E} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (interleave f g) (a+b) := by
  apply Equiv.natSumNatEquivNat.hasSum_iff.mp
  simpa only [interleave, Function.comp_def, Equiv.symm_apply_apply] using
    (HasSum.sum (f := Sum.elim f g) hf hg)

private def mixPart (Γ Λ : MixedState) := interleave Γ.component Λ.component
private def mixWeight (Γ Λ : MixedState) (a b : ℝ) := interleave (fun i => a * Γ.weight i) (fun i => b * Λ.weight i)

private theorem mix_observable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ Λ : MixedState) (a b : ℝ) (f : PureState → E) {u v : E}
    (hΓ : HasSum (fun i => Γ.weight i • f (Γ.component i)) u)
    (hΛ : HasSum (fun i => Λ.weight i • f (Λ.component i)) v) :
    HasSum (fun i => mixWeight Γ Λ a b i • f (mixPart Γ Λ i)) (a • u + b • v) := by
  have h := interleave_sum (hΓ.const_smul a) (hΛ.const_smul b)
  apply h.congr_fun
  intro k
  obtain ⟨i, rfl⟩ := Equiv.natSumNatEquivNat.surjective k
  cases i <;> simp [mixWeight, mixPart, interleave, mul_smul]

/-- The convex mixture is a countable state without orthogonality requirements
between the two input ensembles. -/
def MixedState.mix (Γ Λ : MixedState) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : MixedState where
  component := mixPart Γ Λ
  weight := mixWeight Γ Λ a b
  weight_nonneg k := by
    unfold mixWeight interleave
    cases Equiv.natSumNatEquivNat.symm k with
    | inl i => exact mul_nonneg ha (Γ.weight_nonneg i)
    | inr i => exact mul_nonneg hb (Λ.weight_nonneg i)
  normalized := by simpa only [mixWeight, hab, mul_one] using interleave_sum (Γ.normalized.mul_left a) (Λ.normalized.mul_left b)
  particles_summable := (mix_observable Γ Λ a b (fun s => (s.particles : ℝ)) Γ.particles_summable.hasSum Λ.particles_summable.hasSum).summable
  kinetic_summable := (mix_observable Γ Λ a b PureState.kinetic Γ.kinetic_summable.hasSum Λ.kinetic_summable.hasSum).summable
  interaction_summable := (mix_observable Γ Λ a b PureState.interaction Γ.interaction_summable.hasSum Λ.interaction_summable.hasSum).summable
  density_summable := by
    filter_upwards [Γ.density_summable, Λ.density_summable] with x g l
    intro i j
    exact (mix_observable Γ Λ a b (fun s => s.matrixDensity x i j) (g i j).hasSum (l i j).hasSum).summable

/-- A summable pure-state observable is affine under mixing. This also
applies to each component of the particle and spin currents. -/
theorem MixedState.mix_expectation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ Λ : MixedState) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (F : PureState → E) {u v : E} (hΓ : HasSum (fun i => Γ.weight i • F (Γ.component i)) u)
    (hΛ : HasSum (fun i => Λ.weight i • F (Λ.component i)) v) :
    let t := Γ.mix Λ a b ha hb hab
    HasSum (fun i => t.weight i • F (t.component i)) (a • u + b • v) :=
  mix_observable Γ Λ a b F hΓ hΛ

theorem MixedState.mix_laws (Γ Λ : MixedState) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    let s := Γ.mix Λ a b ha hb hab
    s.kinetic = a*Γ.kinetic + b*Λ.kinetic ∧ s.interaction = a*Γ.interaction + b*Λ.interaction ∧
    s.matrixDensity =ᵐ[volume] fun x => a • Γ.matrixDensity x + b • Λ.matrixDensity x := by
  refine ⟨(mix_observable Γ Λ a b PureState.kinetic Γ.kinetic_summable.hasSum Λ.kinetic_summable.hasSum).tsum_eq,
    (mix_observable Γ Λ a b PureState.interaction Γ.interaction_summable.hasSum Λ.interaction_summable.hasSum).tsum_eq, ?_⟩
  filter_upwards [Γ.density_summable, Λ.density_summable] with x g l
  ext i j
  exact (mix_observable Γ Λ a b (fun s => s.matrixDensity x i j) (g i j).hasSum (l i j).hasSum).tsum_eq

private theorem near_minimum {M : Position → SpinMatrix} (h : ∃ Γ, feasible M Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ, feasible M Γ ∧ Γ.kinetic + Γ.interaction < levyLieb M + ε := by
  obtain ⟨g, hg⟩ := h
  let s : Set ℝ := {v | ∃ Γ : MixedState, feasible M Γ ∧ v = Γ.kinetic + Γ.interaction}
  obtain ⟨v, ⟨Γ, hΓ, rfl⟩, hv⟩ := exists_lt_of_csInf_lt (s := s) ⟨_, g, hg, rfl⟩
    (show sInf s < levyLieb M + ε from lt_add_of_pos_right _ hε)
  exact ⟨Γ, hΓ, hv⟩

theorem levyLieb_convex {M N : Position → SpinMatrix} (hM : ∃ Γ, feasible M Γ) (hN : ∃ Γ, feasible N Γ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    levyLieb (fun x => a • M x + b • N x) ≤ a * levyLieb M + b * levyLieb N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Γ, hΓ, hg⟩ := near_minimum hM hε
  obtain ⟨Λ, hΛ, hl⟩ := near_minimum hN hε
  obtain ⟨hk, hw, hρ⟩ := Γ.mix_laws Λ ha hb hab
  have hmix : feasible (fun x => a • M x + b • N x) (Γ.mix Λ a b ha hb hab) := by
    apply hρ.trans
    filter_upwards [hΓ, hΛ] with x hx hy
    rw [hx, hy]
  have h := levyLieb_le hmix
  rw [hk, hw] at h
  linarith only [h, mul_le_mul_of_nonneg_left hg.le ha, mul_le_mul_of_nonneg_left hl.le hb,
    congrArg (fun t => t * ε) hab]

/-- The direct term cancels at a common charge density. -/
theorem energy_convex_fixed_charge {M N : Position → SpinMatrix} (hM : ∃ Γ, feasible M Γ)
    (hN : ∃ Γ, feasible N Γ) (hr : (fun x => (M x).trace.re) =ᵐ[volume] fun x => (N x).trace.re)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    energy (fun x => a • M x + b • N x) ≤ a * energy M + b * energy N := by
  have hx : (fun x => (a • M x + b • N x).trace.re) =ᵐ[volume] fun x => (N x).trace.re := by
    filter_upwards [hr] with x h
    simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, h, ← add_mul, hab, one_mul]
  have hl := levyLieb_convex hM hN ha hb hab
  unfold energy
  rw [hartree_congr hx, hartree_congr hr]
  linarith only [hl, congrArg (fun t => t * hartree (fun x => (N x).trace.re)) hab]

end TSGA.ManyBody
