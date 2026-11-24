import TSGA.IslandChargeDomain
import TSGA.CoulombTilingMixture

/-! # Disjoint exterior and interior Fock states in the Poisson construction -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {v : ℝ}

/-- The general measurable-selection and barycenter theorem for normal Fock states.
Its arguments are a jointly integrable density and an integrable value of the
positive kinetic-plus-interaction observable. Its conclusion is the spectral
ensemble of the averaged state. -/
def FockBarycenterRealization (μ : Measure Ω) : Prop :=
  ∀ (U : Ω → Position → SpinMatrix) (e : Ω → ℝ),
    (∀ i j, Integrable (fun z : Ω × Position => U z.1 z.2 i j) (μ.prod volume)) →
    Integrable e μ → (∀ᵐ ω ∂μ, ∃ Γ : MixedState, feasible (U ω) Γ ∧ Γ.kinetic+Γ.interaction = e ω) →
    ∃ Γ : MixedState, feasible (fun x i j => ∫ ω, U ω x i j ∂μ) Γ ∧ Γ.kinetic+Γ.interaction = ∫ ω, e ω ∂μ

private theorem cross_comm (f g : Position → ℝ) : crossDirect g f = crossDirect f g := by
  have h (z : PairSpace) : directKernel g f z = directKernel f g z.swap := by
    simp [directKernel,norm_sub_rev z.2 z.1,mul_comm]
  unfold crossDirect
  simp_rw [h]
  exact integral_prod_swap _

private theorem disjoint_pair (tensor : DisjointFockTensorization) (U V : Position → SpinMatrix)
    (Γ Λ : MixedState) (hΓ : feasible U Γ) (hΛ : feasible V Λ)
    (hd : Disjoint (Function.support U) (Function.support V)) :
    ∃ G : MixedState, feasible (U+V) G ∧ G.kinetic+G.interaction =
      Γ.kinetic+Γ.interaction+(Λ.kinetic+Λ.interaction)+
        crossDirect (fun x => (U x).trace.re) (fun x => (V x).trace.re) := by
  classical
  let blocks : Fin 2 → Position → SpinMatrix := ![U,V]
  let states : Fin 2 → MixedState := ![Γ,Λ]
  have hf (i : Fin 2) : feasible (blocks i) (states i) := by fin_cases i <;> assumption
  have hs : Pairwise fun i j => Disjoint (Function.support (blocks i)) (Function.support (blocks j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact hd | exact hd.symm
  obtain ⟨G,hG,hk,hi⟩ := tensor blocks states hf hs
  refine ⟨G,by simpa [Fin.sum_univ_two,blocks] using hG,?_⟩
  rw [hk,hi]
  simp [Fin.sum_univ_two,states,offDiagonalDirect,blocks,cross_comm (fun x => (U x).trace.re) (fun x => (V x).trace.re)]
  ring

namespace IslandMasks
variable (m : IslandMasks μ v) (B D : Density)

omit [IsProbabilityMeasure μ] in
theorem trace_outer (ω : Ω) (x : Position) : (m.outsideMatrix B ω x).trace.re = m.outerCharge B ω x := by
  simp [outsideMatrix,outerCharge,Density.charge,Matrix.trace_smul,Complex.real_smul]

omit [IsProbabilityMeasure μ] in
theorem trace_inner (ω : Ω) (x : Position) : (m.insideMatrix B D ω x).trace.re = m.innerCharge B D ω x := by
  simp [insideMatrix,innerCharge,Density.charge,Matrix.trace_smul,Complex.real_smul]

theorem mean_matrix (x : Position) (i j : Fin 2) :
    (∫ ω, (m.outsideMatrix B ω + m.insideMatrix B D ω) x i j ∂μ) = (B.matrix+D.matrix) x i j := by
  let a := B.matrix x i j
  let b := D.matrix x i j
  have A := (m.outside_mean x).1.smul_const a
  have C := ((m.first_mean x).1.const_mul m.c₁).smul_const a
  have E := ((m.core_mean x).1.const_mul m.c₂).smul_const b
  change (∫ ω, m.outside ω x • a + ((m.c₁*m.first ω x) • a + (m.c₂*m.core ω x) • b) ∂μ) = a+b
  erw [integral_add A (C.add E),integral_add C E]
  simp only [integral_smul_const,integral_const_mul,(m.outside_mean x).2,(m.first_mean x).2,
    (m.core_mean x).2,m.normalized.2,one_smul]
  rw [← add_assoc,← add_smul,m.normalized.1,one_smul]

private theorem single_matrix_integrable (a : Ω → Position → ℝ) (f : Position → ℂ)
    (ha : Measurable (Function.uncurry a)) (C : ℝ) (hC : ∀ ω x, |a ω x| ≤ C) (hf : Integrable f) :
    Integrable (fun z : Ω × Position => a z.1 z.2 • f z.2) (μ.prod volume) := by
  apply ((hf.norm.comp_snd μ).const_mul C).mono' (ha.aestronglyMeasurable.smul (hf.comp_snd μ).aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖a z.1 z.2 • f z.2‖ ≤ C*‖f z.2‖
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC z.1 z.2) (norm_nonneg _)

theorem inner_matrix_integrable (M : m.MeasurableFields) (i j : Fin 2)
    (hb : Integrable (fun x => B.matrix x i j)) (hd : Integrable (fun x => D.matrix x i j)) :
    Integrable (fun z : Ω × Position => m.insideMatrix B D z.1 z.2 i j) (μ.prod volume) := by
  have one (a : ℝ) (h : a ∈ Set.Icc 0 1) : |a| ≤ 1 := (abs_of_nonneg h.1).le.trans h.2
  have mult (a c : ℝ) (h : a ∈ Set.Icc 0 1) : |c*a| ≤ |c| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (one a h)
  exact (single_matrix_integrable _ _ (measurable_const.mul M.first) |m.c₁| (fun ω x => mult _ _ (m.first_range ω x)) hb).add
    (single_matrix_integrable _ _ (measurable_const.mul M.core) |m.c₂| (fun ω x => mult _ _ (m.core_range ω x)) hd)

private theorem matrix_integrable (M : m.MeasurableFields) (i j : Fin 2)
    (hb : Integrable (fun x => B.matrix x i j)) (hd : Integrable (fun x => D.matrix x i j)) :
    Integrable (fun z : Ω × Position => (m.outsideMatrix B z.1+m.insideMatrix B D z.1) z.2 i j) (μ.prod volume) := by
  exact (single_matrix_integrable _ _ M.outside 1
    (fun ω x => (abs_of_nonneg (m.outside_range ω x).1).le.trans (m.outside_range ω x).2) hb).add
    (m.inner_matrix_integrable B D M i j hb hd)

/-- Assemble both concrete states into the trial of Lemma C.1. All Coulomb
form domains, the spin-density constraint and the cross energy are derived
from the same three masks. -/
def fockTrial (tensor : DisjointFockTensorization) (mix : FockBarycenterRealization μ)
    (M : m.MeasurableFields) (H : IslandChargeDomain B D)
    (hb : ∀ i j, Integrable (fun x => B.matrix x i j)) (hd : ∀ i j, Integrable (fun x => D.matrix x i j))
    (out ins : Ω → MixedState) (h₁ : ∀ᵐ ω ∂μ, feasible (m.outsideMatrix B ω) (out ω))
    (h₂ : ∀ᵐ ω ∂μ, feasible (m.insideMatrix B D ω) (ins ω))
    (ho : Integrable (fun ω => (out ω).kinetic+(out ω).interaction) μ)
    (hi : Integrable (fun ω => (ins ω).kinetic+(ins ω).interaction) μ) :
    IslandTrial μ (B.matrix+D.matrix) := by
  let U := fun ω => m.outsideMatrix B ω + m.insideMatrix B D ω
  let e := fun ω => (out ω).kinetic+(out ω).interaction+((ins ω).kinetic+(ins ω).interaction)+
    crossDirect (m.outerCharge B ω) (m.innerCharge B D ω)
  have ofm := (m.controls M H).1
  have ifm := (m.controls M H).2.1
  have sm := (m.controls M H).2.2.1
  have hp (x) : 0 ≤ (B.charge+D.charge) x := add_nonneg (B.charge_nonneg x) (D.charge_nonneg x)
  have cross := ofm.joint (μ := μ) ifm hp H.direct
  have he : Integrable e μ := (ho.add hi).add cross.integral_prod_left
  have product : ∀ᵐ ω ∂μ, ∃ G : MixedState, feasible (U ω) G ∧ G.kinetic+G.interaction = e ω := by
    filter_upwards [h₁,h₂] with ω a b
    simpa only [U,e,m.trace_outer,m.trace_inner] using disjoint_pair tensor _ _ _ _ a b (m.disjoint B D ω)
  have bar := mix U e (fun i j => m.matrix_integrable B D M i j (hb i j) (hd i j)) he product
  let Γ := Classical.choose bar
  have hΓ := Classical.choose_spec bar
  have sum_trace (x : Position) : ((B.matrix+D.matrix) x).trace.re = B.charge x + D.charge x := by
    simp [Density.charge]
  refine ⟨Γ,?_,out,ins,m.outerCharge B,m.innerCharge B D,?_,?_,?_,ofm.joint ofm hp H.direct,
    ifm.joint ifm hp H.direct,cross.prod_right_ae,(ofm.add ifm).joint (ofm.add ifm) hp H.direct,?_,?_,ho,hi,hΓ.2⟩
  · apply hΓ.1.trans
    exact ae_of_all _ fun x => funext fun i => funext fun j => m.mean_matrix B D x i j
  · filter_upwards [h₁] with ω a
    exact a.mono fun x h => (m.trace_outer B ω x).symm.trans (congrArg (fun A : SpinMatrix => A.trace.re) h.symm)
  · filter_upwards [h₂] with ω a
    exact a.mono fun x h => (m.trace_inner B D ω x).symm.trans (congrArg (fun A : SpinMatrix => A.trace.re) h.symm)
  · apply ae_of_all
    intro x
    rw [sum_trace]
    exact m.mean_scalar x _ _
  · simp only [sum_trace]
    exact H.direct
  · simp only [sum_trace]
    exact ((ofm.add ifm).sub sm).joint (μ := μ) ((ofm.add ifm).sub sm) hp H.direct

end IslandMasks
end TSGA.ManyBody
