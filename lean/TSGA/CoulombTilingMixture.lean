import TSGA.CoulombDilationMeasure
import TSGA.IslandHartree
import TSGA.StateMixing
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Gluing disjoint Coulomb trials and averaging their densities

At a fixed position of a tiling the only operator input is the tensor
product of fermionic states on disjoint one-particle spaces. The
constrained searches can be minimized separately. Barycentric mixing over
a probability space follows by integrating the closed convex epigraph
of the grand-canonical universal functional.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory Set

abbrev SpinL1 := Fin 2 → Fin 2 → Lp ℂ 1 (volume : Measure Position)

def spinL1Field (v : SpinL1) (x : Position) : SpinMatrix := fun i j => v i j x

theorem levyLieb_congr_matrix {D N : Position → SpinMatrix} (h : D =ᵐ[volume] N) :
    levyLieb D = levyLieb N := by
  apply congrArg sInf
  ext e
  exact ⟨fun ⟨Γ,hΓ,hE⟩ => ⟨Γ,hΓ.trans h,hE⟩, fun ⟨Γ,hΓ,hE⟩ => ⟨Γ,hΓ.trans h.symm,hE⟩⟩

theorem extended_le_real_iff (v : SpinL1) (r : ℝ) :
    extendedL1ConstrainedSearch v ≤ ↑r ↔
      (∃ Γ, feasible (spinL1Field v) Γ) ∧ levyLieb (spinL1Field v) ≤ r := by
  classical
  change (if ∃ Γ, feasible (spinL1Field v) Γ then (↑(levyLieb (spinL1Field v)) : WithTop ℝ) else ⊤) ≤ ↑r ↔ _
  split_ifs with h <;> simp [h]

private theorem spinL1Field_mix (v w : SpinL1) (a b : ℝ) :
    spinL1Field (a • v + b • w) =ᵐ[volume] fun x => a • spinL1Field v x + b • spinL1Field w x := by
  have entry (i j : Fin 2) :
      (fun x => spinL1Field (a • v + b • w) x i j) =ᵐ[volume]
        (fun x => (a • spinL1Field v x + b • spinL1Field w x) i j) :=
    (Lp.coeFn_add (a • v i j) (b • w i j)).trans ((Lp.coeFn_smul a (v i j)).add (Lp.coeFn_smul b (w i j)))
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (entry i)] with x hx
  exact funext fun i => funext (hx i)

/-- Jensen's inequality with an integrable upper bound on the finite energies.
No measurable choice of near-minimizing Fock states is required. -/
theorem levyLieb_barycenter {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (v : Ω → SpinL1) (g : Ω → ℝ) (hv : Integrable v μ) (hg : Integrable g μ)
    (h : ∀ᵐ ω ∂μ, (∃ Γ, feasible (spinL1Field (v ω)) Γ) ∧ levyLieb (spinL1Field (v ω)) ≤ g ω) :
    ∃ Γ, feasible (spinL1Field (∫ ω, v ω ∂μ)) Γ ∧
      levyLieb (spinL1Field (∫ ω, v ω ∂μ)) ≤ ∫ ω, g ω ∂μ := by
  let S : Set (SpinL1 × ℝ) := {z | extendedL1ConstrainedSearch z.1 ≤ ↑z.2}
  have hclosed : IsClosed S := hlsc.isClosed_epigraph.preimage
    (continuous_fst.prodMk (WithTop.continuous_coe.comp continuous_snd))
  have hconvex : Convex ℝ S := by
    intro z hz w hw a b ha hb hab
    obtain ⟨⟨Γ,hΓ⟩,hz⟩ := (extended_le_real_iff z.1 z.2).1 hz
    obtain ⟨⟨Λ,hΛ⟩,hw⟩ := (extended_le_real_iff w.1 w.2).1 hw
    apply (extended_le_real_iff _ _).2
    have he := spinL1Field_mix z.1 w.1 a b
    constructor
    · refine ⟨Γ.mix Λ a b ha hb hab, ((Γ.mix_laws Λ ha hb hab).2.2.trans ?_).trans he.symm⟩
      filter_upwards [hΓ,hΛ] with x hx hy
      rw [hx,hy]
    · change levyLieb (spinL1Field (a • z.1 + b • w.1)) ≤ a*z.2 + b*w.2
      rw [levyLieb_congr_matrix he]
      exact (levyLieb_convex (M := spinL1Field z.1) (N := spinL1Field w.1) ⟨Γ,hΓ⟩ ⟨Λ,hΛ⟩ ha hb hab).trans
        (add_le_add (mul_le_mul_of_nonneg_left hz ha) (mul_le_mul_of_nonneg_left hw hb))
  have hint := hconvex.integral_mem (f := fun ω => (v ω, g ω)) hclosed
    (h.mono fun ω hω => (extended_le_real_iff (v ω) (g ω)).2 hω) (hv.prodMk hg)
  rw [integral_pair hv hg] at hint
  obtain ⟨⟨Γ,hΓ⟩,hg'⟩ := (extended_le_real_iff _ _).1 hint
  exact ⟨Γ,hΓ,hg'⟩

/-- The off-diagonal part of the direct Coulomb interaction between finitely
many independent blocks. The half compensates for the two pair orders. -/
def offDiagonalDirect {n : ℕ} (r : Fin n → Position → ℝ) : ℝ :=
  (∑ i, ∑ j, if i = j then 0 else crossDirect (r i) (r j))/2

theorem hartree_finite_blocks {n : ℕ} (r : Fin n → Position → ℝ)
    (hint : ∀ i j, Integrable (directKernel (r i) (r j)) pairVolume) :
    hartree (∑ i, r i) = (∑ i, hartree (r i)) + offDiagonalDirect r := by
  classical
  have hk : directKernel (∑ i, r i) (∑ i, r i) = fun z => ∑ i, ∑ j, directKernel (r i) (r j) z := by
    ext z
    simp [directKernel, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_comm
  have hsum := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hint i j
  rw [hartree_eq_pair _ (hk ▸ hsum),hk]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hint i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j),hartree_eq_pair _ (hint _ _)]
  let J := fun i j => crossDirect (r i) (r j)
  have hs (i : Fin n) : (∑ j, J i j) = J i i + ∑ j, if i = j then 0 else J i j := by
    have hsplit (j : Fin n) : J i j = (if i = j then J i i else 0) + (if i = j then 0 else J i j) := by
      split_ifs <;> simp_all
    calc
      ∑ j, J i j = ∑ j, ((if i = j then J i i else 0) + (if i = j then 0 else J i j)) :=
        Finset.sum_congr rfl (fun j _ => hsplit j)
      _ = _ := by simp [Finset.sum_add_distrib]
  change (∑ i, ∑ j, J i j)/2 = (∑ i, J i i/2) + (∑ i, ∑ j, if i = j then 0 else J i j)/2
  simp_rw [hs]
  rw [Finset.sum_add_distrib,← Finset.sum_div]
  ring

/-- Standard Fock tensorization on mutually disjoint supports. This is stated
for arbitrary localized mixed states and contains no variational, geometric,
or finite-size inequality. -/
def DisjointFockTensorization : Prop :=
  ∀ {n : ℕ} (U : Fin n → Position → SpinMatrix) (Γ : Fin n → MixedState),
    (∀ i, feasible (U i) (Γ i)) → (Pairwise fun i j => Disjoint (Function.support (U i)) (Function.support (U j))) →
    ∃ G : MixedState, feasible (∑ i, U i) G ∧ G.kinetic = ∑ i, (Γ i).kinetic ∧
      G.interaction = (∑ i, (Γ i).interaction) + offDiagonalDirect (fun i x => ((U i) x).trace.re)

private theorem finite_sum_charge {n : ℕ} (U : Fin n → Position → SpinMatrix) :
    (fun x => ((∑ i, U i) x).trace.re) = ∑ i, fun x => (U i x).trace.re := by
  funext x
  simp [Finset.sum_apply]

/-- The finite sum may include the skeleton as one block and may be empty. -/
theorem coulomb_energy_disjoint_blocks (tensor : DisjointFockTensorization) {n : ℕ}
    (U : Fin n → Position → SpinMatrix) (hrep : ∀ i, ∃ Γ, feasible (U i) Γ)
    (hdis : Pairwise fun i j => Disjoint (Function.support (U i)) (Function.support (U j)))
    (hint : ∀ i j, Integrable (directKernel (fun x => (U i x).trace.re) (fun x => (U j x).trace.re)) pairVolume) :
    (∃ G, feasible (∑ i, U i) G) ∧ energy (∑ i, U i) ≤ ∑ i, energy (U i) := by
  classical
  choose Γ hΓ using hrep
  obtain ⟨G,hG,_,_⟩ := tensor U Γ hΓ hdis
  refine ⟨⟨G,hG⟩,le_of_forall_pos_le_add fun ε hε => ?_⟩
  let d := ε / ((n:ℝ)+1)
  have hd : 0 < d := div_pos hε (by positivity)
  have near (i : Fin n) : ∃ Λ, feasible (U i) Λ ∧
      Λ.kinetic + Λ.interaction ≤ levyLieb (U i) + d := by
    obtain ⟨e, ⟨Λ,hΛ,rfl⟩,he⟩ := exists_lt_of_csInf_lt
      (s := {e | ∃ Λ : MixedState, feasible (U i) Λ ∧ e = Λ.kinetic + Λ.interaction})
      ⟨_,Γ i,hΓ i,rfl⟩ (show levyLieb (U i) < levyLieb (U i) + d from lt_add_of_pos_right _ hd)
    exact ⟨Λ,hΛ,he.le⟩
  choose Λ hΛ hE using near
  obtain ⟨G',hg,hk,hw⟩ := tensor U Λ hΛ hdis
  have hl := levyLieb_le hg
  rw [hk,hw] at hl
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hE i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at ht
  have hc : (n:ℝ)*d ≤ ε := by
    have he : ((n:ℝ)+1)*d = ε := by dsimp [d]; field_simp
    linarith
  simp only [energy, finite_sum_charge, hartree_finite_blocks _ hint, Finset.sum_sub_distrib]
  linarith

/-- The upper Coulomb bound before estimating the skeleton fluctuation.
The finite set of contributing blocks may depend on the parameter. -/
theorem coulomb_average_disjoint_blocks {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (tensor : DisjointFockTensorization)
    (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (n : Ω → ℕ) (U : (ω : Ω) → Fin (n ω) → Position → SpinMatrix)
    (v : Ω → SpinL1) (hv : Integrable v μ) (D : Position → SpinMatrix)
    (hbar : spinL1Field (∫ ω, v ω ∂μ) =ᵐ[volume] D)
    (hblocks : ∀ᵐ ω ∂μ, spinL1Field (v ω) =ᵐ[volume] ∑ i, U ω i)
    (hrep : ∀ᵐ ω ∂μ, ∀ i, ∃ Γ, feasible (U ω i) Γ)
    (hdis : ∀ᵐ ω ∂μ, Pairwise fun i j => Disjoint (Function.support (U ω i)) (Function.support (U ω j)))
    (hint : ∀ᵐ ω ∂μ, ∀ i j, Integrable (directKernel (fun x => (U ω i x).trace.re)
      (fun x => (U ω j x).trace.re)) pairVolume)
    (he : Integrable (fun ω => ∑ i, energy (U ω i)) μ) :
    let R := fun ω x => ((∑ i, U ω i) x).trace.re
    let m := fun x => (D x).trace.re
    (∀ᵐ x, Integrable (fun ω => R ω x) μ ∧ (∫ ω, R ω x ∂μ) = m x) →
    JointDirectIntegrable μ R → Integrable (directKernel m m) pairVolume →
    JointDirectIntegrable μ (fun ω x => R ω x - m x) →
    energy D ≤ (∫ ω, ∑ i, energy (U ω i) ∂μ) +
      ∫ ω, hartree (fun x => R ω x-m x) ∂μ := by
  intro R m hmean hr hm hc
  have hupper : ∀ᵐ ω ∂μ, (∃ Γ, feasible (spinL1Field (v ω)) Γ) ∧
      levyLieb (spinL1Field (v ω)) ≤ (∑ i, energy (U ω i)) + hartree (R ω) := by
    filter_upwards [hblocks,hrep,hdis,hint] with ω hρ hΓ hd hi
    obtain ⟨⟨Γ,hΓ'⟩,hs⟩ := coulomb_energy_disjoint_blocks tensor (U ω) hΓ hd hi
    refine ⟨⟨Γ,hΓ'.trans hρ.symm⟩, ?_⟩
    rw [levyLieb_congr_matrix hρ]
    exact sub_le_iff_le_add.mp hs
  have hhr := integrable_hartree_of_joint hr
  obtain ⟨_,_,hll⟩ := levyLieb_barycenter hlsc v _ hv (he.add hhr) hupper
  simp only [Pi.add_apply] at hll
  rw [integral_add he hhr,expect_hartree_centered hmean hr hm hc] at hll
  rw [levyLieb_congr_matrix hbar] at hll
  change levyLieb D - hartree m ≤ _
  linarith

/-- A pointwise partition of unity computes the L¹ barycenter used by Jensen.
Set integrals of individual matrix entries are continuous linear functionals. -/
theorem spinL1_barycenter_of_pointwise {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (v : Ω → SpinL1) (hv : Integrable v μ)
    (u : Ω → Position → SpinMatrix) (hu : ∀ᵐ ω ∂μ, spinL1Field (v ω) =ᵐ[volume] u ω)
    (D : Position → SpinMatrix) (hD : ∀ i j, Integrable (fun x => D x i j))
    (hj : ∀ i j, Integrable (fun z : Ω × Position => u z.1 z.2 i j) (μ.prod volume))
    (hmean : ∀ᵐ x, ∀ i j, (∫ ω, u ω x i j ∂μ) = D x i j) :
    spinL1Field (∫ ω, v ω ∂μ) =ᵐ[volume] D := by
  have entry (i j : Fin 2) : (fun x => spinL1Field (∫ ω, v ω ∂μ) x i j) =ᵐ[volume]
      fun x => D x i j := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _) (hD i j)
    intro s hs _
    let row : SpinL1 →L[ℝ] (Fin 2 → Lp ℂ 1 (volume : Measure Position)) := ContinuousLinearMap.proj i
    let col : (Fin 2 → Lp ℂ 1 (volume : Measure Position)) →L[ℝ] Lp ℂ 1 (volume : Measure Position) :=
      ContinuousLinearMap.proj j
    let proj := col.comp row
    let test : SpinL1 →L[ℝ] ℂ := L1.integralCLM.comp ((LpToLpRestrictCLM Position ℂ ℝ volume 1 s).comp proj)
    have eval (w : SpinL1) : test w = ∫ x in s, spinL1Field w x i j := by
      change L1.integralCLM (LpToLpRestrictCLM Position ℂ ℝ volume 1 s (w i j)) = _
      rw [← L1.integral_eq, L1.integral_eq_integral]
      exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s (w i j))
    have hrs : Integrable (fun z : Ω × Position => u z.1 z.2 i j) (μ.prod (volume.restrict s)) := by
      rw [← Measure.restrict_univ (μ := μ), Measure.prod_restrict]
      exact (hj i j).restrict
    calc
      _ = test (∫ ω, v ω ∂μ) := (eval _).symm
      _ = ∫ ω, test (v ω) ∂μ := (test.integral_comp_comm hv).symm
      _ = ∫ ω, (∫ x in s, u ω x i j) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hu] with ω hω
        rw [eval]
        exact integral_congr_ae ((ae_restrict_of_ae hω).mono fun x hx => congrArg (fun m : SpinMatrix => m i j) hx)
      _ = ∫ x in s, ∫ ω, u ω x i j ∂μ := integral_integral_swap hrs
      _ = _ := integral_congr_ae ((ae_restrict_of_ae hmean).mono fun _ h => h i j)
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (entry i)] with x hx
  exact funext fun i => funext (hx i)

end TSGA.ManyBody
