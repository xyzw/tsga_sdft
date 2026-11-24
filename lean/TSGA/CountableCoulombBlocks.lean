import TSGA.CoulombTilingMixture
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Exhaustion of disjoint Fock blocks in the extended constrained search -/

noncomputable section
namespace TSGA.ManyBody

open Filter MeasureTheory Set
open scoped Topology

/-- Passage from finite tensor products to a countable disjoint union.
A finite subfamily agrees with the whole field on its occupied blocks and is
zero elsewhere. This gives domination both in entrywise L¹ and in the
two-particle integral defining the direct energy. -/
theorem coulomb_disjoint_exhaustion {ι : Type*} [Countable ι]
    (hlsc : LowerSemicontinuous extendedL1ConstrainedSearch)
    (F : Position → SpinMatrix) (U : Finset ι → Position → SpinMatrix)
    (e : Finset ι → ℝ) {limit : ℝ} (he : Tendsto e atTop (𝓝 limit))
    (hF : ∀ i j, Integrable (fun x => F x i j))
    (hU : ∀ T i j, Measurable (fun x => U T x i j))
    (hsel : ∀ T x, U T x = F x ∨ U T x = 0)
    (hcover : ∀ x, ∀ᶠ T in atTop, U T x = F x)
    (hK : Integrable (directKernel (fun x => (F x).trace.re) (fun x => (F x).trace.re)) pairVolume)
    (finite : ∀ T, (∃ Γ, feasible (U T) Γ) ∧ energy (U T) ≤ e T) :
    (∃ Γ, feasible F Γ) ∧ energy F ≤ limit := by
  classical
  let r := fun x => (F x).trace.re
  let s := fun T x => (U T x).trace.re
  have ui (T i j) : Integrable (fun x => U T x i j) :=
    (hF i j).norm.mono' (hU T i j).aestronglyMeasurable (ae_of_all _ fun x => by
      rcases hsel T x with h | h <;> simp [h])
  let v : SpinL1 := fun i j => (hF i j).toL1 _
  let w : Finset ι → SpinL1 := fun T i j => (ui T i j).toL1 _
  have vf : spinL1Field v =ᵐ[volume] F := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hF i j).coeFn_toL1] with x hx
    exact funext fun i => funext (hx i)
  have wf (T) : spinL1Field (w T) =ᵐ[volume] U T := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (ui T i j).coeFn_toL1] with x hx
    exact funext fun i => funext (hx i)
  have wlim : Tendsto w atTop (𝓝 v) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter (Finset ι)))
      (F := fun T x => dist (U T x i j) (F x i j)) (f := fun _ => (0:ℝ)) (fun x => ‖F x i j‖)
      (.of_forall fun T => (hU T i j).aestronglyMeasurable.dist (hF i j).1)
      (.of_forall fun T => ae_of_all _ fun x => by rcases hsel T x with eq | eq <;> simp [eq])
      (hF i j).norm (ae_of_all _ fun x => tendsto_const_nhds.congr'
        ((hcover x).mono fun T h => by simp [h]))
    simp only [integral_zero] at h
    apply h.congr (fun T => ?_)
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(ui T i j).coeFn_toL1,(hF i j).coeFn_toL1] with x hx hy
    exact congrArg₂ dist hx.symm hy.symm
  have sm (T) : Measurable (s T) := by
    unfold s Matrix.trace
    exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ => hU T i i)
  have km (T) : Measurable (directKernel (s T) (s T)) :=
    ((sm T).comp measurable_fst |>.mul ((sm T).comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm)
  have kdom (T) (z : PairSpace) : ‖directKernel (s T) (s T) z‖ ≤ ‖directKernel r r z‖ := by
    rcases hsel T z.1 with hx | hx <;> rcases hsel T z.2 with hy | hy <;>
      simp [directKernel,s,r,hx,hy] <;> positivity
  have ki (T) := hK.norm.mono' (km T).aestronglyMeasurable (ae_of_all _ (kdom T))
  have clim : Tendsto (fun T => hartree (s T)) atTop (𝓝 (hartree r)) := by
    simp_rw [hartree_eq_pair (s _) (ki _),hartree_eq_pair r hK]
    apply Tendsto.div_const
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖directKernel r r z‖)
      (.of_forall fun T => (km T).aestronglyMeasurable) (.of_forall fun T => ae_of_all _ (kdom T)) hK.norm
    apply ae_of_all
    intro z
    apply tendsto_const_nhds.congr'
    filter_upwards [hcover z.1,hcover z.2] with T hx hy
    simp [directKernel,s,r,hx,hy]
  let S : Set (SpinL1 × ℝ) := {z | extendedL1ConstrainedSearch z.1 ≤ ↑z.2}
  have closed : IsClosed S := hlsc.isClosed_epigraph.preimage
    (continuous_fst.prodMk (WithTop.continuous_coe.comp continuous_snd))
  have member (T) : (w T,e T + hartree (s T)) ∈ S := by
    obtain ⟨⟨Γ,hΓ⟩,hb⟩ := finite T
    apply (extended_le_real_iff _ _).2
    refine ⟨⟨Γ,hΓ.trans (wf T).symm⟩,?_⟩
    rw [levyLieb_congr_matrix (wf T)]
    exact sub_le_iff_le_add.mp hb
  have final := closed.mem_of_tendsto (wlim.prodMk_nhds (he.add clim)) (.of_forall member)
  obtain ⟨⟨Γ,hΓ⟩,hb⟩ := (extended_le_real_iff _ _).1 final
  refine ⟨⟨Γ,hΓ.trans vf⟩, sub_le_iff_le_add.mpr ?_⟩
  rwa [levyLieb_congr_matrix vf] at hb

end TSGA.ManyBody
