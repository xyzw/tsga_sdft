import TSGA.CutoffGradientBound
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Quantitative gradient bounds from strong convergence of difference quotients

The generic input is strong L² convergence to the coordinate weak derivative.
Convergence of the squared L² norms yields the integral estimate. An almost
everywhere convergent subsequence in each coordinate yields the local estimate.
-/

noncomputable section
namespace TSGA.SSW

open Filter MeasureTheory Set
open scoped Topology InnerProductSpace

def directionalQuotient (u : Position → ℝ) (i : Fin 3) (t : ℝ) (x : Position) : ℝ :=
  (u (x + t • PiLp.single 2 i 1) - u x) / t

theorem directionalQuotient_memLp {u : Position → ℝ} (hu : MemLp u 2) (i : Fin 3) (t : ℝ) :
    MemLp (directionalQuotient u i t) 2 := by
  let v : Position := t • PiLp.single 2 i 1
  have shifted : MemLp (fun x : Position => u (x+v)) 2 volume :=
    hu.comp_measurePreserving (measurePreserving_add_right (volume : Measure Position) v)
  have diff : MemLp (fun x : Position => u (x+v)-u x) 2 volume := shifted.sub hu
  change MemLp (fun x : Position => (u (x+v)-u x)/t) 2 volume
  simpa only [div_eq_mul_inv] using diff.mul_const t⁻¹

theorem gradientComponent_memLp {G : Position → Position} (hG : MemLp G 2) (i : Fin 3) :
    MemLp (fun x => G x i) 2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).comp_memLp' hG

/-- For an H¹ function, one-sided translation difference quotients along a
coordinate axis converge strongly in L² to its weak derivative. -/
def SobolevDirectionalLimits : Prop :=
  ∀ (u : Position → ℝ) (G : Position → Position) (hu : MemLp u 2),
    (∀ i, WeakPartialOn univ i u (fun x => G x i)) → ∀ (hG : MemLp G 2) (i : Fin 3),
      Tendsto (fun t : ℝ => (directionalQuotient_memLp hu i t).toLp (directionalQuotient u i t))
        (𝓝[>] 0) (𝓝 ((gradientComponent_memLp hG i).toLp (fun x => G x i)))

private theorem normSq_L2 {f : Position → ℝ} (hf : MemLp f 2) :
    ‖hf.toLp f‖^2 = ∫ x, f x^2 := by
  rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs,sq_abs]

private theorem coordNorm (t : ℝ) (i : Fin 3) : ‖t • (PiLp.single 2 i 1 : Position)‖^2 = t^2 := by
  simp [norm_smul,sq_abs]

theorem SobolevDirectionalLimits.toDifferenceBounds (H : SobolevDirectionalLimits) : SobolevDifferenceBounds where
  pointwise u G hu hw hG K hbound := by
    have coord (i : Fin 3) : ∀ᵐ x, (G x i)^2 ≤ K x := by
      have hm : TendstoInMeasure volume (directionalQuotient u i) (𝓝[>] 0) (fun x => G x i) :=
        (tendstoInMeasure_of_tendsto_Lp (H u G hu hw hG i)).congr
          (fun t => (directionalQuotient_memLp hu i t).coeFn_toLp) (gradientComponent_memLp hG i).coeFn_toLp
      obtain ⟨t,ht,ha⟩ := hm.exists_seq_tendsto_ae'
      filter_upwards [ha] with x hx
      apply le_of_tendsto (hx.pow 2)
      have dir : Tendsto (fun k => t k • (PiLp.single 2 i 1 : Position)) atTop (𝓝 0) := by
        simpa using (tendsto_nhds_of_tendsto_nhdsWithin ht).smul_const (PiLp.single 2 i 1 : Position)
      filter_upwards [dir.eventually (hbound x),ht.eventually self_mem_nhdsWithin] with k hk hpos
      change 0 < t k at hpos
      rw [coordNorm] at hk
      simpa only [directionalQuotient,div_pow,div_le_iff₀ (sq_pos_of_pos hpos)] using hk
    filter_upwards [ae_all_iff.mpr coord] with x hx
    calc
      ‖G x‖^2 = ∑ i, (G x i)^2 := EuclideanSpace.real_norm_sq_eq _
      _ ≤ ∑ _ : Fin 3, K x := Finset.sum_le_sum fun i _ => hx i
      _ = _ := by simp

  integral u G hu hw hG K hbound := by
    have coord (i : Fin 3) : (∫ x, (G x i)^2) ≤ K := by
      have hn := (H u G hu hw hG i).norm.pow 2
      simp only [normSq_L2] at hn
      apply le_of_tendsto hn
      filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
      change 0 < t at ht
      have hb := hbound (t • PiLp.single 2 i 1)
      rw [coordNorm] at hb
      simp only [directionalQuotient,div_pow,integral_div,div_le_iff₀ (sq_pos_of_pos ht)]
      exact hb
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum _ (fun i _ => (gradientComponent_memLp hG i).integrable_sq)]
    calc
      _ ≤ ∑ _ : Fin 3, K := Finset.sum_le_sum fun i _ => coord i
      _ = _ := by simp

end TSGA.SSW
