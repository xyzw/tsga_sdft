import TSGA.SpatialDensity
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! # Almost-everywhere convergence of the natural-orbital density series -/

noncomputable section
namespace TSGA.ManyBody.Spatial
open MeasureTheory
open scoped ComplexConjugate ENNReal

/-- Finite trace and normalization imply absolute convergence of every entry
of the spin density for almost every point of `ℝᵈ`. -/
theorem OneBody.diagonal_summable {d : ℕ} (γ : OneBody d) :
    ∀ᵐ x, ∀ i j, Summable fun k => (γ.occupation k : ℂ) * γ.orbital k i x * conj (γ.orbital k j x) := by
  let F (k : ℕ) (x : Point d) := γ.occupation k * ∑ s, ‖γ.orbital k s x‖^2
  have hp (k x) : 0 ≤ F k x := mul_nonneg (γ.occupation_mem k).1 (by positivity)
  have hi (k s) := (γ.orbital_L2 k s).integrable_norm_pow (p := 2) (by decide)
  have hF (k) : Integrable (F k) := (integrable_finsetSum _ (fun s _ => hi k s)).const_mul _
  have hunit (k) : (∑ s, ∫ x, ‖γ.orbital k s x‖^2) = 1 := by
    have h := congrArg Complex.re (γ.orthonormal k k)
    simpa [Complex.conj_mul', ← Complex.ofReal_pow, integral_complex_ofReal, Fin.sum_univ_two] using h
  have hm (k) : eLpNorm (F k) 1 volume = ENNReal.ofReal (γ.occupation k) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hF k)]
    simp only [Real.norm_of_nonneg (hp k _), F, integral_const_mul,
      integral_finsetSum _ (fun s _ => hi k s), hunit, mul_one]
  have hn : ∀ᵐ x : Point d, Summable fun k => ‖F k x‖ := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl (fun k => (hF k).1)
    simpa only [hm] using γ.finite_trace.tsum_ofReal_ne_top
  filter_upwards [hn] with x hx
  intro i j
  apply hx.of_norm_bounded
  intro k
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (γ.occupation_mem k).1,
    Complex.norm_conj, Real.norm_of_nonneg (hp k x), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (γ.occupation_mem k).1
  have hb (i : Fin 2) : ‖γ.orbital k i x‖ ^ 2 ≤ ∑ s, ‖γ.orbital k s x‖ ^ 2 :=
    Finset.single_le_sum (f := fun s => ‖γ.orbital k s x‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [hb i, hb j, sq_nonneg (‖γ.orbital k i x‖ - ‖γ.orbital k j x‖)]

end TSGA.ManyBody.Spatial
