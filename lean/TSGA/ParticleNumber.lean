import TSGA.LevyLieb
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Normalization of the one-body marginal

Lebesgue measure on a particle sector splits into the first position and the
remaining positions. Summing the two diagonal spin entries restores the full
spin sum, hence the particle-number factor in the density.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory

private def splitSpace (n : ℕ) : Space (n+1) ≃ᵐ Position × Space n :=
  MeasurableEquiv.piFinSuccAbove (fun _ => Position) 0

private theorem split_preserves (n : ℕ) : MeasurePreserving (splitSpace n) :=
  volume_preserving_piFinSuccAbove (fun _ => Position) 0

private theorem split_inv (n : ℕ) (z : Position × Space n) :
    (splitSpace n).symm z = Fin.cons z.1 z.2 := by
  simp [splitSpace, MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

private def marginal {n : ℕ} (ψ : Wave (n+1)) (s : Spins (n+1)) (x : Position) : ℝ :=
  ∫ y : Space n, ‖ψ.value s (Fin.cons x y)‖ ^ 2

private theorem marginal_fubini {n : ℕ} (ψ : Wave (n+1)) (s : Spins (n+1)) :
    Integrable (marginal ψ s) ∧ (∫ x, marginal ψ s x) = ∫ z, ‖ψ.value s z‖ ^ 2 := by
  let e := splitSpace n
  have he := (split_preserves n).symm
  let f := fun z : Space (n+1) => ‖ψ.value s z‖ ^ 2
  have hi : Integrable f := (ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide)
  have hc : Integrable (fun z : Position × Space n => f (e.symm z)) (volume.prod volume) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).2 hi
  have hg (x : Position) : marginal ψ s x = ∫ y : Space n, f (e.symm (x,y)) := by simp [marginal, e, split_inv, f]
  refine ⟨by rw [show marginal ψ s = _ from funext hg]; exact hc.integral_prod_left, ?_⟩
  simp_rw [hg]
  exact (integral_prod _ hc).symm.trans (he.integral_comp' f)

private theorem marginal_trace {n : ℕ} (ψ : Wave (n+1)) (x : Position) :
    (ψ.matrixDensity x).trace.re = (n+1 : ℕ) * ∑ i : Fin 2, ∑ s : Spins n, marginal ψ (Fin.cons i s) x := by
  simp [Wave.matrixDensity, Matrix.trace, Matrix.diag, marginal, Complex.mul_conj, Complex.sq_norm,
    integral_complex_ofReal, mul_add, Finset.mul_sum]

/-- Every normalized wave in the (n+1)-particle sector has charge n+1. -/
theorem Wave.particleNumber {n : ℕ} (ψ : Wave (n+1)) :
    Integrable (fun x => (ψ.matrixDensity x).trace.re) ∧
    (∫ x, (ψ.matrixDensity x).trace.re) = n+1 := by
  have hs (i : Fin 2) : Integrable (fun x => ∑ s : Spins n, marginal ψ (Fin.cons i s) x) :=
    integrable_finsetSum _ fun s _ => (marginal_fubini ψ _).1
  have ht := (integrable_finsetSum Finset.univ (fun i _ => hs i)).const_mul ((n+1 : ℕ) : ℝ)
  refine ⟨by simpa only [marginal_trace] using ht, ?_⟩
  have hi (i : Fin 2) : (∫ x, ∑ s : Spins n, marginal ψ (Fin.cons i s) x) =
      ∑ s : Spins n, ∫ z, ‖ψ.value (Fin.cons i s) z‖ ^ 2 := by
    rw [integral_finsetSum _ (fun s _ => (marginal_fubini ψ (Fin.cons i s)).1)]
    exact Finset.sum_congr rfl fun s _ => (marginal_fubini ψ (Fin.cons i s)).2
  simp_rw [marginal_trace, integral_const_mul, integral_finsetSum _ (fun i _ => hs i), hi]
  have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2))
    (fun s => ∫ z, ‖ψ.value s z‖^2)
  rw [Fintype.sum_prod_type] at he
  change (∑ i : Fin 2, ∑ s : Spins n, ∫ z, ‖ψ.value (Fin.cons i s) z‖^2) = _ at he
  change _ * (∑ i : Fin 2, ∑ s : Spins n, ∫ z, ‖ψ.value (Fin.cons i s) z‖^2) = _
  rw [he, show (∑ s, ∫ z, ‖ψ.value s z‖^2) = 1 from ψ.normalized]
  simp

private theorem PureState.charge_nonneg (s : PureState) (x : Position) :
    0 ≤ (s.matrixDensity x).trace.re := by
  cases s with
  | vacuum => simp [matrixDensity]
  | occupied ψ =>
    change 0 ≤ (ψ.matrixDensity x).trace.re
    rw [marginal_trace]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

private theorem PureState.charge_mass (s : PureState) :
    Integrable (fun x => (s.matrixDensity x).trace.re) ∧
      (∫ x, (s.matrixDensity x).trace.re) = s.particles := by
  cases s with
  | vacuum => simp [matrixDensity, particles]
  | occupied ψ => simpa [matrixDensity, particles] using ψ.particleNumber

/-- The charge of a mixture integrates to its expected particle number. -/
theorem MixedState.particleNumber (Γ : MixedState) :
    (∫ x, (Γ.matrixDensity x).trace.re) = ∑' k, Γ.weight k * (Γ.component k).particles := by
  let f := fun k x => Γ.weight k * ((Γ.component k).matrixDensity x).trace.re
  have hρ : (fun x => (Γ.matrixDensity x).trace.re) =ᵐ[volume] fun x => ∑' k, f k x := by
    filter_upwards [Γ.density_summable] with x hs
    have hr := Complex.hasSum_re ((hs 0 0).hasSum.add (hs 1 1).hasSum)
    have ht : HasSum (fun k => f k x) ((Γ.matrixDensity x).trace.re) := by
      simpa only [f, MixedState.matrixDensity, Matrix.trace_fin_two, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_add] using hr
    exact ht.tsum_eq.symm
  have hi (k : ℕ) : Integrable (f k) := (Γ.component k).charge_mass.1.const_mul _
  have hm (k : ℕ) : (∫ x, f k x) = Γ.weight k * (Γ.component k).particles := by
    simp only [f, integral_const_mul, (Γ.component k).charge_mass.2]
  have hnorm (k : ℕ) (x : Position) : ‖f k x‖ = f k x :=
    Real.norm_of_nonneg (mul_nonneg (Γ.weight_nonneg k) ((Γ.component k).charge_nonneg x))
  have hsum : Summable (fun k => ∫ x, ‖f k x‖) := by
    simpa only [hnorm, hm] using Γ.particles_summable
  rw [integral_congr_ae hρ, ← integral_tsum_of_summable_integral_norm hi hsum]
  simp only [hm]

end TSGA.ManyBody
