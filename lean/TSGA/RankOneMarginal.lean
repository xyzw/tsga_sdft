import TSGA.MarginalPositivity
import TSGA.SSWBounds
import Mathlib.MeasureTheory.Integral.Pi

/-! # The missing spin channel of a fully polarized marginal

Testing the first marginal with a constant spin row gives an integral of
squares. If this channel is empty, every pure component of positive weight
satisfies the same linear relation between its two spin amplitudes.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped ComplexConjugate ComplexOrder

private def rowValue (c d : ℂ) (A : SpinMatrix) : ℂ :=
  c*conj c*A 0 0 - c*conj d*A 0 1 - d*conj c*A 1 0 + d*conj d*A 1 1

def spinDefect (c d : ℂ) (A : SpinMatrix) : ℝ := (rowValue c d A).re

private theorem row_gram {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (c d : ℂ) :
    ((∫ x, ‖c*u x-d*v x‖^2 ∂μ : ℝ) : ℂ) =
      c*conj c*(∫ x, u x*conj (u x) ∂μ) - c*conj d*(∫ x, u x*conj (v x) ∂μ) -
      d*conj c*(∫ x, v x*conj (u x) ∂μ) + d*conj d*(∫ x, v x*conj (v x) ∂μ) := by
  have hconj {g : α → ℂ} (h : MemLp g 2 μ) : MemLp (fun x => conj (g x)) 2 μ :=
    h.of_le (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable) (ae_of_all _ fun x => (Complex.norm_conj _).le)
  have pair {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (t : ℂ) :
      Integrable (fun x => t*(f x*conj (g x))) μ := (hf.integrable_mul (hconj hg)).const_mul t
  have eqn (x : α) : ((‖c*u x-d*v x‖^2 : ℝ) : ℂ) =
      c*conj c*(u x*conj (u x)) - c*conj d*(u x*conj (v x)) -
      d*conj c*(v x*conj (u x)) + d*conj d*(v x*conj (v x)) := by
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sub, map_mul, map_mul]
    ring
  rw [← integral_complex_ofReal]
  simp_rw [eqn]
  have hab : Integrable (fun x => c*conj c*(u x*conj (u x)) - c*conj d*(u x*conj (v x))) μ :=
    (pair hu hu _).sub (pair hu hv _)
  have habc : Integrable (fun x => c*conj c*(u x*conj (u x)) - c*conj d*(u x*conj (v x)) -
      d*conj c*(v x*conj (u x))) μ := hab.sub (pair hv hu _)
  rw [integral_add habc (pair hv hv (d*conj d)), integral_sub hab (pair hv hu (d*conj c)),
    integral_sub (pair hu hu (c*conj c)) (pair hu hv (c*conj d))]
  simp only [integral_const_mul]

private def rowSection {n : ℕ} (ψ : Wave (n+1)) (c d : ℂ) (t : Spins n) (z : Space (n+1)) : ℝ :=
  ‖c*ψ.value (Fin.cons 0 t) z - d*ψ.value (Fin.cons 1 t) z‖^2

private theorem Wave.test_marginal {n : ℕ} (ψ : Wave (n+1)) (c d : ℂ) :
    ∀ᵐ x, spinDefect c d (ψ.matrixDensity x) =
      (n+1 : ℕ) * ∑ t : Spins n, ∫ y : Space n, rowSection ψ c d t (Fin.cons x y) := by
  filter_upwards [ψ.square_integrable_slices] with x hx
  apply_fun (fun r : ℝ => (r : ℂ)) using Complex.ofReal_injective
  let z (i : Fin 2) (t : Spins n) := fun y : Space n => ψ.value (Fin.cons i t) (Fin.cons x y)
  have eqn : rowValue c d (ψ.matrixDensity x) =
      (((n+1 : ℕ) * ∑ t : Spins n, ∫ y : Space n, rowSection ψ c d t (Fin.cons x y) : ℝ) : ℂ) := by
    push_cast
    simp only [rowValue, Wave.matrixDensity]
    have ht (t : Spins n) := row_gram (hx 0 t) (hx 1 t) c d
    simp only [rowSection]
    simp_rw [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    push_cast
    ring
  change ((rowValue c d (ψ.matrixDensity x)).re : ℂ) = _
  rw [eqn]
  simp

private theorem PureState.defect_nonneg (s : PureState) (c d : ℂ) :
    ∀ᵐ x, 0 ≤ spinDefect c d (s.matrixDensity x) := by
  cases s with
  | vacuum => exact ae_of_all _ fun _ => by simp [matrixDensity, spinDefect, rowValue]
  | occupied ψ =>
    filter_upwards [ψ.test_marginal c d] with x hx
    change 0 ≤ spinDefect c d (ψ.matrixDensity x)
    rw [hx]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

theorem MixedState.component_defect_zero (Γ : MixedState) {f : Position → ℝ} {M : SpinMatrix}
    (rep : feasible (fun x => (f x : ℂ) • M) Γ) {c d : ℂ} (hM : spinDefect c d M = 0)
    (k : ℕ) (hk : 0 < Γ.weight k) :
    ∀ᵐ x, spinDefect c d ((Γ.component k).matrixDensity x) = 0 := by
  filter_upwards [Γ.density_summable,rep,ae_all_iff.mpr (fun l => (Γ.component l).defect_nonneg c d)] with x hs he hp
  have h := (((((hs 0 0).hasSum.mul_left (c*conj c)).sub ((hs 0 1).hasSum.mul_left (c*conj d))).sub
    ((hs 1 0).hasSum.mul_left (d*conj c))).add ((hs 1 1).hasSum.mul_left (d*conj d)))
  have hh : HasSum (fun l => Γ.weight l * spinDefect c d ((Γ.component l).matrixDensity x))
      (spinDefect c d (Γ.matrixDensity x)) := by
    apply (Complex.hasSum_re h).congr_fun
    intro l
    have fact (a : ℝ) (A : SpinMatrix) : c*conj c*((a:ℂ)*A 0 0) - c*conj d*((a:ℂ)*A 0 1) -
        d*conj c*((a:ℂ)*A 1 0) + d*conj d*((a:ℂ)*A 1 1) = (a:ℂ)*rowValue c d A := by
      unfold rowValue
      ring
    symm
    exact (congrArg Complex.re (fact (Γ.weight l) ((Γ.component l).matrixDensity x))).trans
      (Complex.re_ofReal_mul _ _)
  have hz : spinDefect c d (Γ.matrixDensity x) = 0 := by
    rw [he]
    have eqn : rowValue c d ((f x : ℂ) • M) = (f x : ℂ)*rowValue c d M := by
      simp only [rowValue,Matrix.smul_apply,smul_eq_mul]
      ring
    change (rowValue c d _).re = 0
    rw [eqn,Complex.re_ofReal_mul, show (rowValue c d M).re = 0 from hM,mul_zero]
  have hle := hh.summable.le_tsum k fun l _ => mul_nonneg (Γ.weight_nonneg l) (hp l)
  rw [hh.tsum_eq,hz] at hle
  exact le_antisymm (le_of_not_gt (fun h => (mul_pos hk h).not_ge hle)) (hp k)

/-- An empty spin row of the first marginal annihilates the wave in the
full configuration space, for every choice of the remaining spins. -/
theorem Wave.row_zero {n : ℕ} (ψ : Wave (n+1)) {c d : ℂ}
    (zero : ∀ᵐ x, spinDefect c d (ψ.matrixDensity x) = 0) (t : Spins n) :
    ∀ᵐ z, c*ψ.value (Fin.cons 0 t) z = d*ψ.value (Fin.cons 1 t) z := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => Position) 0).symm
  have heq (z : Position × Space n) : e.symm z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hi : Integrable (rowSection ψ c d t) :=
    (((ψ.square_integrable (Fin.cons 0 t)).const_mul c).sub
      ((ψ.square_integrable (Fin.cons 1 t)).const_mul d)).integrable_norm_pow (p := 2) (by decide)
  have hcomp : Integrable (fun z : Position × Space n => rowSection ψ c d t (e.symm z)) (volume.prod volume) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).2 hi
  have mass : (∫ z, rowSection ψ c d t z) = 0 := by
    rw [← he.integral_comp']
    change (∫ z : Position × Space n, rowSection ψ c d t (e.symm z) ∂volume.prod volume) = 0
    rw [integral_prod _ hcomp]
    apply integral_eq_zero_of_ae
    filter_upwards [ψ.test_marginal c d,zero] with x h hz
    rw [hz] at h
    have hs (u : Spins n) : 0 ≤ ∫ y : Space n, rowSection ψ c d u (Fin.cons x y) :=
      integral_nonneg fun _ => sq_nonneg _
    have hzero : (∑ u : Spins n, ∫ y : Space n, rowSection ψ c d u (Fin.cons x y)) = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left (by positivity)
    simpa only [heq,Pi.zero_apply] using (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hs u)).mp hzero t (Finset.mem_univ t)
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp mass] with z hz
  change ‖c*ψ.value (Fin.cons 0 t) z-d*ψ.value (Fin.cons 1 t) z‖^2 = 0 at hz
  exact sub_eq_zero.mp (by simpa using hz)

/-- At full polarization there is a nonzero spin row of zero expectation.
Its coefficients recover the axial magnetization, including when a spin
population vanishes. -/
theorem spinDefect_full_polarization {M : SpinMatrix} {θ : ℝ} (h : SSW.SpinParameters M 1 θ) :
    ∃ c d : ℂ, spinDefect c d M = 0 ∧ 0 < ‖c‖^2 + ‖d‖^2 ∧
      ‖d‖^2 - ‖c‖^2 = Real.cos θ * (‖c‖^2 + ‖d‖^2) := by
  let a := (M 0 0).re
  let b := (M 1 1).re
  let z := M 1 0
  have ha : 0 ≤ a := (RCLike.nonneg_iff.mp h.positive.diag_nonneg).1
  have hb : 0 ≤ b := (RCLike.nonneg_iff.mp h.positive.diag_nonneg).1
  have h00 : (a : ℂ) = M 0 0 := h.positive.1.coe_re_apply_self 0
  have h11 : (b : ℂ) = M 1 1 := h.positive.1.coe_re_apply_self 1
  have h01 : conj z = M 0 1 := h.positive.1.apply 0 1
  have htr : M.trace.re = a+b := by simp [a,b,Matrix.trace_fin_two]
  have hax : a-b = (a+b)*Real.cos θ := by simpa only [SSW.thirdMagnetization,one_mul,htr] using h.axial
  have hr : 0 < a+b := htr ▸ h.charge_pos
  have hmag := h.magnitude
  simp only [transverseMagnetization,SSW.thirdMagnetization,one_mul,htr] at hmag
  change Real.sqrt (‖2*z‖^2 + (a-b)^2) = a+b at hmag
  have hz : ‖z‖^2 = a*b := by
    have hsq := Real.sq_sqrt (show 0 ≤ ‖2*z‖^2+(a-b)^2 from add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [hmag,norm_mul] at hsq
    norm_num at hsq
    nlinarith only [hsq]
  rcases ha.eq_or_lt with h0 | ha'
  · refine ⟨1,0,?_,by norm_num,?_⟩
    · simp [spinDefect,rowValue, ← h00, ← h0]
    · have hpos : b ≠ 0 := by linarith only [h0,hr]
      have hx : Real.cos θ = -1 := by
        apply (mul_left_cancel₀ hpos)
        linarith only [show -b = b*Real.cos θ by simpa [← h0] using hax]
      simp [hx]
  · refine ⟨z,(a:ℂ),?_,?_,?_⟩
    · have hzc : z*conj z = (a:ℂ)*(b:ℂ) := by
        rw [Complex.mul_conj, ← Complex.sq_norm,hz,Complex.ofReal_mul]
      change (z*conj z*M 0 0-z*conj (a:ℂ)*M 0 1-(a:ℂ)*conj z*M 1 0+
        (a:ℂ)*conj (a:ℂ)*M 1 1).re=0
      rw [← h00,← h11,← h01,Complex.conj_ofReal]
      change (z*conj z*(a:ℂ)-z*(a:ℂ)*conj z-(a:ℂ)*conj z*z+(a:ℂ)*(a:ℂ)*(b:ℂ)).re=0
      rw [show z*conj z*(a:ℂ)-z*(a:ℂ)*conj z-(a:ℂ)*conj z*z+(a:ℂ)*(a:ℂ)*(b:ℂ) =
        (a:ℂ)*((a:ℂ)*(b:ℂ)-z*conj z) by ring,hzc,sub_self,mul_zero,Complex.zero_re]
    · rw [Complex.norm_real,Real.norm_of_nonneg ha]
      positivity
    · rw [Complex.norm_real,Real.norm_of_nonneg ha,hz]
      linear_combination a*hax

end TSGA.ManyBody
