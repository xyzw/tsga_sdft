import TSGA.WaveCurrent
import TSGA.WaveTwist
import TSGA.SpinPopulation

/-! # Exact changes of momentum and kinetic energy under a plane-wave twist -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

variable {n : ℕ}

private theorem spinSum_congr {a : Fin 2} {f h : Spins n → Fin n → ℝ}
    (eq : ∀ s i, s i = a → f s i = h s i) : spinSum a f = spinSum a h := by
  unfold spinSum
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  split
  · exact eq s i ‹_›
  · rfl

private theorem spinSum_sum {ι : Type*} [Fintype ι] (a : Fin 2) (f : ι → Spins n → Fin n → ℝ) :
    spinSum a (fun s i => ∑ j, f j s i) = ∑ j, spinSum a (f j) := by
  classical
  have he (s : Spins n) (i : Fin n) :
      (if s i = a then ∑ j, f j s i else 0) = ∑ j, if s i = a then f j s i else 0 := by
    split <;> simp [*]
  unfold spinSum
  simp_rw [he]
  rw [Finset.sum_comm (f := fun j s => ∑ i, if s i = a then f j s i else 0)]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem momentum_coordinate (ψ : Wave n) (v : Fin 2 → Position) (s : Spins n) (i : Fin n) (j : Fin 3) :
    (∫ x, currentPair ((ψ.twist v).value s x) ((ψ.twist v).gradient s x i j)) =
      (∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j)) + v (s i) j * ∫ x, ‖ψ.value s x‖^2 := by
  have h (x : Space n) := currentPair_phase (ψ.value s x) (ψ.gradient s x i j)
    (spinWavePhase v s x) (v (s i) j) (spinWavePhase_norm v s x)
  have he (x : Space n) : currentPair ((ψ.twist v).value s x) ((ψ.twist v).gradient s x i j) =
      currentPair (ψ.value s x) (ψ.gradient s x i j) + v (s i) j * ‖ψ.value s x‖^2 := h x
  simp_rw [he]
  rw [integral_add (currentPair_integrable (ψ.square_integrable s) (ψ.gradient_L2 s i j))
    ((ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide) |>.const_mul _),integral_const_mul]

theorem Wave.spinMomentum_twist (ψ : Wave n) (v : Fin 2 → Position) (a : Fin 2) :
    (ψ.twist v).spinMomentum a = ψ.spinMomentum a + ψ.spinNumber a • v a := by
  ext j
  rw [spinMomentum_apply]
  simp_rw [momentum_coordinate]
  rw [spinSum_add]
  have he : spinSum a (fun s i => v (s i) j * ∫ x, ‖ψ.value s x‖^2) =
      v a j * ψ.spinNumber a := by
    have hm : ψ.spinNumber a = spinSum a (fun s _ => ∫ x, ‖ψ.value s x‖^2) := ψ.spinNumber_eq_sums a
    rw [hm, ← spinSum_mul]
    exact spinSum_congr fun s i hi => by rw [hi]
  rw [he]
  change _+_ = ψ.spinMomentum a j + ψ.spinNumber a * v a j
  rw [mul_comm (ψ.spinNumber a)]
  rfl

theorem Wave.spinNumber_twist (ψ : Wave n) (v : Fin 2 → Position) (a : Fin 2) :
    (ψ.twist v).spinNumber a = ψ.spinNumber a := by
  simp only [spinNumber_eq_sums,twist,norm_mul,spinWavePhase_norm,one_mul]

private theorem energy_coordinate (ψ : Wave n) (v : Fin 2 → Position) (s : Spins n) (i : Fin n) (j : Fin 3) :
    (∫ x, ‖(ψ.twist v).gradient s x i j‖^2) =
      (∫ x, ‖ψ.gradient s x i j‖^2) +
      (2*v (s i) j*(∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j)) +
        (v (s i) j)^2 * ∫ x, ‖ψ.value s x‖^2) := by
  have hv := (ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide)
  have hz := (ψ.gradient_L2 s i j).integrable_norm_pow (p := 2) (by decide)
  have hc := (currentPair_integrable (ψ.square_integrable s) (ψ.gradient_L2 s i j)).const_mul (2*v (s i) j)
  simp only [Wave.twist,norm_mul,spinWavePhase_norm,one_mul,gradient_phase_sq]
  have hleft : Integrable (fun x => ‖ψ.gradient s x i j‖^2 + 2*v (s i) j * currentPair (ψ.value s x) (ψ.gradient s x i j)) :=
    hz.add hc
  rw [integral_add hleft (hv.const_mul ((v (s i) j)^2)),integral_add hz hc,integral_const_mul,integral_const_mul,add_assoc]

private theorem energy_regroup (ψ : Wave n) (v : Fin 2 → Position) :
    (∑ s : Spins n, ∑ i : Fin n, ∑ j : Fin 3,
      (2*v (s i) j*(∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j)) +
        (v (s i) j)^2*(∫ x, ‖ψ.value s x‖^2))) =
      ∑ a, (2*⟪v a, ψ.spinMomentum a⟫_ℝ + ‖v a‖^2 * ψ.spinNumber a) := by
  let J := fun (s : Spins n) (i : Fin n) (j : Fin 3) => ∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j)
  let m := fun s : Spins n => ∫ x, ‖ψ.value s x‖^2
  rw [spinSum_coordinate (fun a s i => ∑ j, (2*v a j*J s i j+(v a j)^2*m s))]
  apply Finset.sum_congr rfl
  intro a _
  rw [spinSum_sum]
  have hp (j : Fin 3) : spinSum a (fun s i => J s i j) = ψ.spinMomentum a j := rfl
  have hm : spinSum a (fun s _ => m s) = ψ.spinNumber a := ψ.spinNumber_eq_sums a |>.symm
  simp_rw [spinSum_add, spinSum_mul]
  simp only [hp, hm, Finset.sum_add_distrib, PiLp.inner_apply, Real.inner_apply, EuclideanSpace.real_norm_sq_eq,
    Finset.mul_sum, Finset.sum_mul]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rfl

theorem Wave.kinetic_twist (ψ : Wave n) (v : Fin 2 → Position) :
    (ψ.twist v).kinetic = ψ.kinetic + ∑ a, (2*⟪v a, ψ.spinMomentum a⟫_ℝ + ‖v a‖^2 * ψ.spinNumber a) := by
  rw [kinetic_eq_sums,ψ.kinetic_eq_sums,← energy_regroup]
  simp_rw [energy_coordinate]
  simp only [Finset.sum_add_distrib]

theorem Wave.kinetic_twist_le (ψ : Wave n) (v : Fin 2 → Position) :
    (ψ.twist v).kinetic ≤ 2*ψ.kinetic + 2*(∑ a, ‖v a‖^2)*(n : ℝ) := by
  have hnon : 0 ≤ (ψ.twist (-v)).kinetic :=
    Finset.sum_nonneg fun s _ => integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [ψ.kinetic_twist] at hnon ⊢
  simp only [Pi.neg_apply,inner_neg_left, mul_neg,norm_neg, Finset.sum_add_distrib,Finset.sum_neg_distrib] at hnon
  rw [Finset.sum_add_distrib]
  have hweight :
      (∑ a, ‖v a‖^2 * ψ.spinNumber a) ≤ (∑ a, ‖v a‖^2)*(n : ℝ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ψ.spinNumber_le a) (sq_nonneg _)
  linarith only [hnon,hweight]

end TSGA.ManyBody
