import TSGA.LevyLieb
import Mathlib.MeasureTheory.Function.L2Space

/-! # Momentum of a fixed spin population in a Coulomb particle sector -/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

/-- Momentum density in one coordinate of one spin configuration. -/
def currentPair (u z : ℂ) : ℝ := (conj u * z).im

theorem currentPair_bound (u z : ℂ) : |currentPair u z| ≤ (‖u‖ ^ 2 + ‖z‖ ^ 2)/2 := by
  have h := Complex.abs_im_le_norm (conj u*z)
  rw [norm_mul,Complex.norm_conj] at h
  change |(conj u*z).im| ≤ _
  nlinarith only [h,sq_nonneg (‖u‖-‖z‖)]

theorem currentPair_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u z : α → ℂ} (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) :
    Integrable (fun x => currentPair (u x) (z x)) μ := by
  have hI := ((hu.integrable_norm_pow (p := 2) (by decide)).add
    (hz.integrable_norm_pow (p := 2) (by decide))).div_const 2
  apply hI.mono' (Complex.continuous_im.comp_aestronglyMeasurable
    ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable).mul hz.aestronglyMeasurable))
  exact ae_of_all _ fun x => currentPair_bound (u x) (z x)

theorem currentPair_phase (u z c : ℂ) (t : ℝ) (hc : ‖c‖ = 1) :
    currentPair (c*u) (c*(z+Complex.I*(t:ℂ)*u)) = currentPair u z + t*‖u‖^2 := by
  have hu : conj c*c = 1 := by rw [mul_comm,Complex.mul_conj, ← Complex.sq_norm,hc]; norm_num
  unfold currentPair
  rw [map_mul, show conj c*conj u*(c*(z+Complex.I*(t:ℂ)*u)) =
    (conj c*c)*(conj u*(z+Complex.I*(t:ℂ)*u)) by ring,hu,one_mul]
  simp [Complex.mul_im,Complex.mul_re,Complex.sq_norm,Complex.normSq_apply]
  ring

theorem gradient_phase_sq (u z : ℂ) (t : ℝ) :
    ‖z+Complex.I*(t:ℂ)*u‖^2 = ‖z‖^2 + 2*t*currentPair u z + t^2*‖u‖^2 := by
  simp [currentPair,Complex.mul_im,Complex.mul_re,Complex.sq_norm,Complex.normSq_apply]
  ring

/-- Select terms corresponding to one electron spin from a sum over all
configurations and all particle positions. -/
def spinSum {n : ℕ} (a : Fin 2) (f : Spins n → Fin n → ℝ) : ℝ :=
  ∑ s, ∑ i, if s i = a then f s i else 0

theorem spinSum_add {n : ℕ} (a : Fin 2) (f h : Spins n → Fin n → ℝ) :
    spinSum a (fun s i => f s i + h s i) = spinSum a f + spinSum a h := by
  simp [spinSum,ite_add_zero,Finset.sum_add_distrib]

theorem spinSum_mul {n : ℕ} (a : Fin 2) (b : ℝ) (f : Spins n → Fin n → ℝ) :
    spinSum a (fun s i => b*f s i) = b*spinSum a f := by
  simp [spinSum,Finset.mul_sum,mul_ite]

theorem spinSum_coordinate {n : ℕ} (f : Fin 2 → Spins n → Fin n → ℝ) :
    (∑ s : Spins n, ∑ i : Fin n, f (s i) s i) = ∑ a : Fin 2, spinSum a (f a) := by
  unfold spinSum
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  simp

/-- The vector of integrated momenta for spin a, in the convention
Im(conj ψ ∇ψ). -/
def Wave.spinMomentum {n : ℕ} (ψ : Wave n) (a : Fin 2) : Position :=
  WithLp.toLp 2 fun j => spinSum a (fun s i => ∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j))

theorem Wave.spinMomentum_apply {n : ℕ} (ψ : Wave n) (a : Fin 2) (j : Fin 3) :
    ψ.spinMomentum a j = spinSum a (fun s i => ∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j)) := rfl

theorem Wave.kinetic_eq_sums {n : ℕ} (ψ : Wave n) :
    ψ.kinetic = ∑ s : Spins n, ∑ i : Fin n, ∑ j : Fin 3, ∫ x, ‖ψ.gradient s x i j‖^2 := by
  unfold kinetic sectorIntegral
  have hi (s i j) := (ψ.gradient_L2 s i j).integrable_norm_pow (p := 2) (by decide)
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi _ i j)),
    integral_finsetSum _ (fun j _ => hi _ _ j)]

theorem Wave.mass_sum {n : ℕ} (ψ : Wave n) :
    (∑ s : Spins n, ∑ _i : Fin n, ∫ x, ‖ψ.value s x‖^2) = n := by
  have hn : (∑ s, ∫ x, ‖ψ.value s x‖^2) = 1 := ψ.normalized
  simp only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul, ← Finset.mul_sum,hn,mul_one]

theorem Wave.spinMomentum_bound {n : ℕ} (ψ : Wave n) (a : Fin 2) (j : Fin 3) :
    |ψ.spinMomentum a j| ≤ (n : ℝ) + ψ.kinetic := by
  let m := fun s : Spins n => ∫ x, ‖ψ.value s x‖^2
  let e := fun (s : Spins n) (i : Fin n) (k : Fin 3) => ∫ x, ‖ψ.gradient s x i k‖^2
  have hm (s) : 0 ≤ m s := integral_nonneg fun _ => sq_nonneg _
  have he (s i k) : 0 ≤ e s i k := integral_nonneg fun _ => sq_nonneg _
  have hi (s i) : |∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j)| ≤ m s + ∑ k, e s i k := by
    have hv := (ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide)
    have hz := (ψ.gradient_L2 s i j).integrable_norm_pow (p := 2) (by decide)
    calc
      _ ≤ ∫ x, ‖currentPair (ψ.value s x) (ψ.gradient s x i j)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖ψ.value s x‖^2 + ‖ψ.gradient s x i j‖^2 := by
        apply integral_mono (currentPair_integrable (ψ.square_integrable s) (ψ.gradient_L2 s i j)).norm (hv.add hz)
        intro x
        change |currentPair _ _| ≤ ‖ψ.value s x‖^2 + ‖ψ.gradient s x i j‖^2
        linarith only [currentPair_bound (ψ.value s x) (ψ.gradient s x i j),sq_nonneg ‖ψ.value s x‖,sq_nonneg ‖ψ.gradient s x i j‖]
      _ ≤ _ := by
        rw [integral_add hv hz]
        exact add_le_add le_rfl (Finset.single_le_sum (fun k _ => he s i k) (Finset.mem_univ j))
  rw [Wave.spinMomentum_apply,spinSum, ← ψ.mass_sum, ψ.kinetic_eq_sums]
  calc
    _ ≤ ∑ s, |∑ i : Fin n, if s i = a then ∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, ∑ i : Fin n, (m s + ∑ k, e s i k) := by
      apply Finset.sum_le_sum
      intro s _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      split
      · exact hi s i
      · rw [abs_zero]
        exact add_nonneg (hm s) (Finset.sum_nonneg (fun k _ => he s i k))
    _ = _ := by simp only [Finset.sum_add_distrib,m,e]

def PureState.spinMomentum (s : PureState) (a : Fin 2) : Position := match s with
  | .vacuum => 0
  | .occupied ψ => ψ.spinMomentum a

theorem PureState.spinMomentum_bound (s : PureState) (a : Fin 2) (j : Fin 3) :
    |s.spinMomentum a j| ≤ (s.particles : ℝ) + s.kinetic := by
  cases s with
  | vacuum => simp [spinMomentum,particles,kinetic]
  | occupied ψ => exact ψ.spinMomentum_bound a j

def MixedState.spinMomentum (Γ : MixedState) (a : Fin 2) : Position :=
  WithLp.toLp 2 (fun j => ∑' k, Γ.weight k * (Γ.component k).spinMomentum a j)

theorem MixedState.spinMomentum_apply (Γ : MixedState) (a : Fin 2) (j : Fin 3) :
    Γ.spinMomentum a j = ∑' k, Γ.weight k * (Γ.component k).spinMomentum a j := rfl

theorem MixedState.spinMomentum_summable (Γ : MixedState) (a : Fin 2) (j : Fin 3) :
    Summable (fun k => Γ.weight k * (Γ.component k).spinMomentum a j) := by
  apply (Γ.particles_summable.add Γ.kinetic_summable).of_norm_bounded
  intro k
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Γ.weight_nonneg k),← mul_add]
  exact mul_le_mul_of_nonneg_left ((Γ.component k).spinMomentum_bound a j) (Γ.weight_nonneg k)

end TSGA.ManyBody
