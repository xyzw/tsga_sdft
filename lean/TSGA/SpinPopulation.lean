import TSGA.ParticleNumber
import TSGA.SSWDomain

/-! # Spin populations of fermionic Coulomb states

Antisymmetry makes the integrated occupation of a fixed spin independent
of the particle coordinate used to compute it. Thus the one-particle
spin marginal also counts particles of each spin in a countable mixture.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory

/-- Total occupation of spin a, summed over all particle coordinates. -/
def Wave.spinNumber {n : ℕ} (ψ : Wave n) (a : Fin 2) : ℝ :=
  sectorIntegral fun s x => ∑ i : Fin n, if s i = a then ‖ψ.value s x‖^2 else 0

theorem Wave.spinNumber_eq_sums {n : ℕ} (ψ : Wave n) (a : Fin 2) :
    ψ.spinNumber a = ∑ s, ∑ i : Fin n, if s i = a then (∫ x, ‖ψ.value s x‖^2) else 0 := by
  unfold spinNumber sectorIntegral
  apply Finset.sum_congr rfl
  intro s _
  have h (i : Fin n) : Integrable (fun x => if s i = a then ‖ψ.value s x‖^2 else 0) := by
    split_ifs
    · exact (ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide)
    · exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun i _ => h i)]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

theorem Wave.spinNumber_nonneg {n : ℕ} (ψ : Wave n) (a : Fin 2) : 0 ≤ ψ.spinNumber a := by
  unfold spinNumber sectorIntegral
  exact Finset.sum_nonneg fun s _ => integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => by split <;> positivity

theorem Wave.sum_spinNumber {n : ℕ} (ψ : Wave n) : ∑ a, ψ.spinNumber a = n := by
  simp_rw [ψ.spinNumber_eq_sums]
  rw [Finset.sum_comm]
  have count (s : Spins n) : (∑ a : Fin 2, ∑ i : Fin n, if s i = a then (∫ x, ‖ψ.value s x‖^2) else 0)
      = n * (∫ x, ‖ψ.value s x‖^2) := by
    rw [Finset.sum_comm]
    simp
  simp_rw [count]
  rw [← Finset.mul_sum, show (∑ s, ∫ x, ‖ψ.value s x‖^2) = 1 from ψ.normalized, mul_one]

theorem Wave.spinNumber_le {n : ℕ} (ψ : Wave n) (a : Fin 2) : ψ.spinNumber a ≤ n := by
  rw [← ψ.sum_spinNumber]
  exact Finset.single_le_sum (fun a _ => ψ.spinNumber_nonneg a) (Finset.mem_univ a)

/-- Relabeling all particles does not change the integrated squared
amplitude of the corresponding spin configuration. -/
theorem Wave.spinMass_perm {n : ℕ} (ψ : Wave n) (π : Equiv.Perm (Fin n)) (s : Spins n) :
    (∫ x, ‖ψ.value (s ∘ π) x‖^2) = (∫ x, ‖ψ.value s x‖^2) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => Position) π.symm
  have he : MeasurePreserving e := volume_measurePreserving_piCongrLeft _ _
  have heq (z : Space n) : e z = z ∘ π := by
    funext i
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [← he.integral_comp' (fun x => ‖ψ.value (s ∘ π) x‖^2)]
  apply integral_congr_ae
  filter_upwards [ψ.antisymmetric π s] with x hx
  simp only [heq, hx, norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

private theorem Wave.spinNumber_first {n : ℕ} (ψ : Wave (n+1)) (a : Fin 2) :
    ψ.spinNumber a = (n+1 : ℕ) * ∑ t : Spins n, ∫ z, ‖ψ.value (Fin.cons a t) z‖^2 := by
  let m := fun s : Spins (n+1) => ∫ z, ‖ψ.value s z‖^2
  let F := fun (i : Fin (n+1)) => ∑ s : Spins (n+1), if s i = a then m s else 0
  have symm (i : Fin (n+1)) : F i = F 0 := by
    let π := Equiv.swap 0 i
    let e := (Equiv.arrowCongr π (Equiv.refl (Fin 2)))
    have hcomp (s : Spins (n+1)) : e s = s ∘ π := by ext j; simp [e, π]
    have h := e.sum_comp (fun s : Spins (n+1) => if s 0 = a then m s else 0)
    simpa only [F, hcomp, Function.comp_apply, show π 0 = i from Equiv.swap_apply_left _ _,
      show ∀ s, m (s ∘ π) = m s from ψ.spinMass_perm π] using h
  have head : F 0 = ∑ t : Spins n, m (Fin.cons a t) := by
    let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)
    have h := e.sum_comp (fun s => if s 0 = a then m s else 0)
    rw [Fintype.sum_prod_type] at h
    change (∑ b : Fin 2, ∑ t : Spins n, if b = a then m (Fin.cons b t) else 0) = F 0 at h
    rw [← h]
    simp only [← Finset.ite_sum_zero]
    simp
  rw [ψ.spinNumber_eq_sums, Finset.sum_comm]
  change (∑ i, F i) = _
  simp only [symm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, head]
  rfl

private def spinSlice {n : ℕ} (ψ : Wave (n+1)) (s : Spins (n+1)) (x : Position) : ℝ :=
  ∫ y : Space n, ‖ψ.value s (Fin.cons x y)‖^2

private theorem spinSlice_mass {n : ℕ} (ψ : Wave (n+1)) (s : Spins (n+1)) :
    Integrable (spinSlice ψ s) ∧ (∫ x, spinSlice ψ s x) = (∫ z, ‖ψ.value s z‖^2) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => Position) 0).symm
  let f := fun z : Space (n+1) => ‖ψ.value s z‖^2
  have hi : Integrable f := (ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide)
  have hc : Integrable (fun z : Position × Space n => f (e.symm z)) (volume.prod volume) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).2 hi
  have hg (x : Position) : spinSlice ψ s x = ∫ y, f (e.symm (x,y)) := by
    have h (z : Position × Space n) : e.symm z = Fin.cons z.1 z.2 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    simp only [h]
    rfl
  refine ⟨by rw [show spinSlice ψ s = _ from funext hg]; exact hc.integral_prod_left, ?_⟩
  simp_rw [hg]
  exact (integral_prod _ hc).symm.trans (he.integral_comp' f)

private theorem Wave.diag_eq {n : ℕ} (ψ : Wave (n+1)) (x : Position) (a : Fin 2) :
    (ψ.matrixDensity x a a).re = (n+1 : ℕ) * ∑ s : Spins n, spinSlice ψ (Fin.cons a s) x := by
  simp [Wave.matrixDensity, spinSlice, Complex.mul_conj, Complex.sq_norm, integral_complex_ofReal,
    Finset.mul_sum]

theorem Wave.integral_spinDensity {n : ℕ} (ψ : Wave (n+1)) (a : Fin 2) :
    Integrable (fun x => (ψ.matrixDensity x a a).re) ∧ (∫ x, (ψ.matrixDensity x a a).re) = ψ.spinNumber a := by
  have h := (integrable_finsetSum Finset.univ (fun s _ => (spinSlice_mass ψ (Fin.cons a s)).1)).const_mul ((n+1 : ℕ) : ℝ)
  refine ⟨by simpa only [ψ.diag_eq] using h, ?_⟩
  simp_rw [ψ.diag_eq, integral_const_mul, integral_finsetSum _ (fun s _ => (spinSlice_mass ψ (Fin.cons a s)).1),
    (fun s => (spinSlice_mass ψ (Fin.cons a s)).2), ψ.spinNumber_first]

def PureState.spinNumber (t : PureState) (a : Fin 2) : ℝ := match t with
  | .vacuum => 0
  | .occupied ψ => ψ.spinNumber a

theorem PureState.spinNumber_nonneg (s : PureState) (a : Fin 2) : 0 ≤ s.spinNumber a := by
  cases s with
  | vacuum => rfl
  | occupied ψ => exact ψ.spinNumber_nonneg a

theorem PureState.sum_spinNumber (s : PureState) : ∑ a, s.spinNumber a = s.particles := by
  cases s with
  | vacuum => simp [spinNumber,particles]
  | occupied ψ => exact ψ.sum_spinNumber

theorem PureState.spinNumber_le (s : PureState) (a : Fin 2) : s.spinNumber a ≤ s.particles := by
  rw [← s.sum_spinNumber]
  exact Finset.single_le_sum (fun a _ => s.spinNumber_nonneg a) (Finset.mem_univ a)

theorem PureState.integral_spinDensity (s : PureState) (a : Fin 2) :
    Integrable (fun x => (s.matrixDensity x a a).re) ∧ (∫ x, (s.matrixDensity x a a).re) = s.spinNumber a := by
  cases s with
  | vacuum => simp [matrixDensity, spinNumber]
  | occupied ψ => exact ψ.integral_spinDensity a

private theorem PureState.diag_nonneg (s : PureState) (a : Fin 2) (x : Position) : 0 ≤ (s.matrixDensity x a a).re := by
  cases s with
  | vacuum => simp [matrixDensity]
  | occupied ψ =>
    change 0 ≤ (ψ.matrixDensity x a a).re
    rw [ψ.diag_eq]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

def MixedState.spinNumber (Γ : MixedState) (a : Fin 2) : ℝ := ∑' k, Γ.weight k * (Γ.component k).spinNumber a

theorem MixedState.spinNumber_summable (Γ : MixedState) (a : Fin 2) :
    Summable (fun k => Γ.weight k * (Γ.component k).spinNumber a) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (Γ.weight_nonneg k) ((Γ.component k).spinNumber_nonneg a))
    (fun k => mul_le_mul_of_nonneg_left ((Γ.component k).spinNumber_le a) (Γ.weight_nonneg k)) Γ.particles_summable

theorem MixedState.spinNumber_nonneg (Γ : MixedState) (a : Fin 2) : 0 ≤ Γ.spinNumber a :=
  tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) ((Γ.component k).spinNumber_nonneg a)

theorem MixedState.sum_spinNumber (Γ : MixedState) : ∑ a, Γ.spinNumber a = ∑' k, Γ.weight k * (Γ.component k).particles := by
  unfold spinNumber
  rw [← Summable.tsum_finsetSum (fun a _ => Γ.spinNumber_summable a)]
  simp_rw [← Finset.mul_sum, PureState.sum_spinNumber]

theorem MixedState.integral_spinDensity (Γ : MixedState) (a : Fin 2) :
    Integrable (fun x => (Γ.matrixDensity x a a).re) ∧ (∫ x, (Γ.matrixDensity x a a).re) = Γ.spinNumber a := by
  let f := fun k x => Γ.weight k * ((Γ.component k).matrixDensity x a a).re
  have hd : (fun x => (Γ.matrixDensity x a a).re) =ᵐ[volume] fun x => ∑' k, f k x := by
    filter_upwards [Γ.density_summable] with x h
    exact (show HasSum (fun k => f k x) ((Γ.matrixDensity x a a).re) by
      simpa only [f, matrixDensity, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using Complex.hasSum_re (h a a).hasSum).tsum_eq.symm
  have hi (k : ℕ) : Integrable (f k) := ((Γ.component k).integral_spinDensity a).1.const_mul _
  have hm (k : ℕ) : (∫ x, f k x) = Γ.weight k * (Γ.component k).spinNumber a := by
    simp only [f, integral_const_mul, ((Γ.component k).integral_spinDensity a).2]
  have hnorm (k : ℕ) (x : Position) : ‖f k x‖ = f k x :=
    Real.norm_of_nonneg (mul_nonneg (Γ.weight_nonneg k) ((Γ.component k).diag_nonneg a x))
  have hsum : Summable (fun k => ∫ x, ‖f k x‖) := by simpa only [hnorm, hm] using Γ.spinNumber_summable a
  have hval : (∫ x, (Γ.matrixDensity x a a).re) = Γ.spinNumber a := by
    rw [integral_congr_ae hd, ← integral_tsum_of_summable_integral_norm hi hsum]
    simp only [spinNumber, hm]
  refine ⟨?_, hval⟩
  by_cases hz : Γ.spinNumber a = 0
  · have hk (k : ℕ) : f k =ᵐ[volume] 0 := by
      have hpos (x) : 0 ≤ f k x := mul_nonneg (Γ.weight_nonneg k) ((Γ.component k).diag_nonneg a x)
      have hl := (Γ.spinNumber_summable a).le_tsum k (fun j _ => 
        mul_nonneg (Γ.weight_nonneg j) ((Γ.component j).spinNumber_nonneg a))
      change _ ≤ Γ.spinNumber a at hl
      exact (integral_eq_zero_iff_of_nonneg hpos (hi k)).1
        (le_antisymm ((hm k).le.trans (hl.trans_eq hz)) (integral_nonneg hpos))
    apply (integrable_zero _ _ _).congr
    apply Filter.EventuallyEq.symm (hd.trans ?_)
    filter_upwards [ae_all_iff.mpr hk] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    simp [hx]
  · exact Integrable.of_integral_ne_zero (hval.trans_ne hz)

theorem MixedState.spinNumber_of_cutoff {Γ : MixedState} {f : Position → ℝ} {A : SpinMatrix}
    (rep : feasible (fun x => (f x : ℂ) • A) Γ) (a : Fin 2) :
    Γ.spinNumber a = (A a a).re * ∫ x, f x := by
  rw [← (Γ.integral_spinDensity a).2]
  have h : (fun x => (Γ.matrixDensity x a a).re) =ᵐ[volume] fun x => f x * (A a a).re :=
    rep.mono fun x hx => by simp [hx, Matrix.smul_apply]
  rw [integral_congr_ae h, integral_mul_const, mul_comm]

theorem MixedState.spinNumber_of_spiral_zero {Γ : MixedState} (D : SSW.DomainSequence) (A : SpinMatrix) (n : ℕ)
    (rep : feasible (D.spiralField A n 0) Γ) (a : Fin 2) :
    Γ.spinNumber a = (A a a).re * D.vol n := by
  apply (Γ.spinNumber_of_cutoff (f := D.cutoff n) (A := A) (by
    exact rep.mono fun x hx => hx.trans (SSW.cutoffSpiral_zero_wavevector _ _ _)) a).trans
  rw [D.cutoff_mass]

end TSGA.ManyBody
