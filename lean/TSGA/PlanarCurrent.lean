import TSGA.CurrentReflection
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Zero current for any coplanar spin density

Complex conjugation reverses both orbital momenta. For magnetizations in
a fixed plane through the third axis, one constant axial spin rotation
restores the prescribed density. Averaging the two states keeps the energy.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped ComplexConjugate ComplexOrder

def Wave.conjugate {n : ℕ} (ψ : Wave n) : Wave n where
  value s x := conj (ψ.value s x)
  gradient s x i j := conj (ψ.gradient s x i j)
  antisymmetric π s := (ψ.antisymmetric π s).mono fun x hx => by rw [hx]; simp
  square_integrable s := Complex.conjCLE.toContinuousLinearMap.comp_memLp' (ψ.square_integrable s)
  gradient_L2 s i j := Complex.conjCLE.toContinuousLinearMap.comp_memLp' (ψ.gradient_L2 s i j)
  normalized := by simpa only [Complex.norm_conj] using ψ.normalized
  weak_gradient s i j f hf hc := by
    have hw := congrArg (starRingEnd ℂ) (ψ.weak_gradient s i j f hf hc)
    simpa only [map_neg,← integral_conj,Complex.real_smul,map_mul,Complex.conj_ofReal] using hw
  interaction_integrable s := by simpa only [Complex.norm_conj] using ψ.interaction_integrable s

@[simp] theorem Wave.kinetic_conjugate {n : ℕ} (ψ : Wave n) : ψ.conjugate.kinetic = ψ.kinetic := by
  simp [kinetic,conjugate]
@[simp] theorem Wave.interaction_conjugate {n : ℕ} (ψ : Wave n) : ψ.conjugate.interaction = ψ.interaction := by
  simp [interaction,conjugate]
@[simp] theorem Wave.density_conjugate {n : ℕ} (ψ : Wave (n+1)) (x : Position) :
    ψ.conjugate.matrixDensity x = (ψ.matrixDensity x).map (starRingEnd ℂ) := by
  ext i j
  simp only [matrixDensity,conjugate,Matrix.map_apply,map_mul,map_natCast,map_sum,← integral_conj]

@[simp] theorem Wave.spinMomentum_conjugate {n : ℕ} (ψ : Wave n) (a : Fin 2) :
    ψ.conjugate.spinMomentum a = -ψ.spinMomentum a := by
  ext j
  change spinSum a _ = -spinSum a _
  have h (u z : ℂ) : currentPair (conj u) (conj z) = (-1:ℝ)*currentPair u z := by
    change (conj (conj u) * conj z).im = _
    rw [← map_mul,Complex.conj_im,neg_one_mul]
    rfl
  simp only [conjugate,h,integral_const_mul]
  rw [spinSum_mul,neg_one_mul]
  
@[simp] theorem Wave.spinMomentum_rotateSpin {n : ℕ} (ψ : Wave n) (b : ℝ) (a : Fin 2) :
    (ψ.rotateSpin b).spinMomentum a = ψ.spinMomentum a := by
  ext j
  have h (s : Spins n) (x : Space n) (i : Fin n) :
      currentPair ((ψ.rotateSpin b).value s x) ((ψ.rotateSpin b).gradient s x i j) =
        currentPair (ψ.value s x) (ψ.gradient s x i j) := by
    unfold rotateSpin
    apply (show ∀ (c : ℂ), ‖c‖=1 → currentPair (c*ψ.value s x) (c*ψ.gradient s x i j) = _ from
      fun c hc => by simpa using currentPair_phase (ψ.value s x) (ψ.gradient s x i j) c 0 hc)
    change ‖phaseFactor _‖ = 1
    simp [phaseFactor,Complex.norm_exp]
  simp only [spinMomentum_apply,h]

def PureState.conjugate : PureState → PureState
  | .vacuum => .vacuum
  | .occupied ψ => .occupied ψ.conjugate

@[simp] theorem PureState.conjugate_kinetic (s : PureState) : s.conjugate.kinetic = s.kinetic := by
  cases s <;> simp [conjugate,kinetic]
@[simp] theorem PureState.conjugate_interaction (s : PureState) : s.conjugate.interaction = s.interaction := by
  cases s <;> simp [conjugate,interaction]
@[simp] theorem PureState.conjugate_particles (s : PureState) : s.conjugate.particles = s.particles := by cases s <;> rfl
@[simp] theorem PureState.conjugate_density (s : PureState) (x : Position) :
    s.conjugate.matrixDensity x = (s.matrixDensity x).map (starRingEnd ℂ) := by
  cases s <;> ext i j <;> simp [conjugate,matrixDensity]
@[simp] theorem PureState.conjugate_spinMomentum (s : PureState) (a : Fin 2) :
    s.conjugate.spinMomentum a = -s.spinMomentum a := by cases s <;> simp [conjugate,spinMomentum]
@[simp] theorem PureState.spinMomentum_rotateSpin (s : PureState) (b : ℝ) (a : Fin 2) :
    (s.rotateSpin b).spinMomentum a = s.spinMomentum a := by cases s <;> simp [rotateSpin,spinMomentum]

def MixedState.conjugate (Γ : MixedState) : MixedState where
  component m := (Γ.component m).conjugate
  weight := Γ.weight
  weight_nonneg := Γ.weight_nonneg
  normalized := Γ.normalized
  particles_summable := by simpa using Γ.particles_summable
  kinetic_summable := by simpa using Γ.kinetic_summable
  interaction_summable := by simpa using Γ.interaction_summable
  density_summable := by
    filter_upwards [Γ.density_summable] with x h
    intro i j
    simpa only [PureState.conjugate_density,Matrix.map_apply,map_mul,Complex.conj_ofReal] using
      (Complex.summable_conj.mpr (h i j))

@[simp] theorem MixedState.kinetic_conjugate (Γ : MixedState) : Γ.conjugate.kinetic = Γ.kinetic := by simp [kinetic,conjugate]
@[simp] theorem MixedState.interaction_conjugate (Γ : MixedState) : Γ.conjugate.interaction = Γ.interaction := by simp [interaction,conjugate]
@[simp] theorem MixedState.density_conjugate (Γ : MixedState) (x : Position) :
    Γ.conjugate.matrixDensity x = (Γ.matrixDensity x).map (starRingEnd ℂ) := by
  ext i j
  simp only [matrixDensity,conjugate,PureState.conjugate_density, Matrix.map_apply,Complex.conj_tsum,map_mul,Complex.conj_ofReal]
@[simp] theorem MixedState.spinMomentum_conjugate (Γ : MixedState) (a : Fin 2) :
    Γ.conjugate.spinMomentum a = -Γ.spinMomentum a := by
  ext j
  simp only [spinMomentum_apply,conjugate,PureState.conjugate_spinMomentum,PiLp.neg_apply,mul_neg,tsum_neg]
@[simp] theorem MixedState.spinMomentum_rotateSpin (Γ : MixedState) (b : ℝ) (a : Fin 2) :
    (Γ.rotateSpin b).spinMomentum a = Γ.spinMomentum a := by
  ext j
  simp [spinMomentum_apply,rotateSpin]

theorem MixedState.zero_currents_of_planar {F : Position → SpinMatrix} (Γ : MixedState) (rep : feasible F Γ)
    (planar : ∃ α : ℝ, ∀ᵐ x, rotate α ((F x).map (starRingEnd ℂ)) = F x) :
    ∃ Λ : MixedState, feasible F Λ ∧ Λ.kinetic = Γ.kinetic ∧ Λ.interaction = Γ.interaction ∧
      ∀ a, Λ.spinMomentum a = 0 := by
  obtain ⟨α, hα⟩ := planar
  let Λ := Γ.conjugate.rotateSpin α
  have rt : feasible F Λ := by
    filter_upwards [rep,hα] with x hx hy
    simpa only [Λ,rotate_matrix,density_conjugate,hx] using hy
  have ht : (0:ℝ) ≤ 1/2 := by norm_num
  have hs : (1/2:ℝ)+1/2 = 1 := by norm_num
  obtain ⟨hk,hw,hd⟩ := Γ.mix_laws Λ ht ht hs
  refine ⟨_,hd.trans ?_,?_,?_,?_⟩
  · filter_upwards [rep,rt] with x hx hy
    rw [hx,hy,← add_smul,hs,one_smul]
  · rw [hk]
    simp only [Λ,rotate_kinetic,kinetic_conjugate,← add_mul,hs,one_mul]
  · rw [hw]
    simp only [Λ,rotate_interaction,interaction_conjugate,← add_mul,hs,one_mul]
  · intro a
    simp [spinMomentum_mix,Λ]

/-- Every scalar cutoff of a fixed Hermitian spin matrix is coplanar.
Twice the phase of its lower off-diagonal entry restores the matrix after
complex conjugation, also when that entry vanishes. -/
theorem planar_cutoff (f : Position → ℝ) {A : SpinMatrix} (hA : A.IsHermitian) :
    ∃ α : ℝ, ∀ᵐ x, rotate α (((f x : ℂ) • A).map (starRingEnd ℂ)) = (f x : ℂ) • A := by
  let z := A 1 0
  let β := z.arg
  have polar : (‖z‖ : ℂ) * phaseFactor β = z := Complex.norm_mul_exp_arg_mul_I z
  have cphase (γ : ℝ) : conj (phaseFactor γ) = phaseFactor (-γ) := star_phaseFactor γ
  have pc : (‖z‖ : ℂ) * phaseFactor (-β) = conj z := by
    simpa only [map_mul,cphase,Complex.conj_ofReal] using congrArg (starRingEnd ℂ) polar
  have bot : phaseFactor (2*β) * conj z = z := calc
    _ = (‖z‖ : ℂ) * (phaseFactor (2*β) * phaseFactor (-β)) := by rw [← pc]; ring
    _ = z := by rw [← phaseFactor_add,show 2*β + -β = β by ring,polar]
  have off : conj z = A 0 1 := hA.apply 0 1
  have top : phaseFactor (-(2*β)) * conj (A 0 1) = A 0 1 := by
    rw [← off]
    simpa only [map_mul,cphase] using congrArg (starRingEnd ℂ) bot
  have entry (i j : Fin 2) : phaseFactor (axialWeight i j * (2*β)) * conj (A i j) = A i j := by
    fin_cases i <;> fin_cases j
    · simpa [axialWeight] using hA.apply 0 0
    · norm_num [axialWeight]
      exact top
    · norm_num [axialWeight]
      exact bot
    · simpa [axialWeight] using hA.apply 1 1
  refine ⟨2*β,ae_of_all _ fun x => ?_⟩
  ext i j
  simp only [rotate_by_entry,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul,Complex.conj_ofReal]
  rw [mul_left_comm,entry]

end TSGA.ManyBody
