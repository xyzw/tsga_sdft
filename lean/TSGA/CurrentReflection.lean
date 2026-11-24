import TSGA.StateReflection
import TSGA.WaveCurrent
import TSGA.CoulombGas

/-! # Zero-current ensembles on the reference balls

Spatial inversion reverses both spin momenta. Equal mixing at an even
prescribed density gives an ensemble with the original energy and zero
momentum in each spin channel.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW

@[simp] theorem Wave.spinMomentum_reflect {n : ℕ} (ψ : Wave n) (a : Fin 2) :
    ψ.reflect.spinMomentum a = -ψ.spinMomentum a := by
  ext j
  change spinSum a _ = -spinSum a _
  have hr (s : Spins n) (i : Fin n) :
      (∫ x, currentPair (ψ.reflect.value s x) (ψ.reflect.gradient s x i j)) =
        (-1:ℝ) * ∫ x, currentPair (ψ.value s x) (ψ.gradient s x i j) := by
    simp only [reflect,currentPair,mul_neg,Complex.neg_im,integral_neg,neg_one_mul]
    exact congrArg Neg.neg (sector_integral_neg (fun x => currentPair (ψ.value s x) (ψ.gradient s x i j)))
  simp_rw [hr]
  rw [spinSum_mul,neg_one_mul]

@[simp] theorem PureState.spinMomentum_reflect (s : PureState) (a : Fin 2) :
    s.reflect.spinMomentum a = -s.spinMomentum a := by
  cases s <;> simp [reflect,spinMomentum]

@[simp] theorem MixedState.spinMomentum_reflect (Γ : MixedState) (a : Fin 2) :
    Γ.reflect.spinMomentum a = -Γ.spinMomentum a := by
  ext j
  change (∑' m, Γ.weight m * ((Γ.component m).reflect.spinMomentum a j)) =
    -(∑' m, Γ.weight m * (Γ.component m).spinMomentum a j)
  simp only [PureState.spinMomentum_reflect, PiLp.neg_apply, mul_neg, tsum_neg]

theorem MixedState.spinMomentum_mix (Γ Λ : MixedState) {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hs : p+r=1) (a : Fin 2) :
    (Γ.mix Λ p r hp hr hs).spinMomentum a = p • Γ.spinMomentum a + r • Λ.spinMomentum a := by
  ext j
  exact (Γ.mix_expectation Λ hp hr hs (fun s => s.spinMomentum a j)
    (Γ.spinMomentum_summable a j).hasSum (Λ.spinMomentum_summable a j).hasSum).tsum_eq

theorem MixedState.zero_currents_of_even {F : Position → SpinMatrix} (Γ : MixedState)
    (rep : feasible F Γ) (even : ∀ x, F (-x) = F x) :
    ∃ Λ : MixedState, feasible F Λ ∧ Λ.kinetic = Γ.kinetic ∧
      Λ.interaction = Γ.interaction ∧ ∀ a, Λ.spinMomentum a = 0 := by
  let t : ℝ := 1/2
  have ht : 0 ≤ t := by norm_num [t]
  have hs : t+t=1 := by norm_num [t]
  let Λ := Γ.mix Γ.reflect t t ht ht hs
  obtain ⟨hk, hw, hd⟩ := Γ.mix_laws Γ.reflect ht ht hs
  have hneg : ∀ᵐ x, Γ.matrixDensity (-x) = F (-x) :=
    (LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.quasiMeasurePreserving.tendsto_ae rep
  refine ⟨Λ,hd.trans ?_,?_,?_,?_⟩
  · filter_upwards [rep,hneg] with x hx hn
    rw [density_reflect, hx, hn, even, ← add_smul, hs, one_smul]
  · change (Γ.mix Γ.reflect t t ht ht hs).kinetic = _
    rw [hk, kinetic_reflect, ← add_mul, hs, one_mul]
  · change (Γ.mix Γ.reflect t t ht ht hs).interaction = _
    rw [hw, interaction_reflect, ← add_mul, hs, one_mul]
  · intro a
    simp [Λ,spinMomentum_mix]

theorem SpiralState.zero_currents_on_balls (η : Mollifier) {M : SpinMatrix} {n : ℕ}
    (s : SpiralState (DomainSequence.balls η) M n 0) :
    ∃ t : SpiralState (DomainSequence.balls η) M n 0,
      t.value = s.value ∧ ∀ a, t.val.spinMomentum a = 0 := by
  have he (x : Position) : (DomainSequence.balls η).spiralField M n 0 (-x) =
      (DomainSequence.balls η).spiralField M n 0 x := by
    simp only [DomainSequence.spiralField,cutoffSpiral_zero_wavevector,ball_cutoff_even]
  obtain ⟨Λ,hΛ,hk,hw,hj⟩ := s.val.zero_currents_of_even s.property he
  exact ⟨⟨Λ,hΛ⟩,by simp [value,hk,hw],hj⟩

end TSGA.ManyBody
