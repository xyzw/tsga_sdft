import TSGA.WaveTwistCurrent
import TSGA.SpinPopulation
import TSGA.AxialKinetic

/-! # Spin-dependent boosts of Coulomb ensembles

The squared momentum shifts are controlled by the expected particle number.
Thus twisting an entire countable ensemble preserves its finite-energy
domain. Both particle currents and the kinetic energy can be summed exactly.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped InnerProductSpace

def PureState.twist (t : PureState) (v : Fin 2 → Position) : PureState := match t with
  | .vacuum => .vacuum
  | .occupied ψ => .occupied (ψ.twist v)

@[simp] theorem PureState.particles_twist (t : PureState) (v : Fin 2 → Position) :
    (t.twist v).particles = t.particles := by cases t <;> rfl
@[simp] theorem PureState.interaction_twist (t : PureState) (v : Fin 2 → Position) :
    (t.twist v).interaction = t.interaction := by cases t <;> simp [interaction,twist]
@[simp] theorem PureState.twist_zero (t : PureState) : t.twist 0 = t := by cases t <;> simp [twist]
theorem PureState.twist_add (t : PureState) (v w : Fin 2 → Position) : (t.twist v).twist w = t.twist (v+w) := by
  cases t <;> simp [twist,Wave.twist_add]
theorem PureState.density_twist (t : PureState) (v : Fin 2 → Position) (x : Position) (i j : Fin 2) :
    (t.twist v).matrixDensity x i j = phaseFactor (⟪v i,x⟫_ℝ-⟪v j,x⟫_ℝ) * t.matrixDensity x i j := by
  cases t with
  | vacuum => simp [twist,matrixDensity]
  | occupied ψ => exact ψ.matrixDensity_twist v x i j

theorem PureState.kinetic_twist (t : PureState) (v : Fin 2 → Position) :
    (t.twist v).kinetic = t.kinetic + ∑ a, (2*⟪v a,t.spinMomentum a⟫_ℝ + ‖v a‖^2*t.spinNumber a) := by
  cases t with
  | vacuum => simp [twist,kinetic,spinMomentum,spinNumber]
  | occupied ψ => exact ψ.kinetic_twist v

theorem PureState.spinMomentum_twist (t : PureState) (v : Fin 2 → Position) (a : Fin 2) :
    (t.twist v).spinMomentum a = t.spinMomentum a + t.spinNumber a • v a := by
  cases t with
  | vacuum => simp [twist,spinMomentum,spinNumber]
  | occupied ψ => exact ψ.spinMomentum_twist v a

theorem PureState.kinetic_twist_le (t : PureState) (v : Fin 2 → Position) :
    (t.twist v).kinetic ≤ 2*t.kinetic + 2*(∑ a, ‖v a‖^2)*(t.particles : ℝ) := by
  cases t with
  | vacuum => simp [twist,particles,kinetic]
  | occupied ψ => exact ψ.kinetic_twist_le v

def MixedState.twist (Γ : MixedState) (v : Fin 2 → Position) : MixedState where
  component m := (Γ.component m).twist v
  weight := Γ.weight
  weight_nonneg := Γ.weight_nonneg
  normalized := Γ.normalized
  particles_summable := by simpa using Γ.particles_summable
  kinetic_summable := by
    let c := 2*(∑ a, ‖v a‖^2)
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (Γ.weight_nonneg _) ((Γ.component m).twist v).kinetic_nonneg)
      _ ((Γ.kinetic_summable.mul_left 2).add (Γ.particles_summable.mul_left c))
    intro m
    exact (mul_le_mul_of_nonneg_left ((Γ.component m).kinetic_twist_le v) (Γ.weight_nonneg m)).trans_eq (by dsimp [c]; ring)
  interaction_summable := by simpa using Γ.interaction_summable
  density_summable := by
    filter_upwards [Γ.density_summable] with x hx
    intro i j
    simpa only [PureState.density_twist,mul_left_comm (Γ.weight _ : ℂ)] using
      (hx i j).mul_left (phaseFactor (⟪v i,x⟫_ℝ-⟪v j,x⟫_ℝ))

@[simp] theorem MixedState.twist_zero (Γ : MixedState) : Γ.twist 0 = Γ := by cases Γ; simp [twist]
theorem MixedState.twist_add (Γ : MixedState) (v w : Fin 2 → Position) :
    (Γ.twist v).twist w = Γ.twist (v+w) := by cases Γ; simp [twist,PureState.twist_add]
@[simp] theorem MixedState.interaction_twist (Γ : MixedState) (v : Fin 2 → Position) :
    (Γ.twist v).interaction = Γ.interaction := by simp [interaction,twist]
theorem MixedState.density_twist (Γ : MixedState) (v : Fin 2 → Position) (x : Position) (i j : Fin 2) :
    (Γ.twist v).matrixDensity x i j = phaseFactor (⟪v i,x⟫_ℝ-⟪v j,x⟫_ℝ) * Γ.matrixDensity x i j := by
  simp only [matrixDensity, twist, PureState.density_twist, mul_left_comm (Γ.weight _ : ℂ),tsum_mul_left]

theorem MixedState.spinMomentum_twist (Γ : MixedState) (v : Fin 2 → Position) (a : Fin 2) :
    (Γ.twist v).spinMomentum a = Γ.spinMomentum a + Γ.spinNumber a • v a := by
  ext j
  change (∑' m, Γ.weight m*(((Γ.component m).twist v).spinMomentum a j)) =
    Γ.spinMomentum a j + Γ.spinNumber a*v a j
  have h := ((Γ.spinMomentum_summable a j).hasSum.add ((Γ.spinNumber_summable a).hasSum.mul_right (v a j)))
  apply HasSum.tsum_eq (h.congr_fun _)
  intro m
  rw [PureState.spinMomentum_twist]
  change Γ.weight m*((Γ.component m).spinMomentum a j+(Γ.component m).spinNumber a*v a j) = _
  ring

private theorem inner_momentum_sum (Γ : MixedState) (a : Fin 2) (v : Position) :
    HasSum (fun m => Γ.weight m * ⟪v,(Γ.component m).spinMomentum a⟫_ℝ) ⟪v,Γ.spinMomentum a⟫_ℝ := by
  have h (j : Fin 3) : HasSum (fun m => Γ.weight m * (Γ.component m).spinMomentum a j * v j)
      (Γ.spinMomentum a j * v j) := (Γ.spinMomentum_summable a j).hasSum.mul_right _
  simpa only [PiLp.inner_apply, Real.inner_apply, Finset.mul_sum, mul_assoc, mul_comm (v _)] using
    hasSum_sum (s := Finset.univ) (fun j _ => h j)

theorem MixedState.kinetic_twist (Γ : MixedState) (v : Fin 2 → Position) :
    (Γ.twist v).kinetic = Γ.kinetic + ∑ a, (2*⟪v a,Γ.spinMomentum a⟫_ℝ + ‖v a‖^2*Γ.spinNumber a) := by
  have h (a : Fin 2) := ((inner_momentum_sum Γ a (v a)).mul_left 2).add
    ((Γ.spinNumber_summable a).hasSum.mul_left (‖v a‖^2))
  apply HasSum.tsum_eq ((Γ.kinetic_summable.hasSum.add (hasSum_sum (s := Finset.univ) fun a _ => h a)).congr_fun _)
  intro m
  change Γ.weight m*((Γ.component m).twist v).kinetic = _
  rw [PureState.kinetic_twist,mul_add,Finset.mul_sum]
  apply congrArg (fun u : ℝ => Γ.weight m * (Γ.component m).kinetic + u)
  apply Finset.sum_congr rfl
  intro a _
  ring

def MixedState.momentum (Γ : MixedState) : Position := Γ.spinMomentum 0 + Γ.spinMomentum 1
def MixedState.axialCurrent (Γ : MixedState) : Position := Γ.spinMomentum 0 - Γ.spinMomentum 1

end TSGA.ManyBody
