import TSGA.EnsembleTwist
import TSGA.CoulombGas

/-! # Uniform boosts of the Coulomb constrained search

A uniform momentum shift in both spin channels preserves the entire spin
density. At fixed cutoff its linear and quadratic energy coefficients are
the total momentum and the integrated charge, respectively.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization
open scoped InnerProductSpace

def MixedState.boost (Γ : MixedState) (k : Position) : MixedState := Γ.twist (fun _ => k)

@[simp] theorem MixedState.density_boost (Γ : MixedState) (k x : Position) :
    (Γ.boost k).matrixDensity x = Γ.matrixDensity x := by
  ext i j
  simp [boost,density_twist]

@[simp] theorem MixedState.interaction_boost (Γ : MixedState) (k : Position) :
    (Γ.boost k).interaction = Γ.interaction := Γ.interaction_twist _

theorem MixedState.kinetic_boost (Γ : MixedState) (k : Position) :
    (Γ.boost k).kinetic = Γ.kinetic + 2*⟪k,Γ.momentum⟫_ℝ +
      ‖k‖^2*(Γ.spinNumber 0 + Γ.spinNumber 1) := by
  rw [boost, kinetic_twist, Fin.sum_univ_two, momentum, inner_add_right]
  ring

theorem MixedState.momentum_boost (Γ : MixedState) (k : Position) :
    (Γ.boost k).momentum = Γ.momentum + (Γ.spinNumber 0 + Γ.spinNumber 1) • k := by
  simp only [momentum,boost,spinMomentum_twist,add_smul]
  abel

theorem MixedState.axialCurrent_boost (Γ : MixedState) (k : Position) :
    (Γ.boost k).axialCurrent = Γ.axialCurrent + (Γ.spinNumber 0 - Γ.spinNumber 1) • k := by
  simp only [axialCurrent,boost,spinMomentum_twist,sub_smul]
  abel

@[simp] theorem MixedState.boost_undo (Γ : MixedState) (k : Position) :
    (Γ.boost k).boost (-k) = Γ := by
  rw [boost,boost,twist_add,show (fun _ : Fin 2 => k)+(fun _ => -k) = 0 by ext a j; simp,twist_zero]

/-- Boosting gives a bijection for every prescribed spin-density field. -/
def MixedState.boostEquiv (F : Position → SpinMatrix) (k : Position) :
    {Γ // feasible F Γ} ≃ {Γ // feasible F Γ} where
  toFun s := ⟨s.val.boost k, s.property.mono fun x hx => (s.val.density_boost k x).trans hx⟩
  invFun s := ⟨s.val.boost (-k), s.property.mono fun x hx => (s.val.density_boost (-k) x).trans hx⟩
  left_inv s := Subtype.ext (s.val.boost_undo k)
  right_inv s := Subtype.ext (by simpa only [neg_neg] using s.val.boost_undo (-k))

theorem SpiralState.charge_spinNumber {D : DomainSequence} {M : SpinMatrix} {n : ℕ}
    (s : SpiralState D M n 0) : s.val.spinNumber 0 + s.val.spinNumber 1 = M.trace.re * D.vol n := by
  rw [s.val.spinNumber_of_spiral_zero D M n s.prop,s.val.spinNumber_of_spiral_zero D M n s.prop,
    Matrix.trace_fin_two,Complex.add_re,add_mul]

theorem SpiralState.axial_spinNumber {D : DomainSequence} {M : SpinMatrix} {n : ℕ}
    (s : SpiralState D M n 0) :
    s.val.spinNumber 0 - s.val.spinNumber 1 = thirdMagnetization M * D.vol n := by
  rw [s.val.spinNumber_of_spiral_zero D M n s.prop,s.val.spinNumber_of_spiral_zero D M n s.prop,
    thirdMagnetization,sub_mul]

theorem SpiralState.boost_energy {D : DomainSequence} {M : SpinMatrix} {n : ℕ}
    (s : SpiralState D M n 0) (k : Position) :
    SpiralState.value (D := D) (M := M) (n := n) (q := 0) (MixedState.boostEquiv (D.spiralField M n 0) k s) =
      s.value + 2*⟪k,s.val.momentum⟫_ℝ + ‖k‖^2*(M.trace.re*D.vol n) := by
  simp only [value,MixedState.boostEquiv,Equiv.coe_fn_mk,MixedState.interaction_boost,
    MixedState.kinetic_boost,s.charge_spinNumber]
  ring

end TSGA.ManyBody
