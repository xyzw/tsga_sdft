import TSGA.EnsembleTwist
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Cauchy bounds for the physical spin current

Apply a spin-dependent boost at every real amplitude to the same ensemble.
The kinetic energy stays nonnegative. The discriminant of its quadratic
polynomial controls every linear combination of the two spin currents.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory
open scoped InnerProductSpace

/-- A spin-dependent velocity probes the two population momenta. The
coefficient on the right is the exact quadratic kinetic cost of this test. -/
theorem MixedState.spinMomentum_cauchy (Γ : MixedState) (v : Fin 2 → Position) :
    (∑ a, ⟪v a, Γ.spinMomentum a⟫_ℝ)^2 ≤ Γ.kinetic*(∑ a, ‖v a‖^2*Γ.spinNumber a) := by
  let p := ∑ a, ⟪v a, Γ.spinMomentum a⟫_ℝ
  let c := ∑ a, ‖v a‖^2*Γ.spinNumber a
  have h (t : ℝ) : 0 ≤ c*(t*t)+(2*p)*t+Γ.kinetic := by
    have ht := (Γ.twist (fun a => t • v a)).kinetic_nonneg
    rw [Γ.kinetic_twist] at ht
    apply ht.trans_eq
    simp only [p,c,Fin.sum_univ_two,real_inner_smul_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hdisc := discrim_le_zero h
  unfold discrim at hdisc
  change p^2 ≤ Γ.kinetic*c
  nlinarith only [hdisc]

theorem MixedState.axialCurrent_cauchy (Γ : MixedState) (q : Position) :
    ⟪q,Γ.axialCurrent⟫_ℝ^2 ≤ ‖q‖^2*(Γ.spinNumber 0 + Γ.spinNumber 1)*Γ.kinetic := by
  let v : Fin 2 → Position := fun a => if a = 0 then q else -q
  have h := Γ.spinMomentum_cauchy v
  simp only [v,Fin.sum_univ_two,ite_true,ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),inner_neg_left,norm_neg] at h
  rw [MixedState.axialCurrent,inner_sub_right,sub_eq_add_neg]
  exact h.trans_eq (by ring)

/-- A spin population of zero carries zero momentum. -/
theorem MixedState.spinMomentum_eq_zero_of_empty (Γ : MixedState) {a : Fin 2}
    (h : Γ.spinNumber a = 0) : Γ.spinMomentum a = 0 := by
  let p := Γ.spinMomentum a
  let v := fun j : Fin 2 => if j = a then p else 0
  have hc := Γ.spinMomentum_cauchy v
  have hp : (∑ j, ⟪v j,Γ.spinMomentum j⟫_ℝ) = ‖p‖^2 := by
    rw [Finset.sum_eq_single a]
    · simp [v,p]
    · intro j _ hja
      simp [v,hja]
    · simp
  have hq : (∑ j, ‖v j‖^2*Γ.spinNumber j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = a <;> simp [v,hj,h]
  rw [hp,hq,mul_zero] at hc
  apply norm_eq_zero.mp
  change ‖p‖ = 0
  exact sq_eq_zero_iff.mp (sq_eq_zero_iff.mp (le_antisymm hc (sq_nonneg _)))

/-- In the finite spiral frame, dividing the integrated current by the
volume gives the Cauchy bound with the actual cutoff charge. -/
theorem MixedState.cutoff_current_cauchy {Γ : MixedState} {f : Position → ℝ} {A : SpinMatrix}
    {V : ℝ} (hV : 0 < V) (mass : (∫ x, f x) = V)
    (rep : feasible (fun x => (f x : ℂ) • A) Γ) (q : Position) :
    (⟪q,Γ.axialCurrent⟫_ℝ / V)^2 ≤ ‖q‖^2*A.trace.re*(Γ.kinetic / V) := by
  have h := Γ.axialCurrent_cauchy q
  rw [Γ.spinNumber_of_cutoff rep 0,Γ.spinNumber_of_cutoff rep 1,mass] at h
  rw [Matrix.trace_fin_two,Complex.add_re,div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hV)).mpr
  exact h.trans_eq (by field_simp)

end TSGA.ManyBody
