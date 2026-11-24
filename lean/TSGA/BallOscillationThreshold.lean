import TSGA.BallActiveMorrey
import TSGA.BallDensityRepresentative

/-! # Passing the large-oscillation test to the global root

The manuscript tests the θ-power in every regime. On the global-root
branch, failure of that test forces the root to fail the smaller threshold
κ/(pθ). The argument compares the spectra at the actual maximum charge.
-/

noncomputable section

namespace TSGA.Localization

open MeasureTheory Set Metric

theorem smallPowerOscillation_of_root {p θ κ R : ℝ} {D N : Density} {c : Position}
    (hp : 0 < p) (hu : 1/p ≤ θ) (_hκ : 0 < κ) (hND : N.matrix =ᵐ[volume] D.matrix)
    (hc : Continuous N.matrix) (cont : ∀ a : ℝ, 0 < a → Continuous (N.power a))
    (hR : 0 < R) :
    SmallPowerOscillation D (1/p) (κ/(p*θ)) R c → SmallPowerOscillation D θ κ R c := by
  have ha : 0 < 1 / p := one_div_pos.mpr hp
  have hθ := ha.trans_le hu
  obtain ⟨z, _, hz, cap⟩ := exists_charge_max_on_ball (c := c) hND hc hR
  let r := N.charge z
  have hr : 0 ≤ r := N.charge_nonneg z
  have hscale : r^(θ-1/p) * r^(1/p) = r^θ := by
    rcases hr.eq_or_lt with hz | hr'
    · rw [← hz, Real.zero_rpow ha.ne', mul_zero, Real.zero_rpow hθ.ne']
    · rw [← Real.rpow_add hr', sub_add_cancel]
  intro small
  have bound := (smallPowerOscillation_iff_closedBall hND hc (cont _ ha) hR).mp small
  apply (smallPowerOscillation_iff_closedBall hND hc (cont _ hθ) hR).mpr
  intro x hx y hy
  have s := bound x hx y hy
  rw [← hz] at s ⊢
  have mat := matrix_power_oscillation (N.positive x) (N.positive y) ha hu hr (cap x hx) (cap y hy)
  rw [div_div_eq_mul_div, div_one] at mat
  calc
    _ ≤ (θ*p*r^(θ-1/p)) * hilbertSchmidt (N.power (1/p) x - N.power (1/p) y) := mat
    _ ≤ (θ*p*r^(θ-1/p)) * (κ/(p*θ)*r^(1/p)) :=
      mul_le_mul_of_nonneg_left s (mul_nonneg (mul_nonneg hθ.le hp.le) (Real.rpow_nonneg hr _))
    _ = κ * (r^(θ-1/p) * r^(1/p)) := by field_simp [hp.ne', hθ.ne']
    _ = _ := by rw [hscale]

end TSGA.Localization
