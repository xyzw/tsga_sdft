import TSGA.ReplacementScale

/-! # Residual-charge terms in the local Coulomb comparison

The bounded-charge island estimate contributes powers 3/2 and 2 of the
charge difference. Both are absorbed at the replacement exponent of
Proposition 4.16, before summing over tiles.
-/

noncomputable section
namespace TSGA.Localization

/-- The interpolation applies to the whole interval between the two residual
powers. V stands for ℓ³, and the input on Vωᵖ is the Morrey inequality. -/
theorem residual_charge_interpolation {m p θ ε r ω V L cap G : ℝ}
    (hp : 3 < p) (hθp : 2 ≤ θ*p) (hm : m ∈ Set.Icc (3/2:ℝ) 2)
    (hε : 0 < ε) (hr : 0 < r) (hV : 0 ≤ V) (hL : 0 ≤ L) (hcap₀ : 0 ≤ cap)
    (hω : 0 ≤ ω) (hsmall : ω ≤ r^θ) (hcap : cap ≤ L*(r^(1-θ)*ω)) (hmorrey : V*ω^p ≤ G) :
    let k := max p (3*θ*p-3)
    V*ε^(1-m)*cap^m ≤ L^m * (ε*V*(r+r^2) + ε^(1-k)*G) := by
  let k := max p (3*θ*p-3)
  let t := m/k
  let β := (m-θ*(p*t))/(1-t)
  have hk : p ≤ k := le_max_left ..
  have hk3 : 3*θ*p-3 ≤ k := le_max_right ..
  have hp' : 0 < p := by linarith
  have hk' := hp'.trans_le hk
  have hm' : 0 < m := by linarith [hm.1]
  have ht : 0 < t := div_pos hm' hk'
  have ht' : t < 1 := (div_lt_one hk').2 (by linarith [hm.2])
  have hmt : t*k = m := div_mul_cancel₀ _ hk'.ne'
  have hat : p*t ≤ m := by linarith only [mul_le_mul_of_nonneg_right hk ht.le,hmt]
  have hβ : β*(1-t) = m-θ*(p*t) := div_mul_cancel₀ _ (sub_pos.mpr ht').ne'
  have hβrange : β ∈ Set.Icc 1 2 := by
    constructor
    · apply (le_div_iff₀ (sub_pos.mpr ht')).2
      have h₁ : m*(θ*p-1) ≤ (m-1)*(3*θ*p-3) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hm.1) (show 0 ≤ θ*p-1 by linarith)]
      have h₂ := h₁.trans (mul_le_mul_of_nonneg_left hk3 (by linarith [hm.1]))
      apply (mul_le_mul_iff_left₀ hk').mp
      nlinarith only [h₂,hmt, congrArg (fun x => (θ*p)*x) hmt]
    · apply (div_le_iff₀ (sub_pos.mpr ht')).2
      nlinarith only [hm.2,mul_nonneg ht.le (sub_nonneg.mpr hθp)]
  let x := ω/r^θ
  have hx : 0 ≤ x := div_nonneg hω (Real.rpow_nonneg hr.le _)
  have hx1 : x ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hr _)).2 hsmall
  have hωx : x*r^θ=ω := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hr _).ne'
  have hxpow : x^m ≤ x^(p*t) := Real.rpow_le_rpow_of_exponent_ge' hx hx1 (mul_nonneg hp'.le ht.le) hat
  have cap : cap ≤ L*(r*x) := by
    have hrw : r^(1-θ)*r^θ = r := by rw [← Real.rpow_add hr, sub_add_cancel, Real.rpow_one]
    calc
      _ ≤ _ := hcap
      _ = L*((r^(1-θ)*r^θ)*x) := by rw [← hωx]; ring
      _ = _ := by rw [hrw]
  let X := ε^(1-k)*ω^p
  let Y := ε*r^β
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have heq : X^t * Y^(1-t) = ε^(1-m)*r^m*x^(p*t) := by
    dsimp only [X,Y]
    rw [Real.mul_rpow (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hω _),
      Real.mul_rpow hε.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hε.le,
      ← Real.rpow_mul hω, ← Real.rpow_mul hr.le, ← hωx, Real.mul_rpow hx (Real.rpow_nonneg hr.le _),
      ← Real.rpow_mul hr.le]
    calc
      _ = (ε^((1-k)*t)*ε^(1-t)) * (r^(θ*(p*t))*r^(β*(1-t))) * x^(p*t) := by ring
      _ = _ := by rw [← Real.rpow_add hε, ← Real.rpow_add hr, hβ,
        show (1-k)*t+(1-t)=1-m by linarith only [hmt], add_sub_cancel]
  have hy := Real.geom_mean_le_arith_mean2_weighted ht.le (sub_nonneg.mpr ht'.le) hX hY
    (by ring : t+(1-t)=1)
  have hy' : ε^(1-m)*r^m*x^(p*t) ≤ X+Y := by
    rw [← heq]
    exact hy.trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr ht'.le) hX, mul_nonneg ht.le hY])
  have hcap₀m := Real.rpow_le_rpow hcap₀ cap hm'.le
  rw [Real.mul_rpow hL (mul_nonneg hr.le hx), Real.mul_rpow hr.le hx] at hcap₀m
  have hx' := mul_le_mul_of_nonneg_left hxpow (mul_nonneg (Real.rpow_nonneg hε.le (1-m)) (Real.rpow_nonneg hr.le m))
  have hX' : V*X ≤ ε^(1-k)*G := by
    dsimp only [X]
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hmorrey (Real.rpow_nonneg hε.le _)
  have hY' : V*Y ≤ ε*V*(r+r^2) := by
    dsimp only [Y]
    rw [← mul_assoc, mul_comm V ε]
    exact mul_le_mul_of_nonneg_left (BulkRegime.density_power_le hr hβrange) (mul_nonneg hε.le hV)
  calc
    _ ≤ V*L^m*(ε^(1-m)*r^m*x^m) := by
      apply (mul_le_mul_of_nonneg_left hcap₀m (mul_nonneg hV (Real.rpow_nonneg hε.le _))).trans_eq
      ring
    _ ≤ V*L^m*(X+Y) := mul_le_mul_of_nonneg_left (hx'.trans hy') (mul_nonneg hV (Real.rpow_nonneg hL _))
    _ = L^m*(V*Y + V*X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hY' hX') (Real.rpow_nonneg hL _)

end TSGA.Localization
