import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Island radii and the bounded-density estimate in Appendix C -/

noncomputable section
namespace TSGA.Islands

/-- Taking v = ε/2 and δ = r^(-1/5)/D keeps all four fluctuation and
boundary coefficients bounded throughout 1 ≤ r ≤ ε^(-1/2). -/
theorem choose_island_width {ε r D : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1)
    (hr : 1 ≤ r) (hmax : ε*r^2 ≤ 1) (hD : 1 ≤ D) :
    let v := ε/2
    let δ := r^(-(1/5 : ℝ)) / D
    0 < v ∧ v ≤ 1/2 ∧ 0 < δ ∧ δ ≤ r/D ∧
    1/r*(1+δ⁻¹) ≤ 1+D ∧
    δ^3/r + v*r^2 + r^(1/3 : ℝ)*δ^(5/3 : ℝ) + δ^2 ≤ 4 := by
  let δ := r^(-(1/5 : ℝ)) / D
  have hr' : 0 < r := zero_lt_one.trans_le hr
  have hD' : 0 < D := zero_lt_one.trans_le hD
  have hv : 0 < δ := div_pos (Real.rpow_pos_of_pos hr' _) hD'
  have hx : r^(-(1/5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
  have hd : δ ≤ r^(-(1/5 : ℝ)) := div_le_self (Real.rpow_nonneg hr'.le _) hD
  have hd' := hd.trans hx
  have hratio : 1/r ≤ 1 := (div_le_one hr').mpr hr
  have hrδ : 1/r ≤ D*δ := by
    dsimp [δ]
    rw [mul_comm D _, div_mul_cancel₀ _ hD'.ne', one_div, ← Real.rpow_neg_one r]
    exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hb : (1/r)*δ⁻¹ ≤ D := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hv).mpr hrδ
  have hδ3 : δ^3/r ≤ 1 := (div_le_one hr').mpr ((pow_le_one₀ hv.le hd').trans hr)
  have hpower : r^(1/3:ℝ)*δ^(5/3:ℝ) ≤ 1 := by
    calc
      _ ≤ r^(1/3:ℝ)*(r^(-(1/5:ℝ)))^(5/3:ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv.le hd (by norm_num)) (Real.rpow_nonneg hr'.le _)
      _ = 1 := by rw [← Real.rpow_mul hr'.le, ← Real.rpow_add hr']; norm_num
  refine ⟨by linarith, by linarith, hv, div_le_div_of_nonneg_right (hx.trans hr) hD'.le, ?_, ?_⟩
  · change (1/r)*(1+δ⁻¹) ≤ _
    linarith only [hratio,hb]
  · change δ^3/r + (ε/2)*r^2 + r^(1/3:ℝ)*δ^(5/3:ℝ)+δ^2 ≤ _
    linarith only [hδ3, hmax, hpower, pow_le_one₀ hv.le hd' (n := 2)]

/-- The choice balances r⁻² and (λ/ε)r², clamped to the admissible radii.
The case λ = 0 uses the largest radius. -/
theorem choose_island_radius {ε cap : ℝ} (he : 0 < ε) (he' : ε ≤ 1) (hl : 0 ≤ cap) :
    ∃ r : ℝ, 1 ≤ r ∧ ε*r^2 ≤ 1 ∧
      r⁻¹^2 + (cap/ε)*r^2 ≤ 2*(ε + Real.sqrt (cap/ε) + cap/ε) := by
  let z := cap/ε
  let k := Real.sqrt z
  let t := max ε (min 1 k)
  have hz : 0 ≤ z := div_nonneg hl he.le
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hkk : k^2 = z := Real.sq_sqrt hz
  have htε : ε ≤ t := le_max_left _ _
  have ht : 0 < t := he.trans_le htε
  have ht' : t ≤ 1 := max_le he' (min_le_left _ _)
  have hrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hrsq : (Real.sqrt t)⁻¹^2 = t⁻¹ := by rw [inv_pow, Real.sq_sqrt ht.le]
  refine ⟨(Real.sqrt t)⁻¹, (one_le_inv₀ hrt).mpr (Real.sqrt_le_one.mpr ht'), ?_, ?_⟩
  · rw [hrsq, ← div_eq_mul_inv]
    exact (div_le_one ht).mpr htε
  · rw [hrsq, inv_inv, Real.sq_sqrt ht.le]
    change t + z*t⁻¹ ≤ 2*(ε+k+z)
    by_cases h : k ≤ 1
    · have hk' : k ≤ t := by
        change k ≤ max ε (min 1 k)
        rw [min_eq_right h]
        exact le_max_right _ _
      have hzt : z*t⁻¹ ≤ k := by
        rw [← div_eq_mul_inv, div_le_iff₀ ht, ← hkk, sq]
        exact mul_le_mul_of_nonneg_left hk' hk
      have htbound : t ≤ ε+k := max_le (by linarith) ((min_le_right _ _).trans (by linarith))
      linarith
    · have htone : t = 1 := by simp [t, min_eq_left (le_of_not_ge h), max_eq_right he']
      rw [htone, inv_one, mul_one]
      linarith

/-- The intermediate Thomas–Fermi cost is absorbed by the same two ratios. -/
theorem two_thirds_le (z : ℝ) (hz : 0 ≤ z) : z^(2/3:ℝ) ≤ Real.sqrt z + z := by
  rcases hz.eq_or_lt with hzero | hpos
  · subst z; norm_num
  rcases le_total z 1 with h | h
  · rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_ge hpos h (by norm_num : 1/2 ≤ (2/3:ℝ))).trans (le_add_of_nonneg_right hz)
  · have ha := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (2/3:ℝ) ≤ 1)
    rw [Real.rpow_one] at ha
    exact ha.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

end TSGA.Islands
