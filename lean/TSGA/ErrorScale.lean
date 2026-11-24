import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Choice of the localization scale in Theorem 3.3 -/

namespace TSGA.Localization

/-- A quantitative choice of the small localization parameter. The constant
works simultaneously for every nonnegative set of error integrals, including
when the bulk and phase terms have different powers. -/
theorem extend_small_scale {A τ : ℝ} (hA : 0 < A) (hτ : 0 < τ) (b k : ℝ) :
    ∃ C > 0, ∀ {X M S U V : ℝ}, 0 ≤ M → 0 ≤ S → 0 ≤ U → 0 ≤ V →
      X ≤ A * (M + S) →
      (∀ δ : ℝ, 0 < δ → δ ≤ τ →
        X ≤ A * (δ * M + S / δ + U / δ ^ b + V / δ ^ k)) →
      ∀ ε : ℝ, 0 < ε →
        X ≤ ε * M + C * (1 + ε) / ε * S + C / ε ^ b * U + C / ε ^ k * V := by
  let K := max 1 (max A (A / τ))
  have hK₁ : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK₁
  have hAK : A ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hτK : A ≤ τ * K := by
    rw [mul_comm]
    exact (div_le_iff₀ hτ).mp ((le_max_right _ _).trans (le_max_right _ _))
  let C := max (A * K) (max (A * K ^ b) (A * K ^ k))
  have hS : A * K ≤ C := le_max_left _ _
  have hB : A * K ^ b ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hP : A * K ^ k ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hAC := (le_mul_of_one_le_right hA.le hK₁).trans hS
  have hC : 0 < C := hA.trans_le hAC
  refine ⟨C, hC, ?_⟩
  intro X M S U V hM hSq hU hV hrough hsmall ε hε
  have hgeom : C ≤ C * (1 + ε) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith only [hC]
  by_cases h : ε ≤ A
  · let δ := ε / K
    have hδ : 0 < δ := div_pos hε hK
    have hδτ : δ ≤ τ := (div_le_iff₀ hK).mpr (h.trans hτK)
    have hm : A * δ ≤ ε := by
      dsimp [δ]
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hK).mpr (by simpa only [mul_comm A ε] using mul_le_mul_of_nonneg_left hAK hε.le)
    have hs : A / δ ≤ C * (1 + ε) / ε := by
      change A / (ε / K) ≤ _
      rw [div_div_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hε).mpr
      exact hS.trans (by nlinarith only [hC, mul_nonneg hC.le hε.le])
    have hpow (a : ℝ) (ha : A * K ^ a ≤ C) : A / δ ^ a ≤ C / ε ^ a := by
      dsimp [δ]
      rw [Real.div_rpow hε.le hK.le, div_div_eq_mul_div]
      exact div_le_div_of_nonneg_right ha (Real.rpow_nonneg hε.le _)
    calc
      X ≤ _ := hsmall δ hδ hδτ
      _ = (A * δ) * M + (A / δ) * S + (A / δ ^ b) * U + (A / δ ^ k) * V := by ring
      _ ≤ _ := add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hm hM) (mul_le_mul_of_nonneg_right hs hSq))
        (mul_le_mul_of_nonneg_right (hpow b hB) hU)) (mul_le_mul_of_nonneg_right (hpow k hP) hV)
  · have hMS : A * M + A * S ≤ ε * M + C * (1 + ε) / ε * S :=
      add_le_add (mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge h)) hM)
        (mul_le_mul_of_nonneg_right (hAC.trans hgeom) hSq)
    have hu : 0 ≤ C / ε ^ b * U := by positivity
    have hv : 0 ≤ C / ε ^ k * V := by positivity
    linarith [show X ≤ A * M + A * S by simpa only [mul_add] using hrough]

end TSGA.Localization
