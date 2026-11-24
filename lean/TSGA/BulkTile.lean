import TSGA.BulkLocalization
import TSGA.Sobolev

/-! # From a finite tile comparison to its bulk error

All integrals and energies in this file have been divided by the tile volume.
On a ball with large oscillation, the cutoff samples a distribution of charges.
The estimate integrates those charges directly; comparability to the maximum
charge is used only in the small-oscillation alternative.
-/

namespace TSGA.BulkRegime

open MeasureTheory

/-- Data prior to the application of Young's inequality. In the large branch
the probability measure is the normalized tile cutoff, `v` is the pointwise
charge, and `r` is its upper bound. The constants `c,K,L` account respectively
for the local energy comparison, charge comparability, and Morrey's inequality.
All constant comparisons explicitly show the dependence on the threshold `κ`. -/
inductive TileInput (mode : BulkRegime) (p θ δ A mass gradient X : ℝ) : Prop where
  | zero (hX : X ≤ 0)
  | small {r ω c K L : ℝ} (hr : 0 < r) (hω : 0 ≤ ω) (hc : 0 ≤ c)
      (hMorrey : ω ^ p ≤ δ ^ (-p) * (L * gradient))
      (hmass : r + r ^ 2 ≤ K * mass)
      (hX : X ≤ c * ((r ^ (4 / 3 : ℝ) + r ^ (5 / 3 : ℝ)) *
        (ω / r ^ (mode.densityPower p θ)) ^ (mode.holderPower p θ)))
      (hK : 2 * c * K ≤ A) (hL : 2 * c * L ≤ A)
  | large {r ω c κ L : ℝ} (μ : Measure Position) (hprob : IsProbabilityMeasure μ)
      (v : Position → ℝ) (hcharge : ∀ᵐ x ∂μ, 0 ≤ v x ∧ v x ≤ r)
      (hbulk : Integrable (fun x => v x ^ (4 / 3 : ℝ) + v x ^ (5 / 3 : ℝ)) μ)
      (hdensity : Integrable (fun x => v x + v x ^ 2) μ)
      (hω : 0 ≤ ω) (hc : 0 ≤ c) (hκ : 0 < κ) (hLpos : 0 ≤ L)
      (hlarge : κ * r ^ (mode.densityPower p θ) ≤ ω)
      (hMorrey : ω ^ p ≤ δ ^ (-p) * (L * gradient))
      (hmass : (∫ x, v x + v x ^ 2 ∂μ) ≤ mass)
      (hX : X ≤ c * ∫ x, v x ^ (4 / 3 : ℝ) + v x ^ (5 / 3 : ℝ) ∂μ)
      (hK : 2 * c / κ ^ (mode.holderPower p θ) ≤ A)
      (hL : (2 * c / κ ^ (mode.holderPower p θ)) * L ≤ A)

private theorem absorb {A c K L δ mass gradient b : ℝ} (hδ : 0 < δ)
    (hmass : 0 ≤ mass) (hgrad : 0 ≤ gradient) (hK : c * K ≤ A) (hL : c * L ≤ A) :
    c * (δ * (K * mass) + L * gradient / δ ^ b) ≤
      A * (δ * mass + gradient / δ ^ b) := by
  calc
    _ = c * K * (δ * mass) + c * L * (gradient / δ ^ b) := by ring
    _ ≤ A * (δ * mass) + A * (gradient / δ ^ b) :=
      add_le_add (mul_le_mul_of_nonneg_right hK (mul_nonneg hδ.le hmass))
        (mul_le_mul_of_nonneg_right hL (div_nonneg hgrad (Real.rpow_nonneg hδ.le _)))
    _ = _ := by ring

/-- On either type of ball the same coefficient controls its density and gradient
errors. The alternative global-root input uses its own matrix power and the sharp
exponent `2p − 1`. -/
theorem TileInput.bound {mode : BulkRegime} {p θ δ A mass gradient X : ℝ}
    (h : TileInput mode p θ δ A mass gradient X) (hp : 3 < p) (hθp : 2 ≤ p * θ)
    (hδ : 0 < δ) (hA : 0 ≤ A) (hmass : 0 ≤ mass) (hgrad : 0 ≤ gradient) :
    X ≤ A * (δ * mass + gradient / δ ^ (mode.exponent p θ)) := by
  cases h with
  | zero hX => exact hX.trans (by positivity)
  | @small r ω c K L hr hω hc hM hcomp hX hK hL =>
    have hlocal := mode.combined_bound hp hθp hδ (V := 1) zero_lt_one hr hω
      (by simpa only [one_mul] using hM)
    simp only [one_mul, mul_one] at hlocal
    calc
      X ≤ _ := hX
      _ ≤ c * (2 * (δ * (r + r ^ 2) + L * gradient / δ ^ (mode.exponent p θ))) :=
        mul_le_mul_of_nonneg_left hlocal hc
      _ ≤ (2 * c) * (δ * (K * mass) + L * gradient / δ ^ (mode.exponent p θ)) := by
        rw [← mul_assoc, mul_comm c 2]
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hcomp hδ.le) le_rfl)
          (mul_nonneg (by norm_num) hc)
      _ ≤ _ := absorb hδ hmass hgrad hK hL
  | @large r ω c κ L μ hprob v hcharge hbulk hdensity hω hc hκ hLpos hlarge hM hcomp hX hK hL =>
    let : IsProbabilityMeasure μ := hprob
    let f := fun x => v x ^ (4 / 3 : ℝ) + v x ^ (5 / 3 : ℝ)
    let g := fun x => v x + v x ^ 2
    let t := κ ^ (mode.holderPower p θ)
    let B := L * gradient / δ ^ (mode.exponent p θ)
    have ht : 0 < t := Real.rpow_pos_of_pos hκ _
    have hf : Integrable f μ := hbulk
    have hg : Integrable g μ := hdensity
    have hpt : ∀ᵐ x ∂μ, f x * t ≤ 2 * (δ * g x + B) := by
      filter_upwards [hcharge] with x hx
      simpa only [one_mul, mul_one, f, g, t, B] using
        (mode.largeOscillation_bound hp hθp hδ (V := 1) zero_lt_one hx.1 hx.2 hω
          (mul_nonneg hLpos hgrad) hκ hlarge (by simpa only [one_mul] using hM))
    have hint : (∫ x, f x ∂μ) * t ≤ 2 * (δ * (∫ x, g x ∂μ) + B) := by
      calc
        _ = ∫ x, f x * t ∂μ := (integral_mul_const _ _).symm
        _ ≤ ∫ x, 2 * (δ * g x + B) ∂μ := integral_mono_ae (hf.mul_const t)
          (((hg.const_mul δ).add (integrable_const B)).const_mul 2) hpt
        _ = _ := by rw [integral_const_mul, integral_add (hg.const_mul δ) (integrable_const B),
          integral_const_mul]; simp
    have himproved := (le_div_iff₀ ht).2 hint
    calc
      X ≤ c * (∫ x, f x ∂μ) := hX
      _ ≤ c * (2 * (δ * (∫ x, g x ∂μ) + B) / t) := mul_le_mul_of_nonneg_left himproved hc
      _ = (2 * c / t) * (δ * (∫ x, g x ∂μ) + B) := by ring
      _ ≤ (2 * c / t) * (δ * (1 * mass) + B) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hcomp hδ.le) le_rfl) (by positivity)
      _ ≤ _ := absorb hδ hmass hgrad (by simpa only [mul_one] using hK) hL

end TSGA.BulkRegime
