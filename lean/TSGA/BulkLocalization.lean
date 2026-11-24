import TSGA.Exponents
import Mathlib.Analysis.MeanInequalities

/-! # Bulk density errors on a localization ball

The finite Morrey estimate controls the oscillation of a matrix power.
Weighted Young interpolation turns it into the bulk gradient error of
Theorem 3.3. A lower bound on the minority density gives an additional estimate.
In the alternative estimate the interpolated quantity is the global root.
-/

namespace TSGA

inductive BulkRegime where
  | general
  | minority
  | globalRoot

namespace BulkRegime

noncomputable def holderPower (mode : BulkRegime) (p θ : ℝ) : ℝ :=
  match mode with
  | .general => min 1 (1 / (3 * θ))
  | .minority => min 1 (p / (3 * (θ * p - 1)))
  | .globalRoot => 1

noncomputable def densityPower (mode : BulkRegime) (p θ : ℝ) : ℝ :=
  match mode with
  | .general | .minority => θ
  | .globalRoot => 1 / p

noncomputable def exponent (mode : BulkRegime) (p θ : ℝ) : ℝ :=
  match mode with
  | .general => bulkExponent p θ
  | .minority => polarizedBulkExponent p θ
  | .globalRoot => 2 * p - 1

/-- The powers appearing after Young interpolation and the formula for the
inverse power of ε, including the global-root case in `eq:root_bulk_SSW`. -/
private theorem powers (mode : BulkRegime) {p θ m : ℝ} (hp : 3 < p) (hθp : 2 ≤ p * θ)
    (hm : m ∈ Set.Icc (4 / 3 : ℝ) (5 / 3)) :
    let a := mode.holderPower p θ
    let s := mode.densityPower p θ
    0 < a ∧ a < p ∧ (m - s * a) * p / (p - a) ∈ Set.Icc 1 2 ∧
      p + p / a - 1 = mode.exponent p θ := by
  have hp' : 0 < p := by linarith
  have hθ : 0 < θ := pos_of_mul_pos_right (by linarith : 0 < p * θ) hp'.le
  have hs : 2 ≤ θ * p := by simpa only [mul_comm] using hθp
  cases mode with
  | general =>
    have ha : 0 < min 1 (1 / (3 * θ)) := lt_min (by norm_num) (by positivity)
    exact ⟨ha, (min_le_left ..).trans_lt (by linarith : 1 < p),
      youngDensityPower_mem_Icc hp hs (.inl rfl) hm, bulkExponent_from_holder hp' hθ⟩
  | minority =>
    have hden : 0 < 3 * (θ * p - 1) := by linarith
    have ha : 0 < min 1 (p / (3 * (θ * p - 1))) :=
      lt_min (by norm_num) (div_pos hp' hden)
    exact ⟨ha, (min_le_left ..).trans_lt (by linarith : 1 < p),
      youngDensityPower_mem_Icc hp hs (.inr rfl) hm, polarizedBulkExponent_from_holder hp' (by linarith)⟩
  | globalRoot =>
    dsimp [holderPower, densityPower, exponent]
    refine ⟨zero_lt_one, by linarith, ?_, by ring⟩
    have hden : 0 < p - 1 := by linarith
    have heq : (m - 1 / p * 1) * p = m * p - 1 := by field_simp
    rw [heq]
    constructor
    · apply (le_div_iff₀ hden).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hm.1) hp'.le]
    · apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) hp'.le]

/-- A density power with exponent between one and two is bounded by the
charge density plus its square regardless of whether the density exceeds one. -/
theorem density_power_le {r γ : ℝ} (hr : 0 < r) (hγ : γ ∈ Set.Icc 1 2) :
    r ^ γ ≤ r + r ^ 2 := by
  rcases le_total r 1 with hsmall | hlarge
  · have h := Real.rpow_le_rpow_of_exponent_ge hr hsmall hγ.1
    simpa only [Real.rpow_one] using h.trans (by simp [sq_nonneg] : r ^ (1 : ℝ) ≤ r + r ^ 2)
  · have h := Real.rpow_le_rpow_of_exponent_le hlarge hγ.2
    rw [Real.rpow_two] at h
    linarith

/-- Single-density-power estimate. Here `V` is ℓ³ and `G` is the Morrey
constant times the integral on the ball of the pth power of the gradient.
The displayed hypothesis is Morrey's inequality at length ℓ = ε⁻¹. -/
theorem oscillation_bound (mode : BulkRegime) {p θ m ε V r ω G : ℝ}
    (hp : 3 < p) (hθp : 2 ≤ p * θ) (hm : m ∈ Set.Icc (4 / 3 : ℝ) (5 / 3))
    (hε : 0 < ε) (hV : 0 < V) (hr : 0 < r) (hω : 0 ≤ ω)
    (hMorrey : V * ω ^ p ≤ ε ^ (-p) * G) :
    V * r ^ m * (ω / r ^ (mode.densityPower p θ)) ^ (mode.holderPower p θ) ≤
      ε * V * (r + r ^ 2) + G / ε ^ (mode.exponent p θ) := by
  let a := mode.holderPower p θ
  let s := mode.densityPower p θ
  let t := a / p
  let γ := (m - s * a) * p / (p - a)
  obtain ⟨ha, hap, hγ, hb⟩ := mode.powers hp hθp hm
  change 0 < a at ha
  change a < p at hap
  change γ ∈ _ at hγ
  change p + p / a - 1 = _ at hb
  have hp' : 0 < p := by linarith
  have ht : 0 < t := div_pos ha hp'
  have ht' : t < 1 := by simpa only [t, div_lt_one hp'] using hap
  have hpwt : p * t = a := by dsimp [t]; field_simp
  have hγwt : γ * (1 - t) = m - s * a := by
    dsimp [γ, t]
    field_simp [hp'.ne', (sub_pos.mpr hap).ne']
  have hεwt : (1 - p / a) * t + (1 - t) = 0 := by
    dsimp [t]
    field_simp [ha.ne', hp'.ne']
    ring
  let X := ε ^ (1 - p / a) * (V * ω ^ p)
  let Y := ε * V * r ^ γ
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hrescale : X ^ t * Y ^ (1 - t) = V * r ^ m * (ω / r ^ s) ^ a := by
    have hVwt : V ^ t * V ^ (1 - t) = V := by
      rw [← Real.rpow_add hV, show t + (1 - t) = 1 by ring, Real.rpow_one]
    have hcancel : ε ^ ((1 - p / a) * t) * ε ^ (1 - t) = 1 := by
      rw [← Real.rpow_add hε, hεwt, Real.rpow_zero]
    dsimp only [X, Y]
    rw [Real.mul_rpow (by positivity : 0 ≤ ε ^ (1 - p / a)) (by positivity : 0 ≤ V * ω ^ p),
      Real.mul_rpow hV.le (Real.rpow_nonneg hω _),
      Real.mul_rpow (mul_nonneg hε.le hV.le) (Real.rpow_nonneg hr.le _),
      Real.mul_rpow hε.le hV.le, ← Real.rpow_mul hω, ← Real.rpow_mul hε.le,
      ← Real.rpow_mul hr.le, hpwt, hγwt]
    calc
      _ = (ε ^ ((1 - p / a) * t) * ε ^ (1 - t)) * (V ^ t * V ^ (1 - t)) *
        ω ^ a * r ^ (m - s * a) := by ring
      _ = _ := by
        rw [hcancel, one_mul, hVwt, Real.rpow_sub hr, Real.div_rpow hω (Real.rpow_nonneg hr.le _),
          ← Real.rpow_mul hr.le]
        ring
  have hYoung := Real.geom_mean_le_arith_mean2_weighted ht.le (sub_nonneg.mpr ht'.le)
    hX hY (by ring : t + (1 - t) = 1)
  have hMorrey' : X ≤ G / ε ^ (mode.exponent p θ) := by
    calc
      X ≤ ε ^ (1 - p / a) * (ε ^ (-p) * G) :=
        mul_le_mul_of_nonneg_left hMorrey (by positivity)
      _ = G / ε ^ (mode.exponent p θ) := by
        rw [← mul_assoc, ← Real.rpow_add hε,
          show 1 - p / a + -p = -(mode.exponent p θ) by linarith only [hb],
          Real.rpow_neg hε.le]
        ring
  have hvolume : Y ≤ ε * V * (r + r ^ 2) :=
    mul_le_mul_of_nonneg_left (density_power_le hr hγ) (mul_nonneg hε.le hV.le)
  change V * r ^ m * (ω / r ^ s) ^ a ≤ _
  rw [← hrescale]
  exact hYoung.trans <| by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht'.le) hX, mul_nonneg ht.le hY, hMorrey', hvolume]

/-- The local gas-energy comparison contains the sum of the 4/3 and 5/3
powers. Both are estimated with the same gradient integral. -/
theorem combined_bound (mode : BulkRegime) {p θ ε V r ω G : ℝ}
    (hp : 3 < p) (hθp : 2 ≤ p * θ) (hε : 0 < ε) (hV : 0 < V)
    (hr : 0 < r) (hω : 0 ≤ ω) (hMorrey : V * ω ^ p ≤ ε ^ (-p) * G) :
    V * (r ^ (4 / 3 : ℝ) + r ^ (5 / 3 : ℝ)) *
      (ω / r ^ (mode.densityPower p θ)) ^ (mode.holderPower p θ) ≤
      2 * (ε * V * (r + r ^ 2) + G / ε ^ (mode.exponent p θ)) := by
  have h₄ := mode.oscillation_bound hp hθp (m := 4 / 3) (by constructor <;> norm_num)
    hε hV hr hω hMorrey
  have h₅ := mode.oscillation_bound hp hθp (m := 5 / 3) (by constructor <;> norm_num)
    hε hV hr hω hMorrey
  linarith only [h₄, h₅]

/-- Large oscillations. The charge `v` is the actual pointwise charge under
the cutoff and may be much smaller than its maximum `r`. The large-oscillation
threshold absorbs the relative modulus on the left of the same Young estimate.
Integrating this bound over the cutoff requires no lower charge bound. -/
theorem largeOscillation_bound (mode : BulkRegime) {p θ ε V r v ω G κ : ℝ}
    (hp : 3 < p) (hθp : 2 ≤ p * θ) (hε : 0 < ε) (hV : 0 < V)
    (hv : 0 ≤ v) (hvr : v ≤ r) (hω : 0 ≤ ω) (hG : 0 ≤ G) (hκ : 0 < κ)
    (hlarge : κ * r ^ (mode.densityPower p θ) ≤ ω)
    (hMorrey : V * ω ^ p ≤ ε ^ (-p) * G) :
    V * (v ^ (4 / 3 : ℝ) + v ^ (5 / 3 : ℝ)) * κ ^ (mode.holderPower p θ) ≤
      2 * (ε * V * (v + v ^ 2) + G / ε ^ (mode.exponent p θ)) := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp only [Real.zero_rpow (by norm_num : (4 / 3 : ℝ) ≠ 0),
      Real.zero_rpow (by norm_num : (5 / 3 : ℝ) ≠ 0), zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add, mul_zero, zero_mul]
    positivity
  have hp' : 0 < p := by linarith
  have hθ : 0 < θ := pos_of_mul_pos_right (by linarith : 0 < p * θ) hp'.le
  have hs : 0 ≤ mode.densityPower p θ := by
    cases mode <;> simp only [densityPower] <;> positivity
  have ha := (mode.powers hp hθp (m := 4 / 3) (by constructor <;> norm_num)).1
  have hrel : κ ≤ ω / v ^ (mode.densityPower p θ) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hv' _)).2
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv hvr hs) hκ.le).trans hlarge
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hκ.le hrel ha.le)
    (by positivity)).trans (mode.combined_bound hp hθp hε hV hv' hω hMorrey)

end BulkRegime
end TSGA
