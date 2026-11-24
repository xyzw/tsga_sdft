import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv

/-! # Neutral radial shells in a tetrahedral pyramid -/

noncomputable section
namespace TSGA.Skeleton

open MeasureTheory Set

/-- Volume fraction of a shell of relative width u in a three-dimensional pyramid. -/
def shellFraction (u : ℝ) := 1 - (1-u)^3

def shellCoefficient (s : ℝ) := shellFraction s / shellFraction (s/2)

theorem shellFraction_pos {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1) : 0 < shellFraction u := by
  have h := pow_lt_pow_left₀ (show 1-u < 1 by linarith) (by linarith : 0 ≤ 1-u) (by decide : 3 ≠ 0)
  simpa [shellFraction] using sub_pos.mpr h

theorem shellFraction_le {u : ℝ} (_hu : 0 ≤ u) (hu' : u ≤ 1) : shellFraction u ≤ 3*u := by
  dsimp only [shellFraction]
  nlinarith only [mul_nonneg (sq_nonneg u) (show 0 ≤ 3-u by linarith)]

theorem shellCoefficient_bounds {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1/2) :
    0 ≤ shellCoefficient s ∧ shellCoefficient s ≤ 2 := by
  have h := shellFraction_pos (half_pos hs) (by linarith : s/2 ≤ 1)
  refine ⟨(div_pos (shellFraction_pos hs (by linarith)) h).le,(div_le_iff₀ h).2 ?_⟩
  dsimp only [shellFraction]
  nlinarith only [mul_nonneg (sq_nonneg s) (show 0 ≤ 2-s by linarith)]

/-- Integral of t² from the inner face of the shell to the ray coordinate λ. -/
def tailPrimitive (u t : ℝ) := if 1-u ≤ t then (t^3-(1-u)^3)/3 else 0

def rayPrimitive (s t : ℝ) := shellCoefficient s * tailPrimitive (s/2) t - tailPrimitive s t

theorem tailPrimitive_integral {u t : ℝ} (hu : u ≤ 1) (ht : 0 ≤ t) :
    (∫ x in 0..t, (Ioi (1-u)).indicator (fun x : ℝ => x^2) x) = tailPrimitive u t := by
  rw [intervalIntegral.integral_of_le ht, setIntegral_indicator measurableSet_Ioi]
  have he : Ioc 0 t ∩ Ioi (1-u) = Ioc (1-u) t := by
    ext x
    simp only [mem_inter_iff,mem_Ioc,mem_Ioi]
    constructor
    · rintro ⟨⟨_,hx⟩,hl⟩
      exact ⟨hl,hx⟩
    · rintro ⟨hl,hx⟩
      exact ⟨⟨by linarith,hx⟩,hl⟩
  rw [he]
  by_cases h : 1-u ≤ t
  · rw [← intervalIntegral.integral_of_le h,integral_pow]
    norm_num [tailPrimitive,h]
  · rw [Ioc_eq_empty (fun hlt => h hlt.le),setIntegral_empty]
    simp [tailPrimitive,h]

theorem rayPrimitive_eq_integrals {s t : ℝ} (hs : s ≤ 1/2) (ht : 0 ≤ t) :
    rayPrimitive s t =
      shellCoefficient s * (∫ x in 0..t, (Ioi (1-s/2)).indicator (fun x : ℝ => x^2) x) -
      ∫ x in 0..t, (Ioi (1-s)).indicator (fun x : ℝ => x^2) x := by
  rw [tailPrimitive_integral (by linarith) ht,tailPrimitive_integral (by linarith) ht]
  rfl

/-- The precise local neutrality cancels the flux through the base face. -/
theorem rayPrimitive_outer {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1/2) : rayPrimitive s 1 = 0 := by
  have h := (shellFraction_pos (half_pos hs) (by linarith : s/2 ≤ 1)).ne'
  have ht (u : ℝ) (hu : 0 ≤ u) : tailPrimitive u 1 = shellFraction u/3 := by
    simp [tailPrimitive,shellFraction,show 1-u ≤ 1 by linarith]
  rw [rayPrimitive,ht _ (half_pos hs).le,ht _ hs.le,shellCoefficient]
  field_simp
  ring

theorem rayPrimitive_off_shell {s t : ℝ} (hs : 0 ≤ s) (ht : t < 1-s) : rayPrimitive s t = 0 := by
  simp [rayPrimitive,tailPrimitive,not_le.mpr ht,show ¬1-s/2 ≤ t by linarith]

theorem rayPrimitive_bound {s t : ℝ} (hs : 0 < s) (hs' : s ≤ 1/2) (ht : t ≤ 1) :
    |rayPrimitive s t| ≤ 2*s := by
  have ht' (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
      0 ≤ tailPrimitive u t ∧ tailPrimitive u t ≤ u := by
    by_cases h : 1-u ≤ t
    · have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1-u) h 3
      have hp' := pow_le_pow_left₀ (by linarith : 0 ≤ t) ht 3
      have hf := shellFraction_le h0 h1
      simp only [tailPrimitive,ite_eq_left h,shellFraction] at *
      constructor <;> linarith
    · simp [tailPrimitive,h,h0]
  have hc := shellCoefficient_bounds hs hs'
  obtain ⟨h0,h1⟩ := ht' (s/2) (half_pos hs).le (by linarith)
  obtain ⟨h2,h3⟩ := ht' s hs.le (by linarith)
  apply abs_le.mpr
  dsimp only [rayPrimitive]
  constructor
  · linarith only [mul_nonneg hc.1 h0,h3,hs.le]
  · linarith only [mul_le_mul hc.2 h1 h0 (by norm_num),h2,hs.le]

/-- Componentwise bound on the radial divergence primitive (x-c)P(λ)/λ³. -/
theorem rayFlux_bound {s t w R : ℝ} (hs : 0 < s) (hs' : s ≤ 1/2) (ht : t ≤ 1) (hw : |w| ≤ R) :
    |w * rayPrimitive s t / t^3| ≤ 16*R*s := by
  have hR := (abs_nonneg w).trans hw
  by_cases h : t < 1-s
  · rw [rayPrimitive_off_shell hs.le h]; simpa using (show 0 ≤ 16*R*s by positivity)
  · have ht' : 1/2 ≤ t := by linarith [le_of_not_gt h]
    have hhalf := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) ht' 3
    have ht0 : 0 < t^3 := pow_pos (by linarith) _
    rw [abs_div, abs_of_pos ht0, abs_mul, div_le_iff₀ ht0]
    calc
      _ ≤ R*(2*s) := mul_le_mul hw (rayPrimitive_bound hs hs' ht) (abs_nonneg _) hR
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 16*R*s by positivity)]

/-- The Fourier test integrated on a pyramid ray with the volume Jacobian. -/
def rayValue (u : ℝ) (g : ℝ → ℂ) := ∫ t in (1-u)..1, ((t^2 : ℝ):ℂ)*g t

/-- The flux paired with the radial derivative of the Fourier test. -/
def rayFlux (u : ℝ) (g' : ℝ → ℂ) :=
  ∫ t in (1-u)..1, (((t^3-(1-u)^3)/3:ℝ):ℂ)*g' t

theorem tail_integration_by_parts (u : ℝ) {g g' : ℝ → ℂ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hgi : Continuous g') :
    rayFlux u g' = ((shellFraction u/3:ℝ):ℂ)*g 1 - rayValue u g := by
  let a := 1-u
  have hp (t : ℝ) : HasDerivAt (fun t : ℝ => ((t^3-a^3)/3)) (t^2) t := by
    have h := ((hasDerivAt_pow 3 t).sub_const (a^3)).div_const 3
    have he : (↑(3:ℕ):ℝ)*t^(3-1)/3 = t^2 := by norm_num
    rw [he] at h
    exact h
  have hi : IntervalIntegrable (fun t : ℝ => ((t^2:ℝ):ℂ)) volume a 1 :=
    (by fun_prop : Continuous (fun t : ℝ => ((t^2:ℝ):ℂ))).intervalIntegrable ..
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := 1)
    (fun t _ => (hp t).ofReal_comp) (fun t _ => hg t) hi (hgi.intervalIntegrable ..)
  simpa [rayFlux,rayValue,a,shellFraction] using H

/-- After summing over a thin and a thick shell, the outer boundary term cancels
exactly. This is the Fourier divergence identity on each family of rays. -/
theorem neutral_integration_by_parts {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1/2)
    {g g' : ℝ → ℂ} (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g') :
    (shellCoefficient s : ℂ)*rayValue (s/2) g-rayValue s g =
      rayFlux s g'-(shellCoefficient s : ℂ)*rayFlux (s/2) g' := by
  have h : shellCoefficient s*(shellFraction (s/2)/3) = shellFraction s/3 := by
    have hd := (shellFraction_pos (half_pos hs) (by linarith : s/2 ≤ 1)).ne'
    dsimp only [shellCoefficient]
    field_simp
  have he : (shellCoefficient s:ℂ)*((shellFraction (s/2)/3:ℝ):ℂ) = ((shellFraction s/3:ℝ):ℂ) := by
    exact_mod_cast h
  rw [tail_integration_by_parts s hg hg',tail_integration_by_parts (s/2) hg hg']
  linear_combination g 1 * he

end TSGA.Skeleton
