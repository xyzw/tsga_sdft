import TSGA.FrozenRate

/-! # Scales for the ordered SSW comparison near full polarization

Writing the parent charge as x³ and its removed fraction as z³, the two
lengths are 1/x and L/(xz). At these lengths the direct cost, the current
cost and the two tetrahedron-rate errors are all of order z.
-/

noncomputable section

namespace TSGA.SSW

open Set

/-- The density and wavevector growth in Proposition E.2. -/
def holderGrowth (r : ℝ) (q : Position) : ℝ :=
  r^(4/3 : ℝ) + r^(5/3 : ℝ) + r*‖q‖^2

theorem holderGrowth_eq {r : ℝ} (hr : 0 < r) (q : Position) :
    holderGrowth r q = r * rateGrowth r q := by
  have h (a : ℝ) : r^(1+a) = r*r^a := by rw [Real.rpow_add hr, Real.rpow_one]
  rw [holderGrowth, show (4/3:ℝ) = 1+1/3 by norm_num, show (5/3:ℝ) = 1+2/3 by norm_num, h, h]
  unfold rateGrowth
  ring

/-- Estimates at the density-selected cutoff and length. The three
bounds inside the dilation interval are for the kinetic cutoff, the
direct charge removed, and the upper finite-size error. -/
theorem ordered_scales {r h L : ℝ} (hr : 0 < r) (hh : 0 < h) (hh₁ : h ≤ 1) (hL : 1 ≤ L)
    (q : Position) :
    ∃ ℓ δ : ℝ, 0 < ℓ ∧ 0 < δ ∧ δ*L ≤ ℓ ∧
      upperRateError r q ℓ δ ≤ 4 * holderGrowth r q * h^(1/3:ℝ) ∧
      ∀ t ∈ scaleInterval,
        r / ((t*ℓ)*(t*δ)) ≤ 4 * holderGrowth r q ∧
        r^2*h*(t*ℓ)^2 ≤ 4*L^2 * holderGrowth r q * h^(1/3:ℝ) ∧
        upperRateError r q (t*ℓ) (t*δ) ≤ 16 * holderGrowth r q * h^(1/3:ℝ) := by
  let x := r^(1/3 : ℝ)
  let z := h^(1/3 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hr _
  have hz : 0 < z := Real.rpow_pos_of_pos hh _
  have hz1 : z ≤ 1 := Real.rpow_le_one hh.le hh₁ (by norm_num)
  have hx3 : x^3 = r := by rw [← Real.rpow_mul_natCast hr.le]; norm_num
  have hz3 : z^3 = h := by rw [← Real.rpow_mul_natCast hh.le]; norm_num
  have hx2 : x^2 = r^(2/3:ℝ) := by rw [← Real.rpow_mul_natCast hr.le]; norm_num
  have hl : 0 < L := zero_lt_one.trans_le hL
  let δ := x⁻¹
  let ℓ := L/(x*z)
  have hd : 0 < δ := inv_pos.mpr hx
  have he : 0 < ℓ := div_pos hl (mul_pos hx hz)
  have hscale : δ*L ≤ ℓ := by
    apply (le_div_iff₀ (mul_pos hx hz)).2
    simp only [δ]
    calc
      _ = L*z := by field_simp
      _ ≤ L := mul_le_of_le_one_right hl.le hz1
  let G := rateGrowth r q
  have hG : G = x + x^2 + ‖q‖^2 := by simp only [G, rateGrowth, x, ← hx2]
  have hs := holderGrowth_eq hr q
  change holderGrowth r q = r*G at hs
  have hg₁ : x ≤ G := by rw [hG]; linarith [sq_nonneg x, sq_nonneg ‖q‖]
  have hg₂ : x^2 ≤ G := by rw [hG]; linarith [hx.le,sq_nonneg ‖q‖]
  have hg : 0 ≤ G := hx.le.trans hg₁
  have h0 : 0 ≤ holderGrowth r q := hs ▸ mul_nonneg hr.le hg
  have hu : upperRateError r q ℓ δ ≤ 4*holderGrowth r q*z := by
    have hid : upperRateError r q ℓ δ = r*z/L*(2*x+x^2+G) := by
      dsimp only [upperRateError, lowerRateError, ℓ, δ]
      change r/(L/(x*z)) + r/(L/(x*z))*((x⁻¹)⁻¹+(x⁻¹)^3*r+x⁻¹*G) = _
      rw [← hx3]
      field_simp
      ring
    rw [hid, hs]
    calc
      _ ≤ (r*z)*(2*x+x^2+G) := mul_le_mul_of_nonneg_right
        (div_le_self (mul_nonneg hr.le hz.le) hL) (by positivity)
      _ ≤ r*z*(4*G) := mul_le_mul_of_nonneg_left (by linarith only [hg₁,hg₂]) (mul_nonneg hr.le hz.le)
      _ = _ := by ring
  refine ⟨ℓ, δ, he, hd, hscale, hu, ?_⟩
  intro t ht
  have ht1 : (1/2:ℝ) ≤ t := ht.1
  have ht2 : t ≤ (3/2:ℝ) := ht.2
  have ht0 : 0 < t := by linarith
  have hlow : 1 ≤ 4*t^2 := by nlinarith [sq_nonneg (t-1/2)]
  have hhigh : t^2 ≤ 4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2-t) (by linarith : 0 ≤ 2+t)]
  refine ⟨?_, ?_, (TSGA.Localization.upperRateError_dilate q hr.le he hd ht).trans
    ((mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ 4)).trans_eq (by ring))⟩
  · have hden : r / ((t*ℓ)*(t*δ)) = r*x^2*z / (L*t^2) := by dsimp [ℓ,δ]; field_simp
    rw [hden, hs]
    apply (div_le_iff₀ (mul_pos hl (sq_pos_of_pos ht0))).2
    calc
      r*x^2*z ≤ r*x^2 := mul_le_of_le_one_right (by positivity) hz1
      _ ≤ r*G := mul_le_mul_of_nonneg_left hg₂ hr.le
      _ ≤ r*G*(4*t^2) := le_mul_of_one_le_right (mul_nonneg hr.le hg) hlow
      _ ≤ r*G*(4*t^2)*L := le_mul_of_one_le_right (by positivity) hL
      _ = _ := by ring
  · have hid : r^2*h*(t*ℓ)^2 = L^2*z*t^2*(r*x) := by
      dsimp [ℓ]
      rw [← hx3, ← hz3]
      field_simp
    rw [hid, hs]
    calc
      _ ≤ L^2*z*4*(r*G) := mul_le_mul (mul_le_mul_of_nonneg_left hhigh (by positivity))
        (mul_le_mul_of_nonneg_left hg₁ hr.le) (by positivity) (by positivity)
      _ = _ := by ring

/-- A density smaller in the Loewner order has no larger lower-rate cost. -/
theorem lowerRateError_le_upper {s r ℓ δ : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r)
    (he : 0 < ℓ) (hd : 0 < δ) (q : Position) : lowerRateError s q ℓ δ ≤ upperRateError r q ℓ δ := by
  have hgr : rateGrowth s q ≤ rateGrowth r q := by
    dsimp [rateGrowth]
    gcongr
  have hg : 0 ≤ rateGrowth s q :=
    add_nonneg (add_nonneg (Real.rpow_nonneg hs _) (Real.rpow_nonneg hs _)) (sq_nonneg _)
  apply (le_add_of_nonneg_left (div_nonneg (hs.trans hsr) he.le)).trans'
  unfold lowerRateError
  apply mul_le_mul (div_le_div_of_nonneg_right hsr he.le) _
    (by positivity) (div_nonneg (hs.trans hsr) he.le)
  exact add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left hsr (pow_nonneg hd.le _)) _)
    (mul_le_mul_of_nonneg_left hgr hd.le)

end TSGA.SSW
