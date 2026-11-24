import TSGA.RayRegularity
import TSGA.SpinComparison
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # The minority fraction at fixed spin direction

The endpoint Hölder bounds and fixed-charge convexity control the
energy in the cube root of the minority fraction, including at zero.
-/

noncomputable section
namespace TSGA.SSW

open scoped ComplexOrder

private theorem cubeRoot_cube {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

/-- Convexity turns the two endpoint moduli into a Lipschitz estimate in
the cube root of the minority fraction on the left half of the interval. -/
theorem convex_minority_cubeRoot {F : ℝ → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (conv : ConvexOn ℝ (Set.Icc 0 1) F)
    (left : ∀ t ∈ Set.Icc (0:ℝ) 1, |F t-F 0| ≤ H*t^(1/3:ℝ))
    (right : ∀ t ∈ Set.Icc (0:ℝ) 1, |F 1-F t| ≤ H*(1-t)^(1/3:ℝ))
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) :
    |F t-F s| ≤ 6*H*|t^(1/3:ℝ)-s^(1/3:ℝ)| := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm (F t), abs_sub_comm (t^_)]
    exact this ht hs (le_of_not_ge hst)
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have ht1 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  let a := s^(1/3:ℝ)
  let b := t^(1/3:ℝ)
  have ha : 0 ≤ a := Real.rpow_nonneg hs.1 _
  have hb : 0 < b := Real.rpow_pos_of_pos (hs.1.trans_lt hst) _
  have hab : a ≤ b := Real.rpow_le_rpow hs.1 hst.le (by norm_num)
  have hb1 : b ≤ 1 := Real.rpow_le_one ht.1 ht1.2 (by norm_num)
  have hca : a^3 = s := cubeRoot_cube hs.1
  have hcb : b^3 = t := cubeRoot_cube ht.1
  have factor : t-s = (b-a)*(b^2+b*a+a^2) := by rw [← hca, ← hcb]; ring
  have hpoly : b^2+b*a+a^2 ≤ 3*b^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hab) ha, mul_nonneg (sub_nonneg.mpr hab) hb.le]
  have hd₁ : t-s ≤ (b-a)*(3*b^2) := factor.trans_le (mul_le_mul_of_nonneg_left hpoly (sub_nonneg.mpr hab))
  have hd₂ : t-s ≤ (b-a)*3 := by
    apply hd₁.trans (mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab))
    nlinarith only [mul_nonneg (sub_nonneg.mpr hb1) hb.le, hb1]
  change |F t-F s| ≤ 6*H*|b-a|
  rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_le]
  constructor
  · have hl := (abs_le.mp (left t ht1)).1
    change -(H*b) ≤ _ at hl
    rcases hs.1.eq_or_lt with hs0 | hsp
    · have ha0 : a = 0 := by dsimp only [a]; rw [← hs0, Real.zero_rpow (by norm_num)]
      rw [ha0, sub_zero, ← hs0]
      linarith only [hl, mul_nonneg hH hb.le]
    have hsec := conv.secant_mono_aux1 (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) ht1 hsp hst
    have hlow : t*(F s-F t) ≤ (t-s)*(H*b) := by
      nlinarith only [hsec, mul_nonneg (sub_nonneg.mpr hst.le) (sub_nonneg.mpr hl)]
    have hbound : t*(F s-F t) ≤ t*(3*H*(b-a)) := calc
      _ ≤ _ := hlow
      _ ≤ (b-a)*(3*b^2)*(H*b) := mul_le_mul_of_nonneg_right hd₁ (mul_nonneg hH hb.le)
      _ = _ := by rw [← hcb]; ring
    have hh := (mul_le_mul_iff_right₀ (hs.1.trans_lt hst)).mp hbound
    nlinarith only [hh, mul_nonneg hH (sub_nonneg.mpr hab)]
  · have hsec := conv.secant_mono_aux1 hs1 (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) hst
      (show t < 1 by linarith [ht.2])
    have hroot : (1-s)^(1/3:ℝ) ≤ 1 := Real.rpow_le_one (by linarith [hs1.2]) (by linarith [hs.1]) (by norm_num)
    have hu : F 1-F s ≤ H := ((abs_le.mp (right s hs1)).2).trans (by simpa using mul_le_mul_of_nonneg_left hroot hH)
    have hhigh : (1-s)*(F t-F s) ≤ (t-s)*H := by
      nlinarith only [hsec, mul_nonneg (sub_nonneg.mpr hst.le) (sub_nonneg.mpr hu)]
    have hbound : (1-s)*(F t-F s) ≤ (1-s)*(6*H*(b-a)) := calc
      _ ≤ _ := hhigh
      _ ≤ ((b-a)*3)*H := mul_le_mul_of_nonneg_right hd₂ hH
      _ ≤ _ := by
        have hhalf : 0 ≤ 1/2-s := sub_nonneg.mpr hs.2
        nlinarith only [mul_nonneg hhalf (mul_nonneg hH (sub_nonneg.mpr hab))]
    exact (mul_le_mul_iff_right₀ (show 0 < 1-s by linarith [hs.2])).mp hbound

/-- On [0,1], changing from cube roots to p-th roots costs p/3. -/
theorem cubeRoot_distance_le_root {p s t : ℝ} (hp : 3 ≤ p)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |t^(1/3:ℝ)-s^(1/3:ℝ)| ≤ (p/3)*|t^(1/p)-s^(1/p)| := by
  let k := p/3
  have hk : 1 ≤ k := by dsimp [k]; linarith
  have hpi : 0 < 1/p := one_div_pos.mpr (by linarith)
  have hmem {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : x^(1/p) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨Real.rpow_nonneg hx.1 _, Real.rpow_le_one hx.1 hx.2 hpi.le⟩
  have hd (x : ℝ) : HasDerivAt (fun u : ℝ => u^k) (k*x^(k-1)) x := Real.hasDerivAt_rpow_const (Or.inr hk)
  have hb (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : ‖k*x^(k-1)‖ ≤ k := by
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx.1 _))]
    simpa using mul_le_mul_of_nonneg_left (Real.rpow_le_one hx.1 hx.2 (sub_nonneg.mpr hk))
      (show 0 ≤ k by linarith)
  have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hd x).hasDerivWithinAt) hb (hmem hs) (hmem ht)
  have hpn : p ≠ 0 := by linarith
  have hpk : (1/p)*k = 1/3 := by dsimp [k]; field_simp [hpn]
  simpa only [Real.norm_eq_abs, ← Real.rpow_mul ht.1, ← Real.rpow_mul hs.1, hpk] using he

open TSGA.Localization

open scoped Matrix.Norms.Frobenius in
/-- The fixed-axis estimate holds along the entire segment between any two spin
matrices of trace r. Opposite pure projectors give occupancies r(1−t) and rt. -/
theorem fixedCharge_segment_cubeRoot {e : SpinMatrix → ℝ} {r H : ℝ} (hr : 0 < r) (hH : 0 ≤ H)
    (conv : ConvexOn ℝ (fixedCharge r) e) (holder : ∀ P ∈ fixedCharge r, ∀ Q ∈ fixedCharge r,
      |e P-e Q| ≤ H*(hilbertSchmidt (P-Q)/r)^(1/3:ℝ))
    {P Q : SpinMatrix} (hP : P ∈ fixedCharge r) (hQ : Q ∈ fixedCharge r)
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) :
    |e (AffineMap.lineMap P Q t)-e (AffineMap.lineMap P Q s)| ≤
      12*H*|t^(1/3:ℝ)-s^(1/3:ℝ)| := by
  let g : ℝ →ᵃ[ℝ] SpinMatrix := AffineMap.lineMap P Q
  have hg {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) : g u ∈ fixedCharge r :=
    conv.1.lineMap_mem hP hQ hu
  have hc : ConvexOn ℝ (Set.Icc 0 1) (e ∘ g) :=
    (conv.comp_affineMap g).subset (fun _ hu => hg hu) (convex_Icc _ _)
  have hdist : ‖Q-P‖ ≤ 2*r := calc
    _ ≤ ‖Q‖ + ‖P‖ := norm_sub_le _ _
    _ ≤ Q.trace.re + P.trace.re := by
      rw [← hs_eq_norm, ← hs_eq_norm]
      exact add_le_add (hilbertSchmidt_le_trace hQ.1) (hilbertSchmidt_le_trace hP.1)
    _ = _ := by rw [hP.2, hQ.2]; ring
  have hpath (u v : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
      |e (g u)-e (g v)| ≤ (2*H)*|u-v|^(1/3:ℝ) := by
    have hd : g u - g v = (u-v) • (Q-P) := by
      simp only [g, AffineMap.lineMap_apply_module', sub_smul]
      abel
    have hb : hilbertSchmidt (g u-g v)/r ≤ 2*|u-v| := by
      rw [div_le_iff₀ hr, hd, hs_eq_norm, norm_smul, Real.norm_eq_abs]
      linarith only [mul_le_mul_of_nonneg_left hdist (abs_nonneg (u-v))]
    have hpow := Real.rpow_le_rpow (div_nonneg (Real.sqrt_nonneg _) hr.le) hb (by norm_num : (0:ℝ) ≤ 1/3)
    rw [Real.mul_rpow (by norm_num) (abs_nonneg _)] at hpow
    have htwo : (2:ℝ)^(1/3:ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1/3:ℝ) ≤ 1)
    calc
      _ ≤ _ := holder _ (hg hu) _ (hg hv)
      _ ≤ H*(2^(1/3:ℝ)*|u-v|^(1/3:ℝ)) := mul_le_mul_of_nonneg_left hpow hH
      _ ≤ _ := by
        rw [← mul_assoc, mul_comm 2 H]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo hH) (Real.rpow_nonneg (abs_nonneg _) _)
  have hleft (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) : |e (g u)-e (g 0)| ≤ 2*H*u^(1/3:ℝ) := by
    simpa only [sub_zero, abs_of_nonneg hu.1] using hpath u 0 hu (by norm_num)
  have hright (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) : |e (g 1)-e (g u)| ≤ 2*H*(1-u)^(1/3:ℝ) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hu.2)] using hpath 1 u (by norm_num) hu
  have hh := convex_minority_cubeRoot (H := 2*H) (by positivity) hc hleft hright hs ht
  rw [show 12*H = 6*(2*H) by ring]
  exact hh

/-- A fully polarized spin at density r belongs to the fixed-charge slice. -/
theorem pureSpin_fixedCharge {r : ℝ} (hr : 0 ≤ r) {n : Fin 3 → ℝ} (hn : spinDot n n = 1) :
    r • spinProjector n ∈ fixedCharge r := by
  have hstar : star (spinProjector n) = spinProjector n := by
    simp [spinProjector, star_smul, pauli_star]
  have hsq : spinProjector n * spinProjector n = spinProjector n := by
    simp only [spinProjector, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one, pauli_sq hn]
    module
  have hpos := Matrix.posSemidef_conjTranspose_mul_self (spinProjector n)
  change (star (spinProjector n) * spinProjector n).PosSemidef at hpos
  rw [hstar, hsq] at hpos
  refine ⟨hpos.smul hr, ?_⟩
  have htrace : (pauli n).trace = 0 := by simp [pauli, Matrix.trace_fin_two]
  simp [spinProjector, Matrix.trace_smul, Matrix.trace_add, htrace, Complex.real_smul]

/-- Opposite fully polarized matrices give the two physical occupancies r(1−t) and rt
on the fixed spin axis n. -/
def minoritySpinMatrix (r : ℝ) (n : Fin 3 → ℝ) (t : ℝ) : SpinMatrix :=
  AffineMap.lineMap (r • spinProjector n) (r • spinProjector (-n)) t

end TSGA.SSW
