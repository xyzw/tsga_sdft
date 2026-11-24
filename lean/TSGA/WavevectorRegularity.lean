import TSGA.SSWGas
import TSGA.SSWRate
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Wavevector regularity of the SSW energy

Proposition E.2(iii) follows by comparing adjacent secants of the corrected
radial energy. The choice of secant length recovers both density powers.
-/

noncomputable section

namespace TSGA.SSW

open Set
open scoped ComplexOrder

private theorem radial_secant {G : ℝ → ℝ} {r a b K x y : ℝ}
    (hc : ConcaveOn ℝ univ G) (hm : AntitoneOn G (Ici 0))
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hg : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → G s - G t ≤ 2*K*r*(a^2+b^2) + r*t^2/4)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    |(G x + r*x^2/4) - (G y + r*y^2/4)| ≤ (2*K+1)*r*(y+a+b)*(y-x) := by
  rcases hxy.eq_or_lt with rfl | hlt
  · simp
  have hy := hx.trans hlt.le
  let h := y+a+b
  have hp : 0 < h := by dsimp [h]; positivity
  have hsum : a^2 + b^2 ≤ h^2 := by
    dsimp [h]
    nlinarith only [sq_nonneg y, mul_nonneg hy ha.le, mul_nonneg hy hb, mul_nonneg ha.le hb]
  have hdist : (y+h)^2 ≤ 4*h^2 := by
    have hh : y ≤ h := by dsimp [h]; linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) (by linarith : 0 ≤ 3*h+y)]
  let L := (2*K+1)*r*h
  have hstep : G y - G (y+h) ≤ L*h := by
    have hs := hg y (y+h) hy (add_nonneg hy hp.le)
    dsimp [L]
    nlinarith only [hs, mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*K*r by positivity),
      mul_le_mul_of_nonneg_left hdist hr]
  have hs := hc.slope_anti_adjacent (mem_univ x) (mem_univ (y+h)) hlt (lt_add_of_pos_right y hp)
  rw [add_sub_cancel_left] at hs
  have hbound : -L ≤ (G (y+h) - G y)/h := (le_div_iff₀ hp).2 (by linarith only [hstep])
  have hl := (le_div_iff₀ (sub_pos.mpr hlt)).1 (hbound.trans hs)
  have hmono := hm hx hy hlt.le
  have hquadr : 0 ≤ r * (y^2-x^2) := mul_nonneg hr (sub_nonneg.mpr (sq_le_sq' (by linarith) hlt.le))
  have hL : r*(x+y)/4 ≤ L := by
    dsimp [L, h]
    nlinarith only [mul_nonneg (mul_nonneg hK hr) hy, mul_nonneg (mul_nonneg hK hr) ha.le,
      mul_nonneg (mul_nonneg hK hr) hb, mul_nonneg hr ha.le, mul_nonneg hr hb,
      mul_nonneg hr (sub_nonneg.mpr hlt.le), mul_nonneg hr hy]
  change _ ≤ L*(y-x)
  apply abs_le.mpr
  constructor
  · nlinarith only [hmono, mul_le_mul_of_nonneg_right hL (sub_nonneg.mpr hlt.le)]
  · linarith only [hl, hquadr]

/-- The rate constant is uniform over spin parameters. The angular average
identifies the values at both wavevectors with the radial values; the
non-increasing corrected energy comes from Proposition 3.2. -/
theorem wavevector_lipschitz {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (rate : FiniteRateTiling E η K) {M : SpinMatrix} (hM : M.PosSemidef) (hr : 0 < M.trace.re)
    (concave : ConcaveOn ℝ univ (fun q => sswEnergy E η M q - ‖q‖^2/4*M.trace.re))
    (q q' : Position) :
    |sswEnergy E η M q - sswEnergy E η M q'| ≤ (2*K+1) *
      (M.trace.re ^ (7/6 : ℝ) + M.trace.re ^ (4/3 : ℝ) + M.trace.re * max ‖q‖ ‖q'‖) * ‖q-q'‖ := by
  let r := M.trace.re
  let e : Position := PiLp.single 2 0 1
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  let f := sswEnergy E η M
  let G := fun t : ℝ => f (t • e) - ‖t • e‖^2/4*r
  have hc : ConcaveOn ℝ univ G := by
    simpa [Function.comp_def, LinearMap.toSpanSingleton_apply, G, f, r] using
      concave.comp_linearMap (LinearMap.toSpanSingleton ℝ _ e)
  have hm : AntitoneOn G (Ici 0) := Thermodynamic.correctedEnergyDensity_antitoneOn_ray concave
    (fun _ _ heq => sswEnergy_isotropic E η M heq) e
  let a := r ^ (1/6 : ℝ)
  let b := r ^ (1/3 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hr _
  have hb : 0 ≤ b := Real.rpow_nonneg hr.le _
  have hK := zero_le_one.trans rate.one_le
  have hpow (u v : ℝ) : (r ^ u) ^ v = r ^ (u*v) := (Real.rpow_mul hr.le u v).symm
  have hasq : a^2 = r ^ (1/3 : ℝ) := by
    rw [show a^2 = a ^ (2:ℝ) by norm_cast, hpow]; norm_num
  have hbsq : b^2 = r ^ (2/3 : ℝ) := by
    rw [show b^2 = b ^ (2:ℝ) by norm_cast, hpow]; norm_num
  have hnorm (t : ℝ) (ht : 0 ≤ t) : ‖t • e‖ = t := by simp [norm_smul, he, Real.norm_of_nonneg ht]
  have hg : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → G s - G t ≤ 2*K*r*(a^2+b^2) + r*t^2/4 := by
    intro s t hs ht
    have hup := (rate.ssw_power_bounds hM 0).2
    have hlo := (rate.ssw_power_bounds hM (t • e)).1
    have hgs := hm (show 0 ∈ Ici (0:ℝ) by simp) hs hs
    change G s ≤ G 0 at hgs
    have hz : G 0 = f 0 := by simp [G]
    rw [hz] at hgs
    change f 0 ≤ K*(r * rateGrowth r 0) at hup
    simp only [rateGrowth, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hup
    change -K*(r*r^(1/3:ℝ)) ≤ f (t • e) at hlo
    rw [show G t = f (t • e) - t^2/4*r by dsimp only [G]; rw [hnorm t ht]]
    rw [← hasq, ← hbsq] at hup
    rw [← hasq] at hlo
    nlinarith only [hgs, hup, hlo, mul_nonneg (mul_nonneg hK hr.le) (sq_nonneg b)]
  have hra : r*a = r ^ (7/6:ℝ) := by
    rw [show (7/6:ℝ) = 1 + 1/6 by norm_num, Real.rpow_add hr, Real.rpow_one]
  have hrb : r*b = r ^ (4/3:ℝ) := by
    rw [show (4/3:ℝ) = 1 + 1/3 by norm_num, Real.rpow_add hr, Real.rpow_one]
  have ordered (u v : Position) (huv : ‖u‖ ≤ ‖v‖) :
      |f u - f v| ≤ (2*K+1) * (r^(7/6:ℝ) + r^(4/3:ℝ) + r*max ‖u‖ ‖v‖) * ‖u-v‖ := by
    have h := radial_secant hc hm hr.le ha hb hK hg (norm_nonneg u) huv
    have hrad (z : Position) : G ‖z‖ + r*‖z‖^2/4 = f z := by
      dsimp only [G]
      have hz := hnorm ‖z‖ (norm_nonneg z)
      rw [hz, show f (‖z‖ • e) = f z from sswEnergy_isotropic E η M hz]
      ring
    rw [hrad u, hrad v] at h
    have hd : ‖v‖-‖u‖ ≤ ‖u-v‖ := by simpa only [norm_sub_rev v u] using norm_sub_norm_le v u
    have hfac : 0 ≤ (2*K+1)*r*(‖v‖+a+b) := by positivity
    rw [max_eq_right huv, ← hra, ← hrb]
    calc
      _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left hd hfac)
      _ = _ := by ring
  rcases le_total ‖q‖ ‖q'‖ with h | h
  · exact ordered q q' h
  · simpa only [abs_sub_comm (f q') (f q), norm_sub_rev q' q, max_comm ‖q'‖ ‖q‖] using ordered q' q h

theorem SSWGasTheorem.wavevector_lipschitz {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (gas : SSWGasTheorem (referenceEnergies E η)) (rate : FiniteRateTiling E η K)
    {M : SpinMatrix} {ζ θ : ℝ} (spin : SpinParameters M ζ θ) (q q' : Position) :
    |sswEnergy E η M q - sswEnergy E η M q'| ≤ (2*K+1) *
      (M.trace.re ^ (7/6 : ℝ) + M.trace.re ^ (4/3 : ℝ) + M.trace.re * max ‖q‖ ‖q'‖) * ‖q-q'‖ :=
  TSGA.SSW.wavevector_lipschitz rate spin.positive spin.charge_pos (gas.concave spin) q q'

/-- The Bloch-vector parameters exist for every positive spin matrix of
positive trace, including zero magnetization and full polarization. -/
theorem exists_spinParameters {M : SpinMatrix} (hM : M.PosSemidef) (hr : 0 < M.trace.re) :
    ∃ ζ θ, SpinParameters M ζ θ := by
  let m := thirdMagnetization M
  let n := Real.sqrt (‖transverseMagnetization M‖ ^ 2 + m ^ 2)
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  have hsq : n^2 = ‖transverseMagnetization M‖ ^ 2 + m^2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hdet : 0 ≤ M.det.re := (RCLike.nonneg_iff.mp hM.det_nonneg).1
  have hoff : star (M 1 0) * M 1 0 = (Complex.normSq (M 1 0) : ℂ) :=
    Complex.normSq_eq_conj_mul_self.symm
  rw [Matrix.det_fin_two, ← hM.isHermitian.apply 0 1, hoff] at hdet
  have him (i : Fin 2) : (M i i).im = 0 := (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := i))).2
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, him, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq] at hdet
  have hnr : n ≤ M.trace.re := by
    apply (sq_le_sq₀ hn hr.le).1
    rw [hsq]
    simp only [transverseMagnetization, norm_mul, Complex.norm_ofNat, m, thirdMagnetization,
      Matrix.trace_fin_two, Complex.add_re]
    nlinarith only [hdet]
  have hm : |m| ≤ n := (sq_le_sq₀ (abs_nonneg m) hn).1 (by rw [sq_abs, hsq]; linarith [sq_nonneg ‖transverseMagnetization M‖])
  have harg : -1 ≤ m/n ∧ m/n ≤ 1 := by
    rcases hn.eq_or_lt with hz | hp
    · simp [← hz]
    · constructor
      · exact (le_div_iff₀ hp).2 (by linarith only [(abs_le.mp hm).1])
      · exact (div_le_one hp).2 (abs_le.mp hm).2
  refine ⟨n / M.trace.re, Real.arccos (m/n), hM, hr, ⟨div_nonneg hn hr.le, (div_le_one hr).2 hnr⟩,
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, (div_mul_cancel₀ n hr.ne').symm, ?_⟩
  change m = _ * _ * Real.cos (Real.arccos (m/n))
  rw [div_mul_cancel₀ _ hr.ne', Real.cos_arccos harg.1 harg.2]
  rcases hn.eq_or_lt with hz | hp
  · have hmz : m = 0 := abs_nonpos_iff.mp (hm.trans_eq hz.symm)
    simp [hmz]
  · field_simp [hp.ne']

/-- Proposition E.2(iii) for all positive semidefinite matrices, including
the vacuum. The same constant works at every charge and wavevector. -/
theorem SSWGasTheorem.wavevector_lipschitz_psd {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (gas : SSWGasTheorem (referenceEnergies E η)) (rate : FiniteRateTiling E η K)
    (M : SpinMatrix) (hM : M.PosSemidef) (q q' : Position) :
    |sswEnergy E η M q - sswEnergy E η M q'| ≤ (2*K+1) *
      (M.trace.re ^ (7/6 : ℝ) + M.trace.re ^ (4/3 : ℝ) + M.trace.re * max ‖q‖ ‖q'‖) * ‖q-q'‖ := by
  by_cases hr : 0 < M.trace.re
  · obtain ⟨ζ, θ, h⟩ := exists_spinParameters hM hr
    exact gas.wavevector_lipschitz rate h q q'
  · have hpos := RCLike.nonneg_iff.mp hM.trace_nonneg
    have hzero := hM.trace_eq_zero_iff.mp (Complex.ext (le_antisymm (le_of_not_gt hr) hpos.1) hpos.2)
    have hz (k : Position) : sswEnergy E η 0 k = 0 := gas.vacuum_ssw k
    simp [hzero, hz, Real.zero_rpow (by norm_num : (7/6 : ℝ) ≠ 0),
      Real.zero_rpow (by norm_num : (4/3 : ℝ) ≠ 0)]

/-- In a frozen tile, the remaining energy comparison at fixed wavevector
only changes the matrix. The full cost of varying the wavevector is explicit. -/
theorem SSWGasTheorem.compare_matrix_wavevector {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (gas : SSWGasTheorem (referenceEnergies E η)) (rate : FiniteRateTiling E η K)
    (B M : SpinMatrix) (hM : M.PosSemidef) (q k : Position) :
    |sswEnergy E η B q - sswEnergy E η M k| ≤ |sswEnergy E η B q - sswEnergy E η M q| +
      (2*K+1) * (M.trace.re ^ (7/6 : ℝ) + M.trace.re ^ (4/3 : ℝ) +
        M.trace.re * max ‖q‖ ‖k‖) * ‖q-k‖ := by
  exact (abs_sub_le ..).trans (add_le_add_right (gas.wavevector_lipschitz_psd rate M hM q k) _)

/-- The known uniform-gas bounds and the spin population inequalities yield
the exact Coulomb and Thomas–Fermi constants of Proposition E.2(i). -/
theorem SSWGasTheorem.bounds_of_uniform_gas {F : GasEnergies} (gas : SSWGasTheorem F)
    {cLO cTF : ℝ} (ueg : ∀ A : SpinMatrix, A.PosSemidef →
      -cLO * A.trace.re ^ (4/3 : ℝ) ≤ F.ueg A ∧ F.ueg A ≤ cTF * A.trace.re ^ (5/3 : ℝ))
    (M : SpinMatrix) (hM : M.PosSemidef) (q : Position) :
    -cLO * M.trace.re ^ (4/3 : ℝ) ≤ F.ssw M q ∧
    F.ssw M q ≤ cTF * M.trace.re ^ (5/3 : ℝ) + M.trace.re * ‖q‖^2/4 := by
  by_cases hρ : 0 < M.trace.re
  · obtain ⟨ζ, θ, h⟩ := exists_spinParameters hM hρ
    have hlo := (gas.bounds h).lower q
    rw [← h.diagonal_eq_populations, F.zero_mode _ h.diagonal_positive] at hlo
    have hdi := (ueg (diagonalSpin M) h.diagonal_positive).1
    rw [trace_diagonalSpin] at hdi
    have hup := (gas.bounds h).upper q
    rw [F.zero_mode M hM] at hup
    have hk : 0 ≤ M.trace.re * ‖q‖^2/4 := by positivity
    exact ⟨hdi.trans hlo, by
      nlinarith only [hup, (ueg M hM).2, mul_nonneg hk (mul_nonneg (sq_nonneg ζ) (sq_nonneg (Real.cos θ)))]⟩
  · have ht := RCLike.nonneg_iff.mp hM.trace_nonneg
    have hz := hM.trace_eq_zero_iff.mp (Complex.ext (le_antisymm (le_of_not_gt hρ) ht.1) ht.2)
    simp [hz, gas.vacuum_ssw, Real.zero_rpow (by norm_num : (4/3 : ℝ) ≠ 0),
      Real.zero_rpow (by norm_num : (5/3 : ℝ) ≠ 0)]

end TSGA.SSW
