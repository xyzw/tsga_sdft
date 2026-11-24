import TSGA.WavevectorRegularity
import TSGA.SpectralLipschitz
import TSGA.MinorityRegularity
import Mathlib.Analysis.Matrix.Normed

/-! # Matrix regularity of the SSW gas along rays

The scaling law initially changes the wavevector together with the density.
The wavevector estimate restores the original wavevector with an error
proportional to the amount of density removed.
-/

noncomputable section

namespace TSGA.SSW

open scoped ComplexOrder

private theorem scaled_difference {X Y G H α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hX : -G ≤ X) (hX' : X ≤ H)
    (hl : α ^ (5/3 : ℝ) * (X + G) - α ^ (4/3 : ℝ) * G ≤ Y)
    (hu : Y ≤ α ^ (4/3 : ℝ) * X) :
    |Y - X| ≤ 2 * (1 - α) * (G + H) := by
  have h4 := Real.rpow_le_one hα hα' (by norm_num : (0:ℝ) ≤ 4/3)
  have h5 := Real.rpow_le_one hα hα' (by norm_num : (0:ℝ) ≤ 5/3)
  have h54 := Real.rpow_le_rpow_of_exponent_ge' hα hα' (by norm_num : (0:ℝ) ≤ 4/3)
    (by norm_num : (4/3:ℝ) ≤ 5/3)
  have h25 : α ^ (2:ℕ) ≤ α ^ (5/3:ℝ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge' hα hα'
      (by norm_num : (0:ℝ) ≤ 5/3) (by norm_num : (5/3:ℝ) ≤ 2)
  have hle : 1 - α^(5/3:ℝ) ≤ 2 * (1 - α) := by nlinarith only [h25, sq_nonneg (1-α)]
  have hB := mul_le_mul_of_nonneg_right hle (add_nonneg hG hH)
  apply abs_le.mpr
  constructor
  · linarith only [hl, hB, mul_le_mul_of_nonneg_left hX' (sub_nonneg.mpr h5),
      mul_le_mul_of_nonneg_right h4 hG]
  · linarith only [hu, hB, mul_le_mul_of_nonneg_left hX (sub_nonneg.mpr h4),
      mul_le_mul_of_nonneg_right h54 hG, mul_nonneg (sub_nonneg.mpr h5) hH]

private theorem wavevector_cross_terms {r z : ℝ} (hr : 0 ≤ r) :
    (r ^ (7/6 : ℝ) + r ^ (4/3 : ℝ) + r*z)*z ≤
      2 * (r ^ (4/3 : ℝ) + r ^ (5/3 : ℝ) + r*z^2) := by
  have hy (s : ℝ) (hs : 0 ≤ s) :
      2 * r ^ (1+s) * z ≤ r ^ (1+2*s) + r*z^2 := by
    rw [Real.rpow_add_of_nonneg hr zero_le_one hs,
      Real.rpow_add_of_nonneg hr zero_le_one (mul_nonneg (by norm_num) hs),
      mul_comm (2:ℝ) s, Real.rpow_mul hr, Real.rpow_two, Real.rpow_one]
    nlinarith only [mul_nonneg hr (sq_nonneg (r^s-z))]
  have h₁ := hy (1/6) (by norm_num)
  have h₂ := hy (1/3) (by norm_num)
  norm_num at h₁ h₂
  linarith only [h₁, h₂, Real.rpow_nonneg hr (4/3), Real.rpow_nonneg hr (5/3)]

private theorem wavevector_ray_difference (e : SpinMatrix → Position → ℝ) {M : SpinMatrix}
    (hM : M.PosSemidef) (q : Position) {α W : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) (hW : 0 ≤ W)
    (wave : ∀ k k' : Position, |e (α • M) k - e (α • M) k'| ≤
      W * ((α • M).trace.re ^ (7/6:ℝ) + (α • M).trace.re ^ (4/3:ℝ) +
        (α • M).trace.re * max ‖k‖ ‖k'‖) * ‖k-k'‖) :
    |e (α • M) q - e (α • M) (α^(1/3:ℝ) • q)| ≤ W*(1-α)*
      (2*(M.trace.re^(4/3:ℝ)+M.trace.re^(5/3:ℝ)+M.trace.re*‖q‖^2)) := by
  let r := M.trace.re
  let z := ‖q‖
  let A := r^(4/3:ℝ) + r^(5/3:ℝ) + r*z^2
  let t := α ^ (1/3:ℝ)
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hz : 0 ≤ z := norm_nonneg _
  have h₄ := Real.rpow_nonneg hr (4/3)
  have h₅ := Real.rpow_nonneg hr (5/3)
  have hzz := mul_nonneg hr (sq_nonneg z)
  have hA : 0 ≤ A := add_nonneg (add_nonneg h₄ h₅) hzz
  have ht₀ : 0 ≤ t := Real.rpow_nonneg hα _
  have ht : t ≤ 1 := Real.rpow_le_one hα hα' (by norm_num)
  have hαt : α ≤ t := Real.self_le_rpow_of_le_one hα hα' (by norm_num)
  have htr : (α • M).trace.re = α*r := by simp [r, Complex.real_smul]
  have htq : ‖t • q‖ = t*z := by rw [norm_smul, Real.norm_of_nonneg ht₀]
  have hdist : ‖q - t • q‖ = (1-t)*z := by
    rw [show q - t • q = (1-t) • q by rw [sub_smul, one_smul],
      norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht)]
  have hαr : α*r ≤ r := mul_le_of_le_one_left hr hα'
  have href : (α*r)^(7/6:ℝ) + (α*r)^(4/3:ℝ) + α*r*z ≤ r^(7/6:ℝ) + r^(4/3:ℝ) + r*z := by
    exact add_le_add (add_le_add (Real.rpow_le_rpow (mul_nonneg hα hr) hαr (by norm_num))
      (Real.rpow_le_rpow (mul_nonneg hα hr) hαr (by norm_num))) (mul_le_mul_of_nonneg_right hαr hz)
  have hw := wave q (t • q)
  rw [htr, htq, max_eq_left (mul_le_of_le_one_left hz ht), hdist] at hw
  have hw' : |e (α • M) q - e (α • M) (t • q)| ≤ W * (1-α) * (2*A) := by
    calc
      _ ≤ W * (1-t) * (((α*r)^(7/6:ℝ) + (α*r)^(4/3:ℝ) + α*r*z)*z) := hw.trans_eq (by ring)
      _ ≤ W * (1-t) * (2*A) := mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right href hz).trans (wavevector_cross_terms hr))
        (mul_nonneg hW (sub_nonneg.mpr ht))
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hαt _) hW)
        (mul_nonneg (by norm_num) hA)
  exact hw'

/-- Equation `eq:Lipschitz_ray_SSW` of Proposition E.2(iv), derived from
the two inequalities of (i) and the wavevector inequality of (iii). -/
theorem ray_lipschitz_of_scaling (e : SpinMatrix → Position → ℝ) {M : SpinMatrix}
    (hM : M.PosSemidef) (q : Position) {α lo tf W : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1)
    (hlo : 0 ≤ lo) (htf : 0 ≤ tf) (hW : 0 ≤ W)
    (bounds : -(lo * M.trace.re ^ (4/3:ℝ)) ≤ e M q ∧
      e M q ≤ tf * M.trace.re ^ (5/3:ℝ) + M.trace.re * ‖q‖^2 / 4)
    (scaling : α ^ (5/3:ℝ) * (e M q + lo * M.trace.re ^ (4/3:ℝ)) -
        α ^ (4/3:ℝ) * (lo * M.trace.re ^ (4/3:ℝ)) ≤ e (α • M) (α^(1/3:ℝ) • q) ∧
      e (α • M) (α^(1/3:ℝ) • q) ≤ α^(4/3:ℝ) * e M q)
    (wave : ∀ k k' : Position, |e (α • M) k - e (α • M) k'| ≤
      W * ((α • M).trace.re ^ (7/6:ℝ) + (α • M).trace.re ^ (4/3:ℝ) +
        (α • M).trace.re * max ‖k‖ ‖k'‖) * ‖k-k'‖) :
    |e (α • M) q - e M q| ≤ (2 * (lo + tf + 1) + 2 * W) * (1-α) *
      (M.trace.re ^ (4/3:ℝ) + M.trace.re ^ (5/3:ℝ) + M.trace.re * ‖q‖^2) := by
  let r := M.trace.re
  let z := ‖q‖
  let A := r^(4/3:ℝ) + r^(5/3:ℝ) + r*z^2
  let t := α ^ (1/3:ℝ)
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have h₄ := Real.rpow_nonneg hr (4/3)
  have h₅ := Real.rpow_nonneg hr (5/3)
  have hzz := mul_nonneg hr (sq_nonneg z)
  have hbase : lo*r^(4/3:ℝ) + (tf*r^(5/3:ℝ) + r*z^2/4) ≤ (lo+tf+1)*A := by
    dsimp [A]
    nlinarith only [h₄,h₅,hzz,mul_nonneg hlo h₅,mul_nonneg hlo hzz,mul_nonneg htf h₄,mul_nonneg htf hzz]
  have hs := scaled_difference hα hα' (mul_nonneg hlo h₄)
    (add_nonneg (mul_nonneg htf h₅) (div_nonneg hzz (by norm_num))) bounds.1 bounds.2 scaling.1 scaling.2
  have hsmall := hs.trans (mul_le_mul_of_nonneg_left hbase (mul_nonneg (by norm_num) (sub_nonneg.mpr hα')))
  have hw' := wavevector_ray_difference e hM q hα hα' hW wave
  have hfinal := (abs_sub_le (e (α • M) q) (e (α • M) (t • q)) (e M q)).trans (add_le_add hw' hsmall)
  exact hfinal.trans_eq (by dsimp only [A,r,z]; ring)

open TSGA.Localization

/-- The finite tiling bounds and the proved wavevector inequality also
suffice when the scaling law is supplied for the concrete gas. -/
theorem SSWGasTheorem.ray_lipschitz {E : EnergyFunctional} {η : Mollifier} {K c : ℝ}
    (gas : SSWGasTheorem (referenceEnergies E η)) (rate : FiniteRateTiling E η K)
    (hc : 0 ≤ c) {M : SpinMatrix} (hM : M.PosSemidef) (q : Position)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1)
    (scaling : α^(5/3:ℝ) * (sswEnergy E η M q + c*M.trace.re^(4/3:ℝ)) -
      α^(4/3:ℝ)*c*M.trace.re^(4/3:ℝ) ≤ sswEnergy E η (α • M) (α^(1/3:ℝ) • q) ∧
      sswEnergy E η (α • M) (α^(1/3:ℝ) • q) ≤ α^(4/3:ℝ)*sswEnergy E η M q) :
    |sswEnergy E η (α • M) q - sswEnergy E η M q| ≤ (2*(c+2*K)+2*(2*K+1))*(1-α)*
      (M.trace.re^(4/3:ℝ)+M.trace.re^(5/3:ℝ)+M.trace.re*‖q‖^2) := by
  let r := M.trace.re
  let A := r^(4/3:ℝ) + r^(5/3:ℝ) + r*‖q‖^2
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have h₄ := Real.rpow_nonneg hr (4/3)
  have h₅ := Real.rpow_nonneg hr (5/3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := zero_le_one.trans rate.one_le
  have ht := rate.ssw_power_bounds hM q
  have hpow (s : ℝ) (hs : 0 ≤ s) : r * r^s = r^(1+s) := by
    rw [Real.rpow_add_of_nonneg hr zero_le_one hs, Real.rpow_one]
  have hf : r*r^(1/3:ℝ) = r^(4/3:ℝ) := by rw [hpow _ (by norm_num)]; norm_num
  have hg : r * rateGrowth r q = A := by
    simp only [rateGrowth, A, mul_add, hf, hpow (2/3) (by norm_num), show (1+2/3:ℝ)=5/3 by norm_num]
  change -K*(r*r^(1/3:ℝ)) ≤ _ ∧ _ ≤ K*(r*rateGrowth r q) at ht
  rw [hf, hg] at ht
  have hfloor : -((c+K)*r^(4/3:ℝ)) ≤ sswEnergy E η M q := by
    linarith only [ht.1, mul_nonneg hc h₄]
  have h54 := Real.rpow_le_rpow_of_exponent_ge' hα hα' (by norm_num : (0:ℝ) ≤ 4/3)
    (by norm_num : (4/3:ℝ) ≤ 5/3)
  have scaleLo : α^(5/3:ℝ)*(sswEnergy E η M q+(c+K)*r^(4/3:ℝ)) -
      α^(4/3:ℝ)*((c+K)*r^(4/3:ℝ)) ≤ sswEnergy E η (α • M) (α^(1/3:ℝ) • q) := by
    dsimp only [r] at *
    linarith only [scaling.1, mul_nonneg (sub_nonneg.mpr h54) (mul_nonneg hK h₄)]
  have hscale := scaled_difference hα hα' (mul_nonneg (add_nonneg hc hK) h₄)
    (mul_nonneg hK hA) hfloor ht.2 scaleLo scaling.2
  have hbudget : (c+K)*r^(4/3:ℝ) + K*A ≤ (c+2*K)*A := by
    have h₄' : r^(4/3:ℝ) ≤ A := by
      dsimp [A]
      linarith only [h₅, mul_nonneg hr (sq_nonneg ‖q‖)]
    linarith only [mul_le_mul_of_nonneg_left h₄' (add_nonneg hc hK)]
  have hsmall := hscale.trans (mul_le_mul_of_nonneg_left hbudget (mul_nonneg (by norm_num) (sub_nonneg.mpr hα')))
  have hw := wavevector_ray_difference (sswEnergy E η) hM q hα hα' (by positivity : 0 ≤ 2*K+1)
    (gas.wavevector_lipschitz_psd rate (α • M) (hM.smul hα))
  exact ((abs_sub_le _ _ _).trans (add_le_add hw hsmall)).trans_eq (by dsimp only [A, r]; ring)

open scoped Matrix.Norms.Frobenius in
theorem hs_eq_norm (M : SpinMatrix) : hilbertSchmidt M = ‖M‖ := by
  simp only [hilbertSchmidt, Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow]

open scoped Matrix.Norms.Frobenius in
private theorem hs_split (M N : SpinMatrix) {α : ℝ} (hα : α ≤ 1) :
    hilbertSchmidt (M - α • N) ≤ hilbertSchmidt (M - N) + (1-α) * hilbertSchmidt N := by
  simp only [hs_eq_norm]
  have heq : M - α • N = (M - N) + (1-α) • N := by rw [sub_smul, one_smul]; abel
  rw [heq]
  exact (norm_add_le ..).trans_eq (by rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hα)])

open scoped Matrix.Norms.Frobenius in
theorem hs_sub_comm (M N : SpinMatrix) : hilbertSchmidt (M-N) = hilbertSchmidt (N-M) := by
  simpa only [hs_eq_norm] using norm_sub_rev M N

theorem hilbertSchmidt_le_trace {M : SpinMatrix} (hM : M.PosSemidef) : hilbertSchmidt M ≤ M.trace.re := by
  let h := hM.isHermitian
  let U := h.eigenvectorUnitary
  let D : SpinMatrix := Matrix.diagonal (fun i => (h.eigenvalues i : ℂ))
  have spec : (U : SpinMatrix) * D * star (U : SpinMatrix) = M := h.spectral_theorem.symm
  have hd : (star U : SpinMatrix) * M * ↑U = D := by
    rw [← spec]
    calc
      _ = (star (U : SpinMatrix) * ↑U) * D * (star (U : SpinMatrix) * ↑U) := by simp only [mul_assoc]
      _ = D := by rw [Unitary.coe_star_mul_self, one_mul, mul_one]
  have hnorm : hilbertSchmidt D = hilbertSchmidt M := hd ▸ hs_unitary M U U
  have htrace : M.trace.re = h.eigenvalues 0 + h.eigenvalues 1 := by
    rw [h.trace_eq_sum_eigenvalues, Fin.sum_univ_two, Complex.add_re]
    rfl
  rw [← hnorm, htrace]
  simp [D, hilbertSchmidt, Fin.sum_univ_two, sq_abs]
  apply Real.sqrt_le_iff.mpr
  have h₀ := hM.eigenvalues_nonneg 0
  have h₁ := hM.eigenvalues_nonneg 1
  exact ⟨add_nonneg h₀ h₁, by nlinarith only [mul_nonneg h₀ h₁]⟩

theorem abs_trace_re_le_hilbertSchmidt (M : SpinMatrix) : |M.trace.re| ≤ 2 * hilbertSchmidt M := by
  rw [Matrix.trace_fin_two, Complex.add_re, two_mul]
  exact (abs_add_le ..).trans (add_le_add ((Complex.abs_re_le_norm _).trans (norm_entry_le_hs M 0 0))
    ((Complex.abs_re_le_norm _).trans (norm_entry_le_hs M 1 1)))

private theorem minority_smul {M : SpinMatrix} {ν r α : ℝ} (hα : 0 ≤ α)
    (h : (M - ((ν*r : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef) :
    (α • M - ((ν*(α*r) : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef := by
  have heq : α • (M - ((ν*r : ℝ) : ℂ) • (1 : SpinMatrix)) =
      α • M - ((ν*(α*r) : ℝ) : ℂ) • (1 : SpinMatrix) := by
    rw [smul_sub, ← smul_assoc]
    congr 2
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  exact heq ▸ h.smul hα

private theorem posSemidef_trace_re_zero {M : SpinMatrix} (h : M.PosSemidef) (hz : M.trace.re = 0) : M = 0 :=
  h.trace_eq_zero_iff.mp (Complex.ext hz (RCLike.nonneg_iff.mp h.trace_nonneg).2)

/-- Combine the common-trace estimate with the ray estimate by scaling the
higher-trace matrix down to the lower trace. Both vacuum endpoints are included. -/
theorem matrix_lipschitz_of_fixed_charge_and_ray (e : SpinMatrix → Position → ℝ) (q : Position)
    {ν L R : ℝ} (hν : 0 < ν) (hν' : ν ≤ 1) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (fixed : ∀ {r : ℝ}, 0 < r → ∀ {M N : SpinMatrix}, M ∈ fixedCharge r → N ∈ fixedCharge r →
      (M - ((ν*r : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef →
      (N - ((ν*r : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef →
      |e M q - e N q| ≤ L/ν * (r^(1/3:ℝ) + r^(2/3:ℝ) + ‖q‖^2) * hilbertSchmidt (M-N))
    (ray : ∀ {N : SpinMatrix}, N.PosSemidef → ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 →
      |e (α • N) q - e N q| ≤ R*(1-α)*(N.trace.re^(4/3:ℝ) + N.trace.re^(5/3:ℝ) + N.trace.re*‖q‖^2))
    {M N : SpinMatrix} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (mM : (M - ((ν*M.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef)
    (mN : (N - ((ν*N.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef) :
    |e M q - e N q| ≤ (3*L+2*R)/ν *
      ((max M.trace.re N.trace.re)^(1/3:ℝ) + (max M.trace.re N.trace.re)^(2/3:ℝ) + ‖q‖^2) *
      hilbertSchmidt (M-N) := by
  wlog horder : M.trace.re ≤ N.trace.re generalizing M N
  · simpa only [max_comm N.trace.re M.trace.re, abs_sub_comm (e N q) (e M q), hs_sub_comm N M]
      using this hN hM mN mM (le_of_not_ge horder)
  let r := N.trace.re
  let s := M.trace.re
  let d := hilbertSchmidt (M-N)
  let B := r^(1/3:ℝ) + r^(2/3:ℝ) + ‖q‖^2
  have hr : 0 ≤ r := (RCLike.nonneg_iff.mp hN.trace_nonneg).1
  have hs : 0 ≤ s := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hB : 0 ≤ B := add_nonneg (add_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)) (sq_nonneg _)
  rw [max_eq_right horder]
  change |e M q-e N q| ≤ (3*L+2*R)/ν * B * d
  by_cases hzero : r=0
  · have hMz := posSemidef_trace_re_zero hM (le_antisymm (horder.trans_eq hzero) hs)
    have hNz := posSemidef_trace_re_zero hN hzero
    rw [hMz, hNz, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg (by positivity) hν.le) hB) hd
  have hr' : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
  let α := s/r
  have har : α*r = s := div_mul_cancel₀ _ hzero
  have ha₀ : 0 ≤ α := div_nonneg hs hr
  have ha₁ : α ≤ 1 := (div_le_one hr').mpr horder
  have hsub : (1-α)*r ≤ 2*d := by
    have ht := abs_trace_re_le_hilbertSchmidt (M-N)
    rw [Matrix.trace_sub, Complex.sub_re, abs_of_nonpos (sub_nonpos.mpr horder)] at ht
    dsimp only [d] at *
    linarith only [ht, har]
  have hd' : hilbertSchmidt (M-α • N) ≤ 3*d := by
    have he := (hs_split M N ha₁).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (hilbertSchmidt_le_trace hN) (sub_nonneg.mpr ha₁)) _)
    linarith only [he, hsub]
  have hαtr : (α • N).trace.re = s := by simpa only [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul] using har
  have hfix : |e M q - e (α • N) q| ≤ L/ν*B*(3*d) := by
    by_cases hz : s=0
    · have hm := posSemidef_trace_re_zero hM hz
      have hn := posSemidef_trace_re_zero (hN.smul ha₀) (hαtr.trans hz)
      rw [hm,hn,sub_self,abs_zero]
      exact mul_nonneg (mul_nonneg (div_nonneg hL hν.le) hB) (by positivity)
    have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hf := fixed hs' ⟨hM,rfl⟩ ⟨hN.smul ha₀,hαtr⟩ mM (har ▸ minority_smul ha₀ mN)
    apply hf.trans
    have hB' : s^(1/3:ℝ) + s^(2/3:ℝ) + ‖q‖^2 ≤ B := by
      exact add_le_add_left (add_le_add (Real.rpow_le_rpow hs horder (by norm_num))
        (Real.rpow_le_rpow hs horder (by norm_num))) _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB' (div_nonneg hL hν.le)) hd' (Real.sqrt_nonneg _)
      (mul_nonneg (div_nonneg hL hν.le) hB)
  have hpow (x : ℝ) (hx : 0 ≤ x) : r^(1+x) = r*r^x := by
    rw [Real.rpow_add_of_nonneg hr zero_le_one hx, Real.rpow_one]
  have hvol : N.trace.re^(4/3:ℝ) + N.trace.re^(5/3:ℝ) + N.trace.re*‖q‖^2 = r*B := by
    dsimp only [B]
    change r^(4/3:ℝ) + r^(5/3:ℝ) + _ = _
    rw [show (4/3:ℝ)=1+1/3 by norm_num, show (5/3:ℝ)=1+2/3 by norm_num,
      hpow _ (by norm_num), hpow _ (by norm_num)]
    ring
  have hrad := ray hN ha₀ ha₁
  rw [hvol] at hrad
  have hy := (abs_sub_le (e M q) (e (α • N) q) (e N q)).trans (add_le_add hfix hrad)
  apply hy.trans
  have hx := mul_le_mul_of_nonneg_right hsub (mul_nonneg hR hB)
  have hR' : R ≤ R/ν := (le_div_iff₀ hν).mpr (mul_le_of_le_one_right hR hν')
  have hz := mul_le_mul_of_nonneg_right hR' (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hd) hB)
  rw [add_div, mul_div_assoc (3:ℝ), mul_div_assoc (2:ℝ)]
  linarith only [hx,hz]

/-- Proposition E.2(iv) with the finite-rate tiling constant. Fixed-charge
convexity and the joint coordinate-scaling inequality are the inputs from
parts (ii) and (i); the wavevector comparison is provided by part (iii). -/
theorem SSWGasTheorem.matrix_lipschitz {E : EnergyFunctional} {η : Mollifier} {K c : ℝ}
    (gas : SSWGasTheorem (referenceEnergies E η)) (rate : FiniteRateTiling E η K)
    (hc : 0 ≤ c) (q : Position)
    (conv : ∀ r : ℝ, 0 < r → ConvexOn ℝ (fixedCharge r) (fun P => sswEnergy E η P q))
    (scaling : ∀ {P : SpinMatrix}, P.PosSemidef → ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 →
      α^(5/3:ℝ) * (sswEnergy E η P q + c*P.trace.re^(4/3:ℝ)) -
        α^(4/3:ℝ)*c*P.trace.re^(4/3:ℝ) ≤ sswEnergy E η (α • P) (α^(1/3:ℝ) • q) ∧
      sswEnergy E η (α • P) (α^(1/3:ℝ) • q) ≤ α^(4/3:ℝ)*sswEnergy E η P q)
    {ν : ℝ} (hν : 0 < ν) (hν' : ν ≤ 1/2) {M N : SpinMatrix} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (mM : (M - ((ν*M.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef)
    (mN : (N - ((ν*N.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef) :
    |sswEnergy E η M q - sswEnergy E η N q| ≤ (4*c + 22*K + 4)/ν *
      ((max M.trace.re N.trace.re)^(1/3:ℝ) + (max M.trace.re N.trace.re)^(2/3:ℝ) + ‖q‖^2) *
        hilbertSchmidt (M-N) := by
  have hK : 0 ≤ K := zero_le_one.trans rate.one_le
  have hs := matrix_lipschitz_of_fixed_charge_and_ray (sswEnergy E η) q hν (by linarith)
    (by positivity : 0 ≤ 2*K) (by positivity : 0 ≤ 2*(c+2*K)+2*(2*K+1))
    (fun {r} hr {P Q} hP hQ mP mQ => minority_fixed_charge_lipschitz rate hr hν q (conv r hr) hP hQ mP mQ)
    (fun {P} hP {α} ha ha' => gas.ray_lipschitz rate hc hP q ha ha' (scaling hP ha ha')) hM hN mM mN
  convert hs using 1
  ring

end TSGA.SSW
