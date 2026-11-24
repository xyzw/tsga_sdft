import TSGA.GasConvexity
import TSGA.SSWRate
import TSGA.SpectralLipschitz

/-! # Equal-charge Lipschitz bound for the SSW gas

For spin matrices with a minority-spin margin νρ, the segment from M to N
can be extended by Hilbert–Schmidt distance νρ beyond N inside the positive
cone. Fixed-charge convexity and the gas energy bounds control its secant.
-/

noncomputable section

namespace TSGA.SSW

open Matrix TSGA.Localization
open scoped ComplexOrder

theorem norm_entry_le_hs (H : SpinMatrix) (i j : Fin 2) :
    ‖H i j‖ ≤ hilbertSchmidt H := by
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (f := fun j => ‖H i j‖ ^ 2)
    (fun k _ => sq_nonneg ‖H i k‖) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun k => ∑ j, ‖H k j‖ ^ 2)
      (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖H k j‖) (Finset.mem_univ i))

/-- The Hilbert–Schmidt norm dominates the absolute value of every
eigenvalue. In particular its scalar identity shift makes H positive. -/
theorem hilbertSchmidt_shift_posSemidef {H : SpinMatrix} (hH : H.IsHermitian) :
    (hilbertSchmidt H • (1 : SpinMatrix) + H).PosSemidef := by
  let U := hH.eigenvectorUnitary
  let D : SpinMatrix := diagonal (fun i => (hH.eigenvalues i : ℂ))
  let d := hilbertSchmidt H
  have spec : (U : SpinMatrix) * D * star (U : SpinMatrix) = H := hH.spectral_theorem.symm
  have hUstar : star (U : SpinMatrix) * (U : SpinMatrix) = 1 := Unitary.coe_star_mul_self U
  have hd : (star U : SpinMatrix) * H * ↑U = D := by
    rw [← spec]
    calc
      _ = (star (U : SpinMatrix) * ↑U) * D * (star (U : SpinMatrix) * ↑U) := by simp only [mul_assoc]
      _ = D := by rw [hUstar, one_mul, mul_one]
  have hnorm : hilbertSchmidt D = d := hd ▸ hs_unitary H U U
  have hev (i : Fin 2) : 0 ≤ d + hH.eigenvalues i := by
    have hi := norm_entry_le_hs D i i
    rw [hnorm] at hi
    simp only [D, diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs] at hi
    linarith only [(abs_le.mp hi).1]
  have hs : (d • (1 : SpinMatrix) + D).PosSemidef := by
    have eq : d • (1 : SpinMatrix) + D = diagonal (fun i => ((d+hH.eigenvalues i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D, Matrix.smul_apply, Complex.real_smul]
      · simp [D, hij, diagonal_apply_ne, Matrix.one_apply_ne]
    rw [eq]
    exact PosSemidef.diagonal fun i => RCLike.nonneg_iff.mpr ⟨hev i, rfl⟩
  have h := hs.mul_mul_conjTranspose_same (U : SpinMatrix)
  change ((U : SpinMatrix) * (d • (1 : SpinMatrix) + D) * (star U : SpinMatrix)).PosSemidef at h
  have hU : (U : SpinMatrix) * star (U : SpinMatrix) = 1 := Unitary.coe_mul_star_self U
  rwa [mul_add, add_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, hU, spec] at h

private theorem directional_minority_bound {E : EnergyFunctional} {η : Mollifier} {K ρ ν : ℝ}
    (rate : FiniteRateTiling E η K) (hρ : 0 < ρ) (hν : 0 < ν) (q : Position)
    (conv : ConvexOn ℝ (fixedCharge ρ) (fun A => sswEnergy E η A q)) {M N : SpinMatrix}
    (hM : M ∈ fixedCharge ρ) (hN : N ∈ fixedCharge ρ)
    (minor : (N - ((ν*ρ : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef) :
    sswEnergy E η N q - sswEnergy E η M q ≤
      (2*K/ν) * rateGrowth ρ q * hilbertSchmidt (N-M) := by
  let d := hilbertSchmidt (N-M)
  have hd₀ : 0 ≤ d := Real.sqrt_nonneg _
  rcases hd₀.eq_or_lt with hz | hd
  · have heq : N-M = 0 := by
      ext i j
      exact norm_eq_zero.mp (le_antisymm ((norm_entry_le_hs (N-M) i j).trans_eq hz.symm) (norm_nonneg _))
    rw [sub_eq_zero.mp heq, sub_self, sub_self]
    simp [hilbertSchmidt]
  have hK := zero_le_one.trans rate.one_le
  let t := ν*ρ/d
  let Z := N + t • (N-M)
  have ht : 0 < t := div_pos (mul_pos hν hρ) hd
  have htd : t*d = ν*ρ := div_mul_cancel₀ _ hd.ne'
  have hm : (N - (ν*ρ) • (1 : SpinMatrix)).PosSemidef := by
    have hsm : (ν*ρ) • (1 : SpinMatrix) = ((ν*ρ : ℝ) : ℂ) • (1 : SpinMatrix) := by
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [hsm]
    exact minor
  have hZ : Z ∈ fixedCharge ρ := by
    refine ⟨?_, ?_⟩
    · have h := hm.add ((hilbertSchmidt_shift_posSemidef (hN.1.1.sub hM.1.1)).smul ht.le)
      change (N - (ν*ρ) • (1 : SpinMatrix) + t • (d • (1 : SpinMatrix) + (N-M))).PosSemidef at h
      rw [smul_add, smul_smul, htd, ← add_assoc, sub_add_cancel] at h
      exact h
    · simp only [Z, trace_add, trace_smul, trace_sub, Complex.add_re, Complex.real_smul,
        Complex.re_ofReal_mul, Complex.sub_re, hM.2, hN.2, sub_self, mul_zero, add_zero]
  let lam := 1/(1+t)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hlid : lam + lam*t = 1 := by dsimp [lam]; field_simp [(by linarith : 1+t ≠ 0)]
  have hlamle : lam ≤ 1 := by linarith only [hlid, mul_nonneg hlam ht.le]
  have mix : (1-lam) • M + lam • Z = N := by
    dsimp only [Z]
    rw [smul_add, smul_smul, show lam*t = 1-lam by linarith only [hlid], smul_sub]
    module
  have hmix := conv.2 hM hZ (sub_nonneg.mpr hlamle) hlam (by ring : (1-lam)+lam=1)
  rw [mix] at hmix
  change sswEnergy E η N q ≤ (1-lam)*sswEnergy E η M q + lam*sswEnergy E η Z q at hmix
  have hu := (rate.ssw_power_bounds hZ.1 q).2
  have hl := (rate.ssw_power_bounds hM.1 q).1
  rw [hZ.2] at hu
  rw [hM.2] at hl
  have hg : ρ ^ (1/3 : ℝ) ≤ rateGrowth ρ q := by
    dsimp [rateGrowth]
    linarith only [Real.rpow_nonneg hρ.le (2/3 : ℝ), sq_nonneg ‖q‖]
  have he : sswEnergy E η Z q - sswEnergy E η M q ≤ 2*K*ρ*rateGrowth ρ q := by
    linarith only [hu, hl, mul_le_mul_of_nonneg_left hg (mul_nonneg hK hρ.le)]
  have hweight : lam ≤ d/(ν*ρ) := by
    apply (le_div_iff₀ (mul_pos hν hρ)).2
    rw [← htd, ← mul_assoc]
    exact mul_le_of_le_one_left hd.le (by linarith only [hlid, hlam])
  have heav : 0 ≤ 2*K*ρ*rateGrowth ρ q :=
    mul_nonneg (by positivity) ((Real.rpow_nonneg hρ.le (1/3:ℝ)).trans hg)
  calc
    _ ≤ lam * (sswEnergy E η Z q - sswEnergy E η M q) := by linarith only [hmix]
    _ ≤ lam * (2*K*ρ*rateGrowth ρ q) := mul_le_mul_of_nonneg_left he hlam
    _ ≤ (d/(ν*ρ)) * (2*K*ρ*rateGrowth ρ q) := mul_le_mul_of_nonneg_right hweight heav
    _ = _ := by change _ = (2*K/ν)*rateGrowth ρ q*d; field_simp [hν.ne', hρ.ne']

/-- Equal-trace part of Proposition E.2(iv). The factor 2K/ν is uniform
over the matrices and wavevector when K is the finite tiling constant. -/
theorem minority_fixed_charge_lipschitz {E : EnergyFunctional} {η : Mollifier} {K : ℝ}
    (rate : FiniteRateTiling E η K) {ρ ν : ℝ} (hρ : 0 < ρ) (hν : 0 < ν) (q : Position)
    (conv : ConvexOn ℝ (fixedCharge ρ) (fun A => sswEnergy E η A q)) {M N : SpinMatrix}
    (hM : M ∈ fixedCharge ρ) (hN : N ∈ fixedCharge ρ)
    (mM : (M - ((ν*ρ : ℝ) : ℂ) • (1:SpinMatrix)).PosSemidef)
    (mN : (N - ((ν*ρ : ℝ) : ℂ) • (1:SpinMatrix)).PosSemidef) :
    |sswEnergy E η M q - sswEnergy E η N q| ≤
      (2*K/ν) * (ρ^(1/3:ℝ) + ρ^(2/3:ℝ) + ‖q‖^2) * hilbertSchmidt (M-N) := by
  have h1 := directional_minority_bound rate hρ hν q conv hM hN mN
  have h2 := directional_minority_bound rate hρ hν q conv hN hM mM
  have heq : hilbertSchmidt (N-M) = hilbertSchmidt (M-N) := by
    simp only [hilbertSchmidt, Matrix.sub_apply, norm_sub_rev (N _ _) (M _ _)]
  rw [heq] at h1
  exact abs_le.mpr ⟨by unfold rateGrowth at h1; linarith only [h1], h2⟩

end TSGA.SSW
