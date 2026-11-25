import TSGA.MainTheorem
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The rescaled LSDA bound

The density at length `L` is evaluated at `x / L`. Its matrix power
gradients acquire the factor `1 / L` and integrals acquire `L³`.
-/

noncomputable section

namespace TSGA

open MeasureTheory MeasureTheory.Measure
open scoped ContDiff ENNReal

def Density.dilate (D : Density) (L : ℝ) : Density :=
  ⟨fun x => D.matrix (L⁻¹ • x), fun x => D.positive (L⁻¹ • x)⟩

def dilatedGradient (G : MatrixGradient) (L : ℝ) : MatrixGradient :=
  fun x i j k => L⁻¹ • G (L⁻¹ • x) i j k

@[simp] theorem Density.charge_dilate (D : Density) (L : ℝ) (x : Position) :
    (D.dilate L).charge x = D.charge (L⁻¹ • x) := rfl

@[simp] theorem Density.power_dilate (D : Density) (L a : ℝ) (x : Position) :
    (D.dilate L).power a x = D.power a (L⁻¹ • x) := rfl

theorem matrixGradNorm_dilate (G : MatrixGradient) {L : ℝ} (hL : 0 < L) (x : Position) :
    matrixGradNorm (dilatedGradient G L) x = L⁻¹ * matrixGradNorm G (L⁻¹ • x) := by
  unfold matrixGradNorm
  simp only [dilatedGradient, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hL.le)]

private theorem dilation_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Position → V) {L : ℝ} (hL : 0 < L) :
    (∫ x, f (L⁻¹ • x)) = L ^ 3 • ∫ x, f x := by
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    Measure.integral_comp_inv_smul_of_nonneg volume f hL.le

private theorem dilation_locallyIntegrable {f : Position → ℂ}
    (hf : LocallyIntegrableOn f Set.univ) {L : ℝ} (hL : 0 < L) :
    LocallyIntegrableOn (fun x => f (L⁻¹ • x)) Set.univ := by
  apply (locallyIntegrableOn_iff isOpen_univ.isLocallyClosed).2
  intro k _ hk
  let e : Position ≃ₜ Position := Homeomorph.smul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hL.ne')).unit : ℝˣ)
  have hc : IsCompact (e '' k) := hk.image e.continuous
  have hi := (integrable_indicator_iff hc.measurableSet).2
    (hf.integrableOn_compact_subset (Set.subset_univ _) hc)
  apply (integrable_indicator_iff hk.measurableSet).1
  have ht (x : Position) : (e '' k).indicator f (L⁻¹ • x) =
      k.indicator (fun y => f (L⁻¹ • y)) x := by
    change (e '' k).indicator f (e x) = _
    by_cases hx : x ∈ k <;> simp [Set.indicator, hx]
    rfl
  simpa only [ht] using hi.comp_smul (inv_ne_zero hL.ne')

/-- Affine pullback of one distributional coordinate derivative, proved
by applying the original integration-by-parts identity to `ψ(L • x)`. -/
theorem WeakPartialOn.dilate {i : Fin 3} {u du : Position → ℂ}
    (h : WeakPartialOn Set.univ i u du) {L : ℝ} (hL : 0 < L) :
    WeakPartialOn Set.univ i (fun x => u (L⁻¹ • x)) (fun x => L⁻¹ • du (L⁻¹ • x)) := by
  refine ⟨dilation_locallyIntegrable h.1 hL, (dilation_locallyIntegrable h.2.1 hL).smul L⁻¹, ?_⟩
  intro ψ hψ hc _
  let A : Position →L[ℝ] Position := L • ContinuousLinearMap.id ℝ Position
  let χ (y : Position) := ψ (A y)
  let v : Position := PiLp.single 2 i 1
  have hχ : ContDiff ℝ ∞ χ := hψ.comp A.contDiff
  have hχc : HasCompactSupport χ := hc.comp_homeomorph
    (Homeomorph.smul ((isUnit_iff_ne_zero.mpr hL.ne').unit : ℝˣ))
  have hdχ (y : Position) : fderiv ℝ χ y v = L * fderiv ℝ ψ (L • y) v := by
    have hfd := ((hψ.differentiable (by simp) (A y)).hasFDerivAt.comp y A.hasFDerivAt).fderiv
    change (fderiv ℝ (ψ ∘ A) y) v = _
    rw [hfd, ContinuousLinearMap.comp_apply]
    exact map_smul (fderiv ℝ ψ (A y)) L v
  have hw := h.2.2 χ hχ hχc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at hw ⊢
  have h1 (x : Position) : (fderiv ℝ ψ x) v • u (L⁻¹ • x) =
      L⁻¹ • ((fderiv ℝ χ (L⁻¹ • x)) v • u (L⁻¹ • x)) := by
    rw [hdχ, smul_inv_smul₀ hL.ne', smul_smul, inv_mul_cancel_left₀ hL.ne']
  have h2 (x : Position) : ψ x • L⁻¹ • du (L⁻¹ • x) =
      L⁻¹ • (χ (L⁻¹ • x) • du (L⁻¹ • x)) := by
    change _ = L⁻¹ • (ψ (L • L⁻¹ • x) • _)
    rw [smul_inv_smul₀ hL.ne', smul_comm]
  change (∫ x, (fderiv ℝ ψ x) v • u (L⁻¹ • x)) = _
  simp only [h1, h2, integral_smul]
  rw [dilation_integral (fun y => (fderiv ℝ χ y) v • u y) hL,
    dilation_integral (fun y => χ y • du y) hL, hw, smul_neg, smul_neg]

private theorem dilation_memLp {f : Position → ℝ} {p : ℝ≥0∞} (hf : MemLp f p)
    {L : ℝ} (hL : 0 < L) : MemLp (fun x => f (L⁻¹ • x)) p := by
  let e := (Homeomorph.smul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hL.ne')).unit : ℝˣ) :
    Position ≃ₜ Position).toMeasurableEquiv
  apply e.memLp_map_measure_iff.mp
  change MemLp f p (Measure.map (fun x : Position => L⁻¹ • x) volume)
  rw [map_addHaar_smul _ (inv_ne_zero hL.ne')]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem DensityRegular.dilate {D : Density} {p θ : ℝ} {S T : MatrixGradient}
    (h : DensityRegular D p θ S T) {L : ℝ} (hL : 0 < L) :
    DensityRegular (D.dilate L) p θ (dilatedGradient S L) (dilatedGradient T L) where
  charge_L1 := h.charge_L1.comp_smul (inv_ne_zero hL.ne')
  charge_L2 := dilation_memLp h.charge_L2 hL
  sqrt_gradient i j k := (h.sqrt_gradient i j k).dilate hL
  sqrt_L2 := by
    simp only [funext (matrixGradNorm_dilate S hL)]
    exact (dilation_memLp h.sqrt_L2 hL).const_mul _
  theta_gradient i j k := (h.theta_gradient i j k).dilate hL
  theta_Lp := by
    simp only [funext (matrixGradNorm_dilate T hL)]
    exact (dilation_memLp h.theta_Lp hL).const_mul _

theorem MinorityBound.dilate {ν : ℝ} {D : Density} (h : MinorityBound ν D)
    {L : ℝ} (hL : 0 < L) : MinorityBound ν (D.dilate L) := by
  let e := (Homeomorph.smul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hL.ne')).unit : ℝˣ) :
    Position ≃ₜ Position).toMeasurableEquiv
  have hmap : Measure.map e volume ≪ volume := by
    change Measure.map (fun x : Position => L⁻¹ • x) volume ≪ volume
    rw [map_addHaar_smul _ (inv_ne_zero hL.ne')]
    exact Measure.smul_absolutelyContinuous
  exact (MeasureTheory.QuasiMeasurePreserving.mk e.measurable.aemeasurable hmap).tendsto_ae h

theorem integral_dilatedGradient (G : MatrixGradient) (r : ℝ) {L : ℝ} (hL : 0 < L) :
    (∫ x, matrixGradNorm (dilatedGradient G L) x ^ r) =
      L ^ (3 - r) * ∫ x, matrixGradNorm G x ^ r := by
  have hadd (x : Position) : (L⁻¹ * matrixGradNorm G (L⁻¹ • x)) ^ r =
      L⁻¹ ^ r * matrixGradNorm G (L⁻¹ • x) ^ r :=
    Real.mul_rpow (inv_nonneg.mpr hL.le) (show 0 ≤ matrixGradNorm G (L⁻¹ • x) from Real.sqrt_nonneg _)
  simp only [matrixGradNorm_dilate _ hL, hadd, integral_const_mul,
    dilation_integral (fun x => matrixGradNorm G x ^ r) hL, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_natCast L 3, ← Real.rpow_add hL]
  congr 2
  norm_num
  ring

def Density.particleScale (D : Density) (N : ℝ) : Density := D.dilate (N ^ (1 / 3 : ℝ))

private theorem volume_particleScale {N : ℝ} (hN : 0 < N) : (N ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  norm_num

theorem integral_particleScale {N : ℝ} (hN : 0 < N) (f : Position → ℝ) :
    (∫ x : Position, f ((N ^ (1 / 3 : ℝ))⁻¹ • x)) = N * ∫ x, f x := by
  rw [dilation_integral f (Real.rpow_pos_of_pos hN _), volume_particleScale hN, smul_eq_mul]

/-- A unit-mass profile has particle number `N` after the dilation. -/
theorem Density.charge_particleScale {N : ℝ} (hN : 0 < N) (D : Density) (hm : (∫ x, D.charge x) = 1) :
    (∫ x, (D.particleScale N).charge x) = N := by
  rw [Density.particleScale, show (∫ x, (D.dilate (N ^ (1 / 3 : ℝ))).charge x) = _
    from integral_particleScale hN D.charge, hm, mul_one]

/-- Optimized particle-number powers, stated with the two density integrals
grouped in the term of order `N^(1 − p/(3(b+1)))`. -/
def RescaledLSDAEstimate (F : GasEnergies) (classOf : Density → Prop) (p θ b C : ℝ) : Prop :=
  ∀ (D : Density) (S T : MatrixGradient), classOf D → DensityRegular D p θ S T → ∀ N : ℝ, 1 ≤ N →
    |F.energy (D.particleScale N).matrix - N * ∫ x, F.ueg (D.matrix x)| ≤
      (2 * C) * N ^ (1 / 3 + scalingExponent p b) * (∫ x, matrixGradNorm S x ^ 2) +
      N ^ (1 - scalingExponent p b) * ((∫ x, D.charge x + D.charge x ^ 2) +
        C * (∫ x, matrixGradNorm T x ^ p))

theorem LSDAEstimate.rescale {F : GasEnergies} {classOf : Density → Prop} {p θ b C : ℝ}
    (h : LSDAEstimate F classOf p θ b C) (hp : 0 < p) (hb : 0 < b + 1) (hC : 0 ≤ C)
    (hclass : ∀ (D : Density) (L : ℝ), 0 < L → classOf D → classOf (D.dilate L)) :
    RescaledLSDAEstimate F classOf p θ b C := by
  intro D S T hc hD N hN
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let L := N ^ (1 / 3 : ℝ)
  let s := scalingExponent p b
  let ε := N ^ (-s)
  have hL : 0 < L := Real.rpow_pos_of_pos hN₀ _
  have hε : 0 < ε := Real.rpow_pos_of_pos hN₀ _
  have hs : 0 ≤ s := (div_pos hp (mul_pos (by norm_num) hb)).le
  have hε' : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)
  have hc' := hclass D L hL hc
  have hx := (h (D.dilate L) (dilatedGradient S L) (dilatedGradient T L) hc' (hD.dilate hL) ε hε).2
  have hj (r : ℝ) : L ^ (3 - r) = N ^ (1 - r / 3) := by
    rw [show L = N ^ (1 / 3 : ℝ) from rfl, ← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hmass : ε * N = N ^ (1 - s) := by
    change N ^ (-s) * N = _
    rw [← Real.rpow_add_one hN₀.ne']
    congr 1
    ring
  have hbulk : C / ε ^ b * N ^ (1 - p / 3) = C * N ^ (1 - s) := by
    change C / (N ^ (-s)) ^ b * _ = _
    rw [← Real.rpow_mul hN₀.le, div_eq_mul_inv, ← Real.rpow_neg hN₀.le, mul_assoc, ← Real.rpow_add hN₀]
    congr 2
    dsimp only [s]
    linarith [scaling_balance (p := p) hb.ne']
  have hkin : C * (1 + ε) / ε * N ^ (1 - (2:ℝ) / 3) ≤ 2 * C * N ^ (1 / 3 + s) := by
    have he : ε⁻¹ = N ^ s := by simp [ε, Real.rpow_neg hN₀.le]
    rw [div_eq_mul_inv, he, mul_assoc, Real.rpow_add hN₀, show 1 - (2:ℝ)/3 = 1/3 by norm_num]
    have ht : C * (1 + ε) ≤ 2 * C := by nlinarith [mul_nonneg hC (sub_nonneg.mpr hε')]
    calc
      _ ≤ (2 * C) * (N ^ s * N ^ (1/3 : ℝ)) := mul_le_mul_of_nonneg_right ht (by positivity)
      _ = _ := by ring
  have href : (∫ x, F.ueg ((D.dilate L).matrix x)) = N * ∫ x, F.ueg (D.matrix x) :=
    integral_particleScale hN₀ (fun x => F.ueg (D.matrix x))
  have hm : (∫ x, (D.dilate L).charge x + (D.dilate L).charge x ^ 2) =
      N * ∫ x, D.charge x + D.charge x ^ 2 := integral_particleScale hN₀ (fun x => D.charge x + D.charge x ^ 2)
  have h2 : (∫ x, matrixGradNorm (dilatedGradient S L) x ^ 2) =
      N ^ (1 - (2 : ℝ) / 3) * ∫ x, matrixGradNorm S x ^ 2 := by
    simpa only [hj, Real.rpow_two] using integral_dilatedGradient S 2 hL
  rw [href, lsdaError, hm, h2, integral_dilatedGradient _ p hL, hj] at hx
  have hkin' := mul_le_mul_of_nonneg_right hkin (integral_nonneg (μ := volume)
    (fun x => sq_nonneg (matrixGradNorm S x)))
  change |F.energy (D.dilate L).matrix - N * ∫ x, F.ueg (D.matrix x)| ≤ _
  apply hx.trans
  rw [← mul_assoc ε, hmass, ← mul_assoc (C / ε ^ b), hbulk]
  dsimp only [s] at *
  linarith only [hkin']

/-- Particle-number scaling for arbitrary polarization and for a uniform minority
fraction. Both constants are independent of the density and particle number. -/
theorem rescaledLSDA_of_mainTSGA {F : GasEnergies} (H : MainTSGAEstimate F)
    {p θ : ℝ} (hp : 3 < p) (hθ : 2 / p ≤ θ) (hθ' : θ < 1) :
    (∃ C > 0, RescaledLSDAEstimate F (fun _ => True) p θ (bulkExponent p θ) C) ∧
    (∀ ν : ℝ, 0 < ν → ν ≤ 1 / 2 → ∃ C > 0,
      RescaledLSDAEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C) := by
  obtain ⟨hg, hm⟩ := mainLSDA_of_mainTSGA H hp hθ hθ'
  have hp₀ : 0 < p := by linarith
  have hb (z : ℝ) : 0 < max (2 * p) z - 1 + 1 := by linarith [le_max_left (2 * p) z]
  constructor
  · obtain ⟨C, hC, he⟩ := hg
    exact ⟨C, hC, he.rescale hp₀ (hb _) hC.le (fun _ _ _ _ => trivial)⟩
  · intro ν hν hν'
    obtain ⟨C, hC, he⟩ := hm ν hν hν'
    exact ⟨C, hC, he.rescale hp₀ (hb _) hC.le (fun _ _ hL hminor => hminor.dilate hL)⟩

/-- The optimized `ε` exponent in the minority regime, including the
transition to the two sharp powers. -/
theorem scalingExponent_polarized (p θ : ℝ) (hp : 0 < p) :
    scalingExponent p (polarizedBulkExponent p θ) =
      if θ * p ≤ 1 + p / 3 then 1 / 6 else p / (3 * ((1 + 3 * θ) * p - 3)) := by
  split_ifs with h
  · rw [(polarizedBulkExponent_eq_two_mul_sub_one_iff p θ).mpr h, scalingExponent_of_sharp_bulk hp]
  · have hgt : 2 * p ≤ (1 + 3 * θ) * p - 3 := by linarith
    simp only [scalingExponent, polarizedBulkExponent, max_eq_right hgt, sub_add_cancel]

/-- In the sharp-exponent regime the kinetic term is of order `N^(1/2)`
and the full error is bounded by a fixed profile constant times `N^(5/6)`. -/
theorem RescaledLSDAEstimate.sharp_rate {F : GasEnergies} {classOf : Density → Prop} {p θ C : ℝ}
    (h : RescaledLSDAEstimate F classOf p θ (2 * p - 1) C) (hp : 0 < p) (hC : 0 ≤ C)
    (D : Density) (S T : MatrixGradient) (hc : classOf D) (hD : DensityRegular D p θ S T)
    {N : ℝ} (hN : 1 ≤ N) :
    |F.energy (D.particleScale N).matrix - N * ∫ x, F.ueg (D.matrix x)| ≤
      N ^ (5 / 6 : ℝ) * ((2 * C) * (∫ x, matrixGradNorm S x ^ 2) +
        (∫ x, D.charge x + D.charge x ^ 2) + C * (∫ x, matrixGradNorm T x ^ p)) := by
  have he := h D S T hc hD N hN
  rw [scalingExponent_of_sharp_bulk hp,
    show (1/3 + 1/6 : ℝ) = 1/2 by norm_num, show (1 - 1/6 : ℝ) = 5/6 by norm_num] at he
  have hn := Real.rpow_le_rpow_of_exponent_le hN (show (1/2 : ℝ) ≤ 5/6 by norm_num)
  have hn' := mul_le_mul_of_nonneg_right hn (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC)
    (integral_nonneg (μ := volume) fun x => sq_nonneg (matrixGradNorm S x)))
  nlinarith only [he, hn']

open Asymptotics Filter in
theorem RescaledLSDAEstimate.sharp_isBigO {F : GasEnergies} {classOf : Density → Prop} {p θ C : ℝ}
    (h : RescaledLSDAEstimate F classOf p θ (2 * p - 1) C) (hp : 0 < p) (hC : 0 ≤ C)
    (D : Density) (S T : MatrixGradient) (hc : classOf D) (hD : DensityRegular D p θ S T) :
    (fun N : ℝ => F.energy (D.particleScale N).matrix - N * ∫ x, F.ueg (D.matrix x))
      =O[atTop] (fun N : ℝ => N ^ (5 / 6 : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨2 * C * (∫ x, matrixGradNorm S x ^ 2) + (∫ x, D.charge x + D.charge x ^ 2) +
    C * (∫ x, matrixGradNorm T x ^ p), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ N) _)]
  exact (h.sharp_rate hp hC D S T hc hD hN).trans_eq (mul_comm _ _)

open Asymptotics Filter in
/-- The `N^(5/6)` rate under each of the two sharp-exponent conditions on the bulk exponent. The implicit constant may depend on the fixed profile. -/
theorem sharp_rescaledLSDA_of_mainTSGA {F : GasEnergies} (H : MainTSGAEstimate F)
    {p θ : ℝ} (hp : 3 < p) (hθ : 2 / p ≤ θ) (hθ' : θ < 1) (D : Density)
    (S T : MatrixGradient) (hD : DensityRegular D p θ S T)
    (hsharp : θ ≤ 1 / 3 ∨ ∃ ν : ℝ, 0 < ν ∧ ν ≤ 1 / 2 ∧ MinorityBound ν D ∧ θ * p ≤ 1 + p / 3) :
    (fun N : ℝ => F.energy (D.particleScale N).matrix - N * ∫ x, F.ueg (D.matrix x))
      =O[atTop] (fun N : ℝ => N ^ (5 / 6 : ℝ)) := by
  obtain ⟨hg, hm⟩ := rescaledLSDA_of_mainTSGA H hp hθ hθ'
  have hp₀ : 0 < p := by linarith
  rcases hsharp with hsmall | ⟨ν, hν, hν', hminor, hsmall⟩
  · obtain ⟨C, hC, he⟩ := hg
    rw [(bulkExponent_eq_two_mul_sub_one_iff hp₀).2 hsmall] at he
    exact he.sharp_isBigO hp₀ hC.le D S T trivial hD
  · obtain ⟨C, hC, he⟩ := hm ν hν hν'
    rw [(polarizedBulkExponent_eq_two_mul_sub_one_iff p θ).2 hsmall] at he
    exact he.sharp_isBigO hp₀ hC.le D S T hminor hD

end TSGA
