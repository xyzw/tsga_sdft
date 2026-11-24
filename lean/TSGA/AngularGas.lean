import TSGA.OrderedGas
import TSGA.RayRegularity

/-! # Angular regularity of the Coulomb spin-spiral gas -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory Filter SSW TSGA.Localization
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

private theorem conjugate_trace {U : SpinMatrix} (hU : U ∈ unitary SpinMatrix) (B : SpinMatrix) :
    (U*B*star U).trace.re = B.trace.re := by
  rw [Matrix.trace_mul_cycle, (Unitary.mem_iff.mp hU).1, one_mul]

private theorem sqrt_hs_sq {B : SpinMatrix} (hB : B.PosSemidef) :
    hilbertSchmidt (CFC.sqrt B)^2 = B.trace.re := by
  rw [hilbertSchmidt, Real.sq_sqrt (by positivity), hs_trace, (CFC.sqrt_nonneg B).star_eq,
    CFC.sqrt_mul_sqrt_self B hB.nonneg]

private theorem norm_loss (D : SpinMatrix) {B : SpinMatrix} (hB : B.PosSemidef) :
    hilbertSchmidt (D*CFC.sqrt B)^2 ≤ B.trace.re*‖D‖^2 := by
  let R := CFC.sqrt B
  have h := trace_product_nonneg (Matrix.le_iff.mp (CStarAlgebra.star_mul_le_algebraMap_norm_sq D)) hB
  have halg : algebraMap ℝ SpinMatrix (‖D‖^2) = (‖D‖^2) • (1 : SpinMatrix) :=
    Algebra.algebraMap_eq_smul_one _
  rw [halg, sub_mul, Matrix.trace_sub, Algebra.smul_mul_assoc, one_mul, Matrix.trace_smul,
    Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul] at h
  have ht : (D*R*star (D*R)).trace = ((star D*D)*B).trace := by
    rw [star_mul, show star R = R from (CFC.sqrt_nonneg B).star_eq]
    calc
      _ = (D*(R*R)*star D).trace := by congr 1; noncomm_ring
      _ = _ := by rw [show R*R = B from CFC.sqrt_mul_sqrt_self B hB.nonneg, Matrix.trace_mul_cycle]
  rw [hilbertSchmidt, Real.sq_sqrt (by positivity), hs_trace, ht]
  linarith

open scoped Matrix.Norms.Frobenius in
private theorem hs_loss (D : SpinMatrix) {B : SpinMatrix} (hB : B.PosSemidef) :
    hilbertSchmidt (D*CFC.sqrt B)^2 ≤ B.trace.re*hilbertSchmidt D^2 := by
  have h : hilbertSchmidt (D*CFC.sqrt B) ≤ hilbertSchmidt D*hilbertSchmidt (CFC.sqrt B) := by
    simpa only [hs_eq_norm] using Matrix.frobenius_norm_mul D (CFC.sqrt B)
  have hh : hilbertSchmidt (D*CFC.sqrt B)^2 ≤ (hilbertSchmidt D * hilbertSchmidt (CFC.sqrt B))^2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr h
  rwa [mul_pow, sqrt_hs_sq hB, mul_comm] at hh

/-- A spin unitary preserves the trace, so the direct cost in the general
contraction comparison vanishes at every finite volume. -/
private theorem spin_rotation_le {η : Mollifier} {J K : ℝ}
    (loc : ∀ B : SpinMatrix, B.PosSemidef → 0 < B.trace.re → ∀ q : Position, FiniteLocalization energy η B q)
    (rate : FiniteRateTiling energy η K) (H : SpiralRemovalInputs η J)
    {B U : SpinMatrix} (hB : B.PosSemidef) (hr : 0 < B.trace.re) (hU : U ∈ unitary SpinMatrix)
    {d : ℝ} (hd : 0 ≤ d) (hloss : hilbertSchmidt ((1-U)*CFC.sqrt B)^2 ≤ B.trace.re*d^2) (q : Position) :
    sswEnergy energy η (U*B*star U) q ≤ sswEnergy energy η B q +
      8*(4*(K+J+1))*holderGrowth B.trace.re q*d := by
  let L := 4*(K+J+1)
  have hJL : J ≤ L := by dsimp only [L]; linarith [H.one_le,rate.one_le]
  let A := U*B*star U
  have ht : A.trace.re = B.trace.re := conjugate_trace hU B
  have hA : A.PosSemidef := hB.mul_mul_conjTranspose_same U
  let r := B.trace.re
  let G := holderGrowth r q
  have hG : 0 < G := by dsimp [G,holderGrowth,r]; positivity
  have hAlim := (loc A hA (ht.symm ▸ hr) q).tile_tendsto zero_lt_one
  have hBlim := (loc B hB hr q).tile_tendsto zero_lt_one
  apply le_of_tendsto_of_tendsto hAlim (hBlim.add_const (8*L*G*d))
  filter_upwards [eventually_ge_atTop (max 1 (r/G)), eventually_ge_atTop K] with ℓ hℓ hscale
  have h1 : 1 ≤ ℓ := (le_max_left ..).trans hℓ
  have he : 0 < ℓ := zero_lt_one.trans_le h1
  have hc : r/(ℓ*1) ≤ 4*G := by
    rw [mul_one,div_le_iff₀ he]
    have hw := (div_le_iff₀ hG).mp ((le_max_right ..).trans hℓ)
    nlinarith only [hw,mul_nonneg he.le hG.le]
  apply direction_mono_add (tile_directions_integrable rate hA q he zero_lt_one (by simpa using hscale))
    (tile_directions_integrable rate hB q he zero_lt_one (by simpa using hscale))
  intro ω
  let k := ‖q‖ • (ω : Position)
  have hk : holderGrowth r k = G := by simp [k,G,holderGrowth,norm_smul]
  have hc' : r/(ℓ*1) ≤ 4*holderGrowth r k := hk.symm ▸ hc
  have hw := contraction_tile_comparison (H.enlarge hJL) hB hr U (Unitary.mem_iff.mp hU).1.le
    (A := A) rfl ht.le hd hloss k he zero_lt_one h1 hc' (tile_upper_from_zero rate H B hB hr _ he _ zero_lt_one h1 k)
  change _ ≤ _ + 8*L*holderGrowth r k*d + (B.trace.re^2-A.trace.re^2)*_ at hw
  simpa only [ht,sub_self,zero_mul,add_zero,hk] using hw

private theorem spin_rotation_abs {η : Mollifier} {J K : ℝ}
    (loc : ∀ B : SpinMatrix, B.PosSemidef → 0 < B.trace.re → ∀ q : Position, FiniteLocalization energy η B q)
    (rate : FiniteRateTiling energy η K) (H : SpiralRemovalInputs η J)
    {A U : SpinMatrix} (hA : A.PosSemidef) (hr : 0 < A.trace.re) (hU : U ∈ unitary SpinMatrix)
    {d : ℝ} (hd : 0 ≤ d) (hf : hilbertSchmidt ((1-U)*CFC.sqrt A)^2 ≤ A.trace.re*d^2)
    (hb : hilbertSchmidt ((1-star U)*CFC.sqrt (U*A*star U))^2 ≤ (U*A*star U).trace.re*d^2) (q : Position) :
    |sswEnergy energy η (U*A*star U) q-sswEnergy energy η A q| ≤
      8*(4*(K+J+1))*holderGrowth A.trace.re q*d := by
  have ht := conjugate_trace hU A
  have ht' : star U*(U*A*star U)*star (star U) = A := by
    calc
      _ = (star U*U)*A*(star U*U) := by rw [star_star]; noncomm_ring
      _ = A := by rw [(Unitary.mem_iff.mp hU).1,one_mul,mul_one]
  have h₁ := spin_rotation_le loc rate H hA hr hU hd hf q
  have h₂ := spin_rotation_le loc rate H (B := U*A*star U) (hA.mul_mul_conjTranspose_same U) (ht.symm ▸ hr)
    (Unitary.star_mem hU) hd hb q
  rw [ht',ht] at h₂
  exact abs_le.mpr ⟨by linarith only [h₂], by linarith only [h₁]⟩

/-- The operator-norm angular estimate of Proposition E.2(vi), including fully
polarized matrices and arbitrary unitaries in U(2). -/
theorem coulomb_ssw_spin_rotation {η : Mollifier} {J K : ℝ}
    (loc : ∀ A : SpinMatrix, A.PosSemidef → 0 < A.trace.re → ∀ q : Position, FiniteLocalization energy η A q)
    (rate : FiniteRateTiling energy η K) (H : SpiralRemovalInputs η J) :
    ∃ C > 0, ∀ A : SpinMatrix, A.PosSemidef → 0 < A.trace.re → ∀ U ∈ unitary SpinMatrix, ∀ q : Position,
      |sswEnergy energy η (U*A*star U) q - sswEnergy energy η A q| ≤ C*holderGrowth A.trace.re q*‖U-1‖ := by
  refine ⟨8*(4*(K+J+1)),by linarith [H.one_le,rate.one_le],?_⟩
  intro A hA hr U hU q
  apply spin_rotation_abs loc rate H hA hr hU (norm_nonneg _) _ _ q
  · simpa only [norm_sub_rev (1:SpinMatrix) U] using norm_loss (1-U) hA
  · have hh : ‖1-star U‖ = ‖U-1‖ := by
      rw [show 1-star U = star (1-U) by rw [star_sub,star_one], norm_star, norm_sub_rev]
    simpa only [hh] using norm_loss (1-star U) (B := U*A*star U) (hA.mul_mul_conjTranspose_same U)

/-- Hilbert–Schmidt version, in the norm used for spin alignment. -/
theorem coulomb_ssw_spin_rotation_hs {η : Mollifier} {J K : ℝ}
    (loc : ∀ A : SpinMatrix, A.PosSemidef → 0 < A.trace.re → ∀ q : Position, FiniteLocalization energy η A q)
    (rate : FiniteRateTiling energy η K) (H : SpiralRemovalInputs η J) :
    ∃ C > 0, ∀ A : SpinMatrix, A.PosSemidef → 0 < A.trace.re → ∀ U ∈ unitary SpinMatrix, ∀ q : Position,
      |sswEnergy energy η (U*A*star U) q - sswEnergy energy η A q| ≤ C*holderGrowth A.trace.re q*hilbertSchmidt (U-1) := by
  refine ⟨8*(4*(K+J+1)),by linarith [H.one_le,rate.one_le],?_⟩
  intro A hA hr U hU q
  apply spin_rotation_abs loc rate H hA hr hU (d := hilbertSchmidt (U-1)) (Real.sqrt_nonneg _) _ _ q
  · simpa only [hs_sub_comm (1:SpinMatrix) U] using hs_loss (1-U) hA
  · have hh : hilbertSchmidt (1-star U) = hilbertSchmidt (U-1) := by
      have hstar (X : SpinMatrix) : hilbertSchmidt (star X) = hilbertSchmidt X := by
        rw [hs_eq_norm,hs_eq_norm]
        exact Matrix.frobenius_norm_conjTranspose X
      rw [show 1-star U = star (1-U) by rw [star_sub,star_one],hstar,hs_sub_comm]
    simpa only [hh] using hs_loss (1-star U) (B := U*A*star U) (hA.mul_mul_conjTranspose_same U)

end TSGA.ManyBody
