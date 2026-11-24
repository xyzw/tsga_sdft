import TSGA.KineticEnergy
import TSGA.AxialKinetic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # The spin-matrix Hoffmann–Ostenhof inequality

Writing a nonzero spinor as `r z` with `|z| = 1`, the positive square root
of its density is `r z z*`. The differential below results from the ordinary
product and norm rules. Its squared Hilbert–Schmidt norm gives the factor two.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory Matrix TSGA.Localization
open scoped ComplexConjugate ComplexOrder

abbrev OrbitalValue := Fin 2 → ℂ

def spinSq (v : OrbitalValue) : ℝ := ∑ j, ‖v j‖ ^ 2
def spinOverlap (v w : OrbitalValue) : ℂ := ∑ j, conj (v j) * w j
def entrySq (M : SpinMatrix) : ℝ := ∑ j, ∑ k, ‖M j k‖ ^ 2

def orbitalDensity (f : Position → OrbitalValue) : Density :=
  ⟨fun x => vecMulVec (f x) (star (f x)), fun x => posSemidef_vecMulVec_self_star (f x)⟩

def rootVariation (z w : OrbitalValue) : SpinMatrix := fun j k =>
  w j * conj (z k) + z j * conj (w k) - ((spinOverlap z w).re : ℂ) * z j * conj (z k)

set_option maxHeartbeats 2000000 in
private theorem variation_polynomial (z w : OrbitalValue) :
    entrySq (rootVariation z w) =
      2 * spinSq z * spinSq w + 2 * (spinOverlap z w).re^2 - 2 * (spinOverlap z w).im^2 -
      4 * spinSq z * (spinOverlap z w).re^2 + (spinSq z)^2 * (spinOverlap z w).re^2 := by
  simp only [entrySq, rootVariation, spinOverlap, spinSq, Fin.sum_univ_two, Complex.sq_norm,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Exact square-root energy for a single spinor derivative, including the
radial and phase components that are absent from the optimal factor. -/
theorem rankOne_variation_energy {z : OrbitalValue} (hz : spinSq z = 1) (w : OrbitalValue) :
    entrySq (rootVariation z w) =
      2 * spinSq w - (spinOverlap z w).re ^ 2 - 2 * (spinOverlap z w).im ^ 2 := by
  rw [variation_polynomial, hz]
  ring

theorem rankOne_variation_le {z : OrbitalValue} (hz : spinSq z = 1) (w : OrbitalValue) :
    entrySq (rootVariation z w) ≤ 2 * spinSq w := by
  rw [rankOne_variation_energy hz]
  linarith [sq_nonneg (spinOverlap z w).re, sq_nonneg (spinOverlap z w).im]

/-- Local weak calculus for a spinor. Away from zero this is the product rule
for the rank-one square root `v v* / |v|`. A Sobolev field has zero derivative
almost everywhere on its zero set. No kinetic comparison is part of this input. -/
def RankOneRootChain : Prop :=
  ∀ (f : Position → OrbitalValue) (w : Position → Fin 3 → OrbitalValue),
    (∀ i j, WeakPartialOn Set.univ i (fun x => f x j) (fun x => w x i j)) →
    ∃ Z : MatrixGradient, IsMatrixGradientOn Set.univ ((orbitalDensity f).power (1/2)) Z ∧
      ∀ᵐ x, (f x = 0 ∧ ∀ i, Z x i = 0) ∨
        ∃ z : OrbitalValue, spinSq z = 1 ∧ f x = (√(spinSq (f x))) • z ∧
          ∀ i, Z x i = rootVariation z (w x i)

/-- Countable convexity and positive homogeneity of the matrix Fisher
integral, with lower semicontinuity at an infinite sum. -/
def CountableFisherConvexity : Prop :=
  ∀ (D : Density) (S : MatrixGradient), SqrtRegular D S →
    ∀ (A : ℕ → Density) (V : ℕ → MatrixGradient) (n : ℕ → ℝ), (∀ k, 0 ≤ n k) →
      (∀ k, IsMatrixGradientOn Set.univ ((A k).power (1/2)) (V k)) →
      (∀ k, Integrable (kineticDensity (V k))) →
      (∀ᵐ x, ∀ i j, HasSum (fun k => (n k : ℂ) * (A k).matrix x i j) (D.matrix x i j)) →
      Summable (fun k => n k * sqrtKinetic (V k)) →
      sqrtKinetic S ≤ ∑' k, n k * sqrtKinetic (V k)

/-- The diagonal kernel series converges almost everywhere and the one-body
marginal of a mixed state preserves its spin density and kinetic trace. -/
structure OneBodyMarginals : Prop where
  diagonal : ∀ γ : OneBody, ∀ᵐ x, ∀ i j, Summable (fun k => (γ.occupation k : ℂ) *
    γ.orbital k i x * conj (γ.orbital k j x))
  marginal : ∀ Γ : MixedState, ∃ γ : OneBody,
    γ.matrixDensity =ᵐ[volume] Γ.matrixDensity ∧ γ.kinetic = Γ.kinetic

private theorem singleOrbital_bound (chain : RankOneRootChain) (f : Position → OrbitalValue)
    (w : Position → Fin 3 → OrbitalValue)
    (hweak : ∀ i j, WeakPartialOn Set.univ i (fun x => f x j) (fun x => w x i j))
    (hLp : ∀ i j, MemLp (fun x => w x i j) 2 volume) :
    ∃ Z : MatrixGradient,
      IsMatrixGradientOn Set.univ ((orbitalDensity f).power (1/2)) Z ∧
      Integrable (kineticDensity Z) ∧
      sqrtKinetic Z ≤ 2 * ∑ j, ∑ i, ∫ x, ‖w x i j‖ ^ 2 := by
  obtain ⟨Z, hZ, hpolar⟩ := chain f w hweak
  refine ⟨Z, hZ, ?_⟩
  have hpoint : ∀ᵐ x, kineticDensity Z x ≤ 2 * ∑ i, spinSq (w x i) := by
    filter_upwards [hpolar] with x hx
    have hs : kineticDensity Z x = ∑ i, entrySq (Z x i) := Real.sq_sqrt (by positivity)
    rw [hs, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases hx with ⟨_, hzero⟩ | ⟨z, hz, _, he⟩
    · have h0 : entrySq (Z x i) = 0 := by rw [hzero i]; simp [entrySq]
      rw [h0]
      unfold spinSq
      positivity
    · rw [he]
      exact rankOne_variation_le hz _
  have hnorm (i j) : Integrable (fun x => ‖w x i j‖ ^ 2) volume :=
    (hLp i j).integrable_norm_pow (p := 2) (by decide)
  have hder (i) : Integrable (fun x => spinSq (w x i)) volume :=
    integrable_finsetSum _ (fun j _ => hnorm i j)
  have hi := (integrable_finsetSum Finset.univ (fun i _ => hder i)).const_mul 2
  have hm (i j k) : AEMeasurable (fun x => Z x i j k) volume :=
    (locallyIntegrableOn_univ.mp (hZ i j k).2.1).aestronglyMeasurable.aemeasurable
  have he : AEMeasurable (kineticDensity Z) volume := by
    have heq : kineticDensity Z = fun x => ∑ i, ∑ j, ∑ k, ‖Z x i j k‖^2 :=
      funext fun x => Real.sq_sqrt (by positivity)
    rw [heq]
    exact Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      Finset.aemeasurable_fun_sum _ fun k _ => (hm i j k).norm.pow_const 2
  have hZi : Integrable (kineticDensity Z) := hi.mono' he.aestronglyMeasurable
    (hpoint.mono fun x hx => by simpa only [Real.norm_of_nonneg (show 0 ≤ kineticDensity Z x from sq_nonneg _)] using hx)
  refine ⟨hZi, ?_⟩
  have hint := integral_mono_ae hZi hi hpoint
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hder i)] at hint
  simp only [spinSq, integral_finsetSum _ (fun j _ => hnorm _ j)] at hint
  rw [Finset.sum_comm]
  exact hint

/-- Arbitrary nonnegative occupation numbers in the spectral decomposition.
The Hoffmann–Ostenhof inequality uses no upper bound on occupations. -/
theorem hoffmann_ostenhof_occupied (chain : RankOneRootChain) (convex : CountableFisherConvexity)
    (D : Density) (S : MatrixGradient) (hD : SqrtRegular D S)
    (f : ℕ → Position → OrbitalValue) (w : ℕ → Position → Fin 3 → OrbitalValue) (n : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ n k)
    (weak : ∀ k i j, WeakPartialOn Set.univ i (fun x => f k x j) (fun x => w k x i j))
    (hLp : ∀ k i j, MemLp (fun x => w k x i j) 2 volume)
    (hd : ∀ᵐ x, ∀ i j, HasSum (fun k => (n k : ℂ) * (orbitalDensity (f k)).matrix x i j) (D.matrix x i j))
    (hK : Summable fun k => n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2) :
    sqrtKinetic S / 2 ≤ ∑' k, n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2 := by
  classical
  choose V hV hVi hcost using fun k => singleOrbital_bound chain (f k) (w k) (weak k) (hLp k)
  have hb (k) : n k * sqrtKinetic (V k) ≤ 2 * (n k * ∑ j, ∑ i, ∫ x, ‖w k x i j‖^2) :=
    (mul_le_mul_of_nonneg_left (hcost k) (hn k)).trans_eq (by ring)
  have hmajor := hK.mul_left 2
  have hs := Summable.of_nonneg_of_le (fun k => mul_nonneg (hn k)
    (integral_nonneg fun x => sq_nonneg (matrixGradNorm (V k) x))) hb hmajor
  have hf := convex D S hD (fun k => orbitalDensity (f k)) V n hn hV hVi hd hs
  have hb' := hs.tsum_le_tsum hb hmajor
  rw [tsum_mul_left] at hb'
  linarith

/-- Specialization to the natural orbitals of a one-body contraction. -/
theorem hoffmann_ostenhof_oneBody (chain : RankOneRootChain) (convex : CountableFisherConvexity)
    (marg : OneBodyMarginals) (γ : OneBody) (D : Density) (S : MatrixGradient)
    (hD : SqrtRegular D S) (hd : γ.matrixDensity =ᵐ[volume] D.matrix) :
    sqrtKinetic S / 2 ≤ γ.kinetic := by
  apply hoffmann_ostenhof_occupied chain convex D S hD (fun k x j => γ.orbital k j x)
    (fun k x i j => γ.gradient k j i x) γ.occupation (fun k => (γ.occupation_mem k).1)
    (fun k i j => γ.weak k j i) (fun k i j => γ.gradient_L2 k j i) _ γ.finite_kinetic
  filter_upwards [marg.diagonal γ, hd] with x hx hx'
  intro i j
  rw [← hx']
  simpa only [orbitalDensity, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, mul_assoc,
    OneBody.matrixDensity, OneBody.kernel] using (hx i j).hasSum

theorem hoffmann_ostenhof_state (chain : RankOneRootChain) (convex : CountableFisherConvexity)
    (marg : OneBodyMarginals) (D : Density) (S : MatrixGradient) (hD : SqrtRegular D S)
    (Γ : MixedState) (hf : feasible D.matrix Γ) : sqrtKinetic S / 2 ≤ Γ.kinetic := by
  obtain ⟨γ, hd, ht⟩ := marg.marginal Γ
  rw [← ht]
  exact hoffmann_ostenhof_oneBody chain convex marg γ D S hD (hd.trans hf)

/-- Unit spinor in the real plane and its derivative with radial speed `a`
and tangential speed `b`. -/
def planarSpin (t : ℝ) : OrbitalValue := ![(Real.cos t : ℂ), (Real.sin t : ℂ)]

def planarVelocity (t a b : ℝ) : OrbitalValue :=
  ![((a * Real.cos t - b * Real.sin t : ℝ) : ℂ), ((a * Real.sin t + b * Real.cos t : ℝ) : ℂ)]

theorem planar_unit (t : ℝ) : spinSq (planarSpin t) = 1 := by
  rw [spinSq, Fin.sum_univ_two]
  change ‖(Real.cos t : ℂ)‖^2 + ‖(Real.sin t : ℂ)‖^2 = 1
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, add_comm] using
    (Real.sin_sq_add_cos_sq t)

theorem planar_energies (t a b : ℝ) :
    spinSq (planarVelocity t a b) = a^2+b^2 ∧
    entrySq (rootVariation (planarSpin t) (planarVelocity t a b)) = a^2+2*b^2 := by
  have hv : spinSq (planarVelocity t a b) = a^2+b^2 := by
    rw [spinSq, Fin.sum_univ_two]
    change ‖((a*Real.cos t-b*Real.sin t : ℝ):ℂ)‖^2 + ‖((a*Real.sin t+b*Real.cos t : ℝ):ℂ)‖^2 = _
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith only [congrArg (fun s : ℝ => (a^2+b^2)*s) (Real.sin_sq_add_cos_sq t)]
  have hover : spinOverlap (planarSpin t) (planarVelocity t a b) = (a : ℂ) := by
    rw [spinOverlap, Fin.sum_univ_two]
    change conj (Real.cos t : ℂ) * ((a*Real.cos t-b*Real.sin t : ℝ):ℂ) +
      conj (Real.sin t : ℂ) * ((a*Real.sin t+b*Real.cos t : ℝ):ℂ) = (a : ℂ)
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_inj]
    nlinarith only [congrArg (fun s : ℝ => a*s) (Real.sin_sq_add_cos_sq t)]
  refine ⟨hv, ?_⟩
  rw [rankOne_variation_energy (planar_unit t), hv, hover, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem planar_derivative {f θ : ℝ → ℝ} {s a b : ℝ}
    (hf : HasDerivAt f a s) (hθ : HasDerivAt θ b s) (j : Fin 2) :
    HasDerivAt (fun u => ((f u : ℂ) * planarSpin (θ u) j))
      (planarVelocity (θ s) a (f s * b) j) s := by
  fin_cases j
  · simpa [planarSpin, planarVelocity, Complex.ofReal_mul, Complex.ofReal_sub, sub_eq_add_neg,
      mul_comm, mul_assoc, mul_left_comm] using (hf.mul hθ.cos).ofReal_comp
  · simpa [planarSpin, planarVelocity, Complex.ofReal_mul, Complex.ofReal_add,
      mul_comm, mul_assoc, mul_left_comm] using (hf.mul hθ.sin).ofReal_comp

/-- For any normalized spatial amplitude the test spinor
`f(x) (cos(k x₀), sin(k x₀))` has orbital kinetic cost `A+k²` and square-root
cost `A+2k²`, where `A` is the kinetic energy of the amplitude. Thus every
coefficient strictly greater than one half fails for some frequency. -/
theorem rotating_envelope_sharp (f : Position → ℝ) (df : Position → Fin 3 → ℝ)
    (hf : Integrable (fun x => f x^2)) (hunit : (∫ x, f x^2) = 1)
    (hd : ∀ i, Integrable (fun x => df x i ^ 2)) {C : ℝ} (hC : 1 / 2 < C) :
    ∃ k : ℝ,
      let θ := fun x : Position => k * x 0
      let w := fun x i => planarVelocity (θ x) (df x i) (if i = 0 then k*f x else 0)
      (∫ x, ∑ i, spinSq (w x i)) <
        C * ∫ x, ∑ i, entrySq (rootVariation (planarSpin (θ x)) (w x i)) := by
  let A := ∫ x, ∑ i, df x i ^ 2
  let k := Real.sqrt ((|(1-C)*A|+1) / (2*C-1))
  have hk : k^2 = (|(1-C)*A|+1)/(2*C-1) := Real.sq_sqrt
    (div_nonneg (by positivity) (by linarith))
  have hgap : (2*C-1)*k^2 = |(1-C)*A|+1 := by rw [hk]; field_simp [show 2*C-1 ≠ 0 by linarith]
  refine ⟨k, ?_⟩
  dsimp only
  simp_rw [(planar_energies _ _ _).1, (planar_energies _ _ _).2, Finset.sum_add_distrib]
  have hsq (x : Position) : (∑ i : Fin 3, (if i = 0 then k * f x else 0)^2) = k^2 * f x^2 := by
    simp [mul_pow]
  simp_rw [← Finset.mul_sum, hsq]
  have hi := integrable_finsetSum Finset.univ (fun i _ => hd i)
  have hkf := hf.const_mul (k^2)
  rw [integral_add hi hkf, integral_add hi (hkf.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hunit]
  change A + _ < C * (A + _)
  nlinarith only [hgap, le_abs_self ((1-C)*A)]

end TSGA.ManyBody
