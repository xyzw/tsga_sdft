import TSGA.SpatialHoffmannOstenhof
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Optimality of the spin Hoffmann–Ostenhof bound in every positive dimension -/

noncomputable section
namespace TSGA.ManyBody.Spatial
open MeasureTheory

variable {d : ℕ} [NeZero d]

/-- For any normalized spatial amplitude the test spinor
`f(x) (cos(k x₀), sin(k x₀))` has orbital kinetic cost `A+k²` and square-root
cost `A+2k²`, where `A` is the kinetic energy of the amplitude. Thus every
coefficient strictly greater than one half fails for some frequency. -/
theorem rotating_envelope_sharp (f : Point d → ℝ) (df : Point d → Fin d → ℝ)
    (hf : Integrable (fun x => f x^2)) (hunit : (∫ x, f x^2) = 1)
    (hd : ∀ i, Integrable (fun x => df x i ^ 2)) {C : ℝ} (hC : 1 / 2 < C) :
    ∃ k : ℝ,
      let θ := fun x : Point d => k * x 0
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
  have hsq (x : Point d) : (∑ i : Fin d, (if i = 0 then k * f x else 0)^2) = k^2 * f x^2 := by
    simp [mul_pow]
  simp_rw [← Finset.mul_sum, hsq]
  have hi := integrable_finsetSum Finset.univ (fun i _ => hd i)
  have hkf := hf.const_mul (k^2)
  rw [integral_add hi hkf, integral_add hi (hkf.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hunit]
  change A + _ < C * (A + _)
  nlinarith only [hgap, le_abs_self ((1-C)*A)]


def rotatingOrbital (f : Point d → ℝ) (k : ℝ) (x : Point d) : OrbitalValue :=
  f x • planarSpin (k * x 0)

def rotatingGradient (f : Point d → ℝ) (df : Point d → Fin d → ℝ) (k : ℝ)
    (x : Point d) (i : Fin d) : OrbitalValue :=
  planarVelocity (k * x 0) (df x i) (if i = 0 then k*f x else 0)

private theorem rotating_mass (f : Point d → ℝ) (k : ℝ) (x : Point d) :
    spinSq (rotatingOrbital f k x) = f x ^ 2 := by
  have hs (a : ℝ) (v : OrbitalValue) : spinSq (a • v) = a^2 * spinSq v := by
    simp only [spinSq, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  rw [rotatingOrbital, hs, planar_unit, mul_one]

/-- Any nonnegative normalized Sobolev amplitude satisfying the ordinary weak
product rule for its rotating spinor yields a normalized orbital for which
the coefficient `C > 1/2` fails. The gradient used on the right is a weak
gradient of the actual matrix square root. -/
theorem normalized_rotating_counterexample (chain : RankOneRootChain d)
    (f : Point d → ℝ) (df : Point d → Fin d → ℝ)
    (hp : ∀ x, 0 ≤ f x) (hz : ∀ x, f x = 0 → ∀ i, df x i = 0)
    (hf : Integrable (fun x => f x^2)) (hunit : (∫ x, f x^2) = 1)
    (hd : ∀ i, Integrable (fun x => df x i ^ 2))
    (hw : ∀ k : ℝ, ∀ i j, WeakPartial i (fun x => rotatingOrbital f k x j)
      (fun x => rotatingGradient f df k x i j)) {C : ℝ} (hC : 1 / 2 < C) :
    ∃ (k : ℝ) (Z : Gradient d),
      (∫ x, spinSq (rotatingOrbital f k x)) = 1 ∧
      IsMatrixGradient ((orbitalDensity (rotatingOrbital f k)).power (1/2)) Z ∧
      Integrable (fun x => ∑ i, spinSq (rotatingGradient f df k x i)) ∧
      Integrable (kineticDensity Z) ∧
      (∫ x, ∑ i, spinSq (rotatingGradient f df k x i)) < C * sqrtKinetic Z := by
  obtain ⟨k, ht⟩ := rotating_envelope_sharp f df hf hunit hd hC
  obtain ⟨Z, hZ, hc⟩ := chain (rotatingOrbital f k) (rotatingGradient f df k) (hw k)
  refine ⟨k, Z, by simpa only [rotating_mass] using hunit, hZ, ?_⟩
  have he : (fun x => kineticDensity Z x) =ᵐ[volume] fun x =>
      ∑ i, entrySq (rootVariation (planarSpin (k*x 0)) (rotatingGradient f df k x i)) := by
    filter_upwards [hc] with x hx
    have hs : kineticDensity Z x = ∑ i, entrySq (Z x i) := rfl
    rw [hs]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h0 : f x = 0
    · have hv : rotatingGradient f df k x i = 0 := by
        ext j
        fin_cases j <;> simp [rotatingGradient, planarVelocity, h0, hz x h0]
      rcases hx with ⟨_, heq⟩ | ⟨z, _, _, heq⟩ <;> simp [heq, hv, entrySq, rootVariation, spinOverlap]
    · rcases hx with ⟨hv, _⟩ | ⟨z, _, heq, he⟩
      · have hm := rotating_mass f k x
        rw [hv] at hm
        simp [spinSq] at hm
        exact (h0 (by nlinarith [hm])).elim
      · rw [rotating_mass, Real.sqrt_sq (hp x)] at heq
        have hv : planarSpin (k*x 0) = z := (smul_right_injective _ h0) heq
        rw [he, hv]
  have hi (i : Fin d) : Integrable (fun x => spinSq (rotatingGradient f df k x i)) := by
    simp only [rotatingGradient, (planar_energies _ _ _).1]
    by_cases h : i = 0
    · simp only [h, ↓reduceIte, mul_pow]
      exact (hd 0).add (hf.const_mul (k^2))
    · simp only [h, ↓reduceIte, zero_pow (by decide : 2 ≠ 0), add_zero]
      exact hd i
  have hbad : (∫ x, ∑ i, spinSq (rotatingGradient f df k x i)) < C * sqrtKinetic Z := by
    unfold sqrtKinetic
    rw [integral_congr_ae he]
    exact ht
  have hpos : 0 < C * sqrtKinetic Z := lt_of_le_of_lt
    (integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) hbad
  have hZint : Integrable (kineticDensity Z) := Integrable.of_integral_ne_zero fun hz => by
    change 0 < C * (∫ x, kineticDensity Z x) at hpos
    simp [hz] at hpos
  exact ⟨integrable_finsetSum _ (fun i _ => hi i), hZint, hbad⟩

omit [NeZero d] in
private theorem smooth_weak (u : Point d → ℂ) (hu : ContDiff ℝ 1 u) (i : Fin d) :
    WeakPartial i u (fun x => fderiv ℝ u x (PiLp.single 2 i 1)) := by
  let e : Point d := PiLp.single 2 i 1
  have hd : Continuous (fun x => fderiv ℝ u x e) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine ⟨hu.continuous.locallyIntegrable, hd.locallyIntegrable, ?_⟩
  intro ψ hψ hc
  have hw := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (v := e)
    (hu.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ e))
    (hd.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc)
    (hu.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc)
    (fun x _ => hψ.differentiable (by simp) x) (fun x _ => hu.differentiable (by norm_num) x)
  rw [hw, neg_neg]

private theorem rotating_weak (f : Point d → ℝ) (hf : ContDiff ℝ 1 f) (k : ℝ) (i : Fin d)
    (j : Fin 2) :
    WeakPartial i (fun x => rotatingOrbital f k x j)
      (fun x => rotatingGradient f (fun y l => fderiv ℝ f y (PiLp.single 2 l 1)) k x i j) := by
  let v : Point d := PiLp.single 2 i 1
  let u := fun x => rotatingOrbital f k x j
  have hu : ContDiff ℝ 1 u := by
    have hproj : ContDiff ℝ 1 (fun x : Point d => x 0) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) 0).contDiff
    have ht : ContDiff ℝ 1 (fun x : Point d => k*x 0) := contDiff_const.mul hproj
    have hcast : ContDiff ℝ 1 ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    fin_cases j
    · exact (hcast.comp hf).mul (hcast.comp (Real.contDiff_cos.comp ht))
    · exact (hcast.comp hf).mul (hcast.comp (Real.contDiff_sin.comp ht))
  have hpartial (x : Point d) : fderiv ℝ u x v =
      rotatingGradient f (fun y l => fderiv ℝ f y (PiLp.single 2 l 1)) k x i j := by
    let θ := fun x : Point d => k * x 0
    have hθ : HasFDerivAt θ (k • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) 0)) x :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) 0).hasFDerivAt.const_smul k
    have ha := ((hf.differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt v)
    have ht := hθ.hasLineDerivAt v
    have H := planar_derivative ha ht j
    have H' := (hu.differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt v
    apply HasDerivAt.unique H' (by
      simpa [u, rotatingOrbital, rotatingGradient, θ, v, PiLp.single_apply, eq_comm,
        Algebra.smul_def, mul_ite, mul_assoc, mul_comm, mul_left_comm] using H)
  have := smooth_weak u hu i
  simpa only [← hpartial] using this

/-- An actual normalized smooth spinor test family. The test amplitude can be
any nonnegative compactly supported C¹ function of L² norm one. -/
theorem smooth_rotating_counterexample (chain : RankOneRootChain d)
    (f : Point d → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hp : ∀ x, 0 ≤ f x)
    (hn : (∫ x, f x^2) = 1) {C : ℝ} (hC : 1/2 < C) :
    ∃ (v : Point d → OrbitalValue) (w : Point d → Fin d → OrbitalValue) (Z : Gradient d),
      (∫ x, spinSq (v x)) = 1 ∧ (∀ i j, WeakPartial i (fun x => v x j) (fun x => w x i j)) ∧
      IsMatrixGradient ((orbitalDensity v).power (1/2)) Z ∧
      Integrable (fun x => ∑ i, spinSq (w x i)) ∧ Integrable (kineticDensity Z) ∧
      (∫ x, ∑ i, spinSq (w x i)) < C * sqrtKinetic Z := by
  let df := fun (x : Point d) (i : Fin d) => fderiv ℝ f x (PiLp.single 2 i 1)
  have hz (x : Point d) (heq : f x = 0) (i : Fin d) : df x i = 0 := by
    have hmin : IsLocalMin f x := Filter.Eventually.of_forall fun y => heq ▸ hp y
    simp [df, hmin.fderiv_eq_zero]
  have hI {g : Point d → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) :
      Integrable (fun x => g x^2) volume := by
    rw [show (fun x => g x^2) = g*g by ext; simp [sq]]
    exact (hg.mul hg).integrable_of_hasCompactSupport (hs.mul_right (f' := g))
  have hd (i) : Integrable (fun x => df x i ^ 2) :=
    hI ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
  obtain ⟨k, Z, hunit, hZ, hfin, hZfin, hbad⟩ := normalized_rotating_counterexample chain f df hp hz
    (hI hf.continuous hc) hn hd (rotating_weak f hf) hC
  exact ⟨_, _, Z, hunit, rotating_weak f hf k, hZ, hfin, hZfin, hbad⟩

/-- Every coefficient larger than one half is violated by a normalized
one-particle spinor with a smooth compactly supported amplitude. -/
theorem hoffmann_ostenhof_sharp (chain : RankOneRootChain d) {C : ℝ} (hC : 1/2 < C) :
    ∃ (v : Point d → OrbitalValue) (w : Point d → Fin d → OrbitalValue) (Z : Gradient d),
      (∫ x, spinSq (v x)) = 1 ∧ (∀ i j, WeakPartial i (fun x => v x j) (fun x => w x i j)) ∧
      IsMatrixGradient ((orbitalDensity v).power (1/2)) Z ∧
      Integrable (fun x => ∑ i, spinSq (w x i)) ∧ Integrable (kineticDensity Z) ∧
      (∫ x, ∑ i, spinSq (w x i)) < C * sqrtKinetic Z := by
  let b : ContDiffBump (0 : Point d) := ⟨1, 2, by norm_num, by norm_num⟩
  let A := ∫ x, b x ^ 2
  have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hc : HasCompactSupport (fun x => b x^2) := by
    rw [show (fun x => b x^2) = (b : Point d → ℝ) * (fun x => b x) by ext; simp [sq]]
    exact b.hasCompactSupport.mul_right
  have ha : 0 < A := integral_pos_of_integrable_nonneg_nonzero (x := (0 : Point d))
    (b.continuous.pow 2) ((b.continuous.pow 2).integrable_of_hasCompactSupport hc)
    (fun x => sq_nonneg _) (by simp [hb])
  let f := fun x : Point d => b x / √A
  have hfc : HasCompactSupport f := by
    rw [show f = (b : Point d → ℝ) * (fun _ => (√A)⁻¹) by ext; simp [f, div_eq_mul_inv]]
    exact b.hasCompactSupport.mul_right
  have hn : (∫ x, f x^2) = 1 := by
    simp only [f, div_pow, Real.sq_sqrt ha.le, integral_div]
    exact div_self ha.ne'
  exact smooth_rotating_counterexample chain f (b.contDiff.div_const _) hfc
    (fun x => div_nonneg (b.nonneg' x) (Real.sqrt_nonneg _)) hn hC

end TSGA.ManyBody.Spatial
