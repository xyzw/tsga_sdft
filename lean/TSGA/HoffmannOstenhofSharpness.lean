import TSGA.SpatialHoffmannOstenhofSharpness

/-! # Weak gradient witnesses for sharpness of the spin Hoffmann–Ostenhof bound -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization

def rotatingOrbital (f : Position → ℝ) (k : ℝ) (x : Position) : OrbitalValue :=
  f x • planarSpin (k * x 0)

def rotatingGradient (f : Position → ℝ) (df : Position → Fin 3 → ℝ) (k : ℝ)
    (x : Position) (i : Fin 3) : OrbitalValue :=
  planarVelocity (k * x 0) (df x i) (if i = 0 then k*f x else 0)

private theorem weak_three (i : Fin 3) (f g : Position → ℂ) :
    WeakPartialOn Set.univ i f g ↔ Spatial.WeakPartial i f g := by
  simp [WeakPartialOn, Spatial.WeakPartial, locallyIntegrableOn_univ]

private theorem gradient_three (M : Position → SpinMatrix) (Z : MatrixGradient) :
    IsMatrixGradientOn Set.univ M Z ↔ Spatial.IsMatrixGradient M Z := by
  simp only [IsMatrixGradientOn, Spatial.IsMatrixGradient, weak_three]

private theorem kinetic_three (Z : MatrixGradient) :
    kineticDensity Z = Spatial.kineticDensity Z :=
  funext fun _ => Real.sq_sqrt (by positivity)

private theorem orbital_power_three (v : Position → OrbitalValue) (p : ℝ) :
    (orbitalDensity v).power p = (Spatial.orbitalDensity v).power p := rfl

private theorem orbital_three (f : Position → ℝ) (k : ℝ) :
    rotatingOrbital f k = Spatial.rotatingOrbital f k := rfl

private theorem rotating_gradient_three (f : Position → ℝ) (df : Position → Fin 3 → ℝ) (k : ℝ) :
    rotatingGradient f df k = Spatial.rotatingGradient f df k := rfl

private theorem root_chain_three (chain : RankOneRootChain) : Spatial.RankOneRootChain 3 := by
  intro v w hw
  obtain ⟨S, hS, hform⟩ := chain v w (fun i j => (weak_three i _ _).2 (hw i j))
  exact ⟨S, (gradient_three _ S).1 hS, hform⟩

/-- Any nonnegative normalized Sobolev amplitude satisfying the ordinary weak
product rule for its rotating spinor yields a normalized orbital for which
the coefficient `C > 1/2` fails. The gradient used on the right is a weak
gradient of the actual matrix square root. -/
theorem normalized_rotating_counterexample (chain : RankOneRootChain)
    (f : Position → ℝ) (df : Position → Fin 3 → ℝ)
    (hp : ∀ x, 0 ≤ f x) (hz : ∀ x, f x = 0 → ∀ i, df x i = 0)
    (hf : Integrable (fun x => f x^2)) (hunit : (∫ x, f x^2) = 1)
    (hd : ∀ i, Integrable (fun x => df x i ^ 2))
    (hw : ∀ k : ℝ, ∀ i j, WeakPartialOn Set.univ i (fun x => rotatingOrbital f k x j)
      (fun x => rotatingGradient f df k x i j)) {C : ℝ} (hC : 1 / 2 < C) :
    ∃ (k : ℝ) (Z : MatrixGradient),
      (∫ x, spinSq (rotatingOrbital f k x)) = 1 ∧
      IsMatrixGradientOn Set.univ ((orbitalDensity (rotatingOrbital f k)).power (1/2)) Z ∧
      Integrable (fun x => ∑ i, spinSq (rotatingGradient f df k x i)) ∧
      Integrable (kineticDensity Z) ∧
      (∫ x, ∑ i, spinSq (rotatingGradient f df k x i)) < C * sqrtKinetic Z := by
  have h := Spatial.normalized_rotating_counterexample (root_chain_three chain) f df hp hz hf hunit hd
    (fun k i j => (weak_three i _ _).1 (hw k i j)) hC
  simpa only [gradient_three, kinetic_three, sqrtKinetic, Spatial.sqrtKinetic, orbital_power_three, orbital_three, rotating_gradient_three] using h

/-- An actual normalized smooth spinor test family. The test amplitude can be
any nonnegative compactly supported C¹ function of L² norm one. -/
theorem smooth_rotating_counterexample (chain : RankOneRootChain)
    (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hp : ∀ x, 0 ≤ f x)
    (hn : (∫ x, f x^2) = 1) {C : ℝ} (hC : 1/2 < C) :
    ∃ (v : Position → OrbitalValue) (w : Position → Fin 3 → OrbitalValue) (Z : MatrixGradient),
      (∫ x, spinSq (v x)) = 1 ∧ (∀ i j, WeakPartialOn Set.univ i (fun x => v x j) (fun x => w x i j)) ∧
      IsMatrixGradientOn Set.univ ((orbitalDensity v).power (1/2)) Z ∧
      Integrable (fun x => ∑ i, spinSq (w x i)) ∧ Integrable (kineticDensity Z) ∧
      (∫ x, ∑ i, spinSq (w x i)) < C * sqrtKinetic Z := by
  simpa only [weak_three, gradient_three, kinetic_three, sqrtKinetic, Spatial.sqrtKinetic, orbital_power_three, orbital_three, rotating_gradient_three] using
    (Spatial.smooth_rotating_counterexample (root_chain_three chain) f hf hc hp hn hC)

/-- Every coefficient larger than one half is violated by a normalized
one-particle spinor with a smooth compactly supported amplitude. -/
theorem hoffmann_ostenhof_sharp (chain : RankOneRootChain) {C : ℝ} (hC : 1/2 < C) :
    ∃ (v : Position → OrbitalValue) (w : Position → Fin 3 → OrbitalValue) (Z : MatrixGradient),
      (∫ x, spinSq (v x)) = 1 ∧ (∀ i j, WeakPartialOn Set.univ i (fun x => v x j) (fun x => w x i j)) ∧
      IsMatrixGradientOn Set.univ ((orbitalDensity v).power (1/2)) Z ∧
      Integrable (fun x => ∑ i, spinSq (w x i)) ∧ Integrable (kineticDensity Z) ∧
      (∫ x, ∑ i, spinSq (w x i)) < C * sqrtKinetic Z := by
  simpa only [weak_three, gradient_three, kinetic_three, sqrtKinetic, Spatial.sqrtKinetic, orbital_power_three, orbital_three, rotating_gradient_three] using
    (Spatial.hoffmann_ostenhof_sharp (root_chain_three chain) hC)

end TSGA.ManyBody
