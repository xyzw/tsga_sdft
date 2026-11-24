import TSGA.LevyLieb
import TSGA.BallSequence
import TSGA.StateMixing

/-! # Spatial inversion of Coulomb ensembles

Reflection reverses the derivative in every particle coordinate. The even
cutoffs on the reference balls therefore permit averaging a state with its
reflection at fixed spin density and fixed energy.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW
open scoped ContDiff ComplexConjugate

theorem sector_neg_preserving (n : ℕ) :
    MeasurePreserving (fun x : Space n => -x) volume volume :=
  measurePreserving_pi (fun _ => (volume : Measure Position)) (fun _ => (volume : Measure Position))
    (fun _ => (LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving)

theorem sector_integral_neg {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space n → E) : (∫ x, f (-x)) = ∫ x, f x :=
  (sector_neg_preserving n).integral_comp (Homeomorph.neg (Space n)).toMeasurableEquiv.measurableEmbedding f

private theorem coulomb_neg {n : ℕ} (x : Space n) : coulomb (-x) = coulomb x := by
  unfold coulomb
  simp only [Pi.neg_apply,neg_sub_neg,norm_sub_rev]

private theorem reflected_weak {n : ℕ} (ψ : Wave n) (s : Spins n) (i : Fin n) (j : Fin 3)
    (f : Space n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, (fderiv ℝ f x (particleDirection i j)) • ψ.value s (-x)) =
      -(∫ x, f x • (-ψ.gradient s (-x) i j)) := by
  let L : Space n →L[ℝ] Space n := -(ContinuousLinearMap.id ℝ _)
  let g := f ∘ L
  have hg : ContDiff ℝ ∞ g := hf.comp L.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph (Homeomorph.neg (Space n))
  have dg (y) : fderiv ℝ g y (particleDirection i j) = -(fderiv ℝ f (-y) (particleDirection i j)) := by
    rw [((hf.differentiable (by simp) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply]
    exact map_neg (fderiv ℝ f (-y)) _
  have hw := ψ.weak_gradient s i j g hg hgc
  simp_rw [dg, neg_smul, integral_neg] at hw
  have he := sector_integral_neg (fun x => fderiv ℝ f (-x) (particleDirection i j) • ψ.value s x)
  have he' := sector_integral_neg (fun x => g x • ψ.gradient s x i j)
  simp only [neg_neg] at he
  have gs (x) : g (-x) = f x := by change f (- -x) = _; rw [neg_neg]
  simp only [gs] at he'
  simp only [smul_neg, integral_neg, neg_neg]
  exact he.trans ((neg_inj.mp hw).trans he'.symm)

def Wave.reflect {n : ℕ} (ψ : Wave n) : Wave n where
  value s x := ψ.value s (-x)
  gradient s x i j := -ψ.gradient s (-x) i j
  antisymmetric π s := (sector_neg_preserving n).quasiMeasurePreserving.tendsto_ae (ψ.antisymmetric π s)
  square_integrable s := (ψ.square_integrable s).comp_measurePreserving (sector_neg_preserving n)
  normalized := by
    apply Eq.trans _ ψ.normalized
    exact Finset.sum_congr rfl fun s _ => sector_integral_neg (fun x => ‖ψ.value s x‖^2)
  gradient_L2 s i j := ((ψ.gradient_L2 s i j).comp_measurePreserving (sector_neg_preserving n)).neg
  weak_gradient s i j := reflected_weak ψ s i j
  interaction_integrable s := by
    simpa only [Function.comp_def, coulomb_neg] using
      ((sector_neg_preserving n).integrable_comp (ψ.interaction_integrable s).1).mpr (ψ.interaction_integrable s)

@[simp] theorem Wave.kinetic_reflect {n : ℕ} (ψ : Wave n) : ψ.reflect.kinetic = ψ.kinetic := by
  simp only [kinetic,sectorIntegral,reflect,norm_neg]
  exact Finset.sum_congr rfl fun s _ => sector_integral_neg (fun x => ∑ i, ∑ j, ‖ψ.gradient s x i j‖^2)

@[simp] theorem Wave.interaction_reflect {n : ℕ} (ψ : Wave n) : ψ.reflect.interaction = ψ.interaction := by
  unfold interaction sectorIntegral
  apply Finset.sum_congr rfl
  intro s _
  simpa only [reflect,coulomb_neg] using sector_integral_neg (fun x => coulomb x*‖ψ.value s x‖^2)

@[simp] theorem Wave.density_reflect {n : ℕ} (ψ : Wave (n+1)) (x : Position) :
    ψ.reflect.matrixDensity x = ψ.matrixDensity (-x) := by
  have neg_cons (y : Space n) : -(Fin.cons x y : Space (n+1)) = Fin.cons (-x) (-y) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  ext i j
  simp only [matrixDensity, reflect, neg_cons]
  congr 1
  exact Finset.sum_congr rfl fun s _ => sector_integral_neg (fun y =>
    ψ.value (Fin.cons i s) (Fin.cons (-x) y) * conj (ψ.value (Fin.cons j s) (Fin.cons (-x) y)))

def PureState.reflect : PureState → PureState
  | .vacuum => .vacuum
  | .occupied ψ => .occupied ψ.reflect

@[simp] theorem PureState.kinetic_reflect (s : PureState) : s.reflect.kinetic = s.kinetic := by
  cases s <;> simp [kinetic, reflect]
@[simp] theorem PureState.interaction_reflect (s : PureState) : s.reflect.interaction = s.interaction := by
  cases s <;> simp [interaction, reflect]
@[simp] theorem PureState.density_reflect (s : PureState) (x : Position) : s.reflect.matrixDensity x = s.matrixDensity (-x) := by
  cases s <;> simp [matrixDensity, reflect]
@[simp] theorem PureState.particles_reflect (s : PureState) : s.reflect.particles = s.particles := by cases s <;> rfl

def MixedState.reflect (Γ : MixedState) : MixedState where
  component m := (Γ.component m).reflect
  weight := Γ.weight
  weight_nonneg := Γ.weight_nonneg
  normalized := Γ.normalized
  particles_summable := by simpa using Γ.particles_summable
  kinetic_summable := by simpa using Γ.kinetic_summable
  interaction_summable := by simpa using Γ.interaction_summable
  density_summable := by
    simp only [PureState.density_reflect]
    exact (LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.quasiMeasurePreserving.tendsto_ae Γ.density_summable

@[simp] theorem MixedState.kinetic_reflect (Γ : MixedState) : Γ.reflect.kinetic = Γ.kinetic := by simp [kinetic,reflect]
@[simp] theorem MixedState.interaction_reflect (Γ : MixedState) : Γ.reflect.interaction = Γ.interaction := by simp [interaction,reflect]
@[simp] theorem MixedState.density_reflect (Γ : MixedState) (x : Position) :
    Γ.reflect.matrixDensity x = Γ.matrixDensity (-x) := by ext i j; simp [matrixDensity,reflect]

theorem ball_cutoff_even (η : Mollifier) (n : ℕ) (x : Position) :
    (DomainSequence.balls η).cutoff n (-x) = (DomainSequence.balls η).cutoff n x := by
  classical
  let R : ℝ := n+1
  let f := (Metric.ball (0 : Position) R).indicator (fun _ => (1:ℝ))
  let k := η.scaled 1
  have hχ (y : Position) : f (-y) = f y := by
    by_cases h : ‖y‖ < R <;> simp [f,Metric.mem_ball,dist_zero_right,h]
  have hk (y : Position) : k (-y) = k y := by
    simp only [k,Mollifier.scaled,one_pow,inv_one,one_smul,one_mul]
    exact η.radial _ _ (norm_neg _)
  change (∫ y, f y * k (-x-y)) = ∫ y, f y * k (x-y)
  have H := (LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.integral_comp
    (Homeomorph.neg Position).toMeasurableEquiv.measurableEmbedding (fun y => f y * k (-x-y))
  change (∫ y, f (-y) * k (-x- -y)) = _ at H
  simpa only [hχ,show ∀ y : Position, -x- -y = -(x-y) from fun y => by abel,hk] using H.symm

end TSGA.ManyBody
