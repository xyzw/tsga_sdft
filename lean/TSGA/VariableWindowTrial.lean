import TSGA.IslandInteriorTrial
import TSGA.RootTraceRegularity

/-! # Quasi-free states for scalar windows of a variable spin density -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped ComplexOrder

def windowDensity (D : Density) (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x) : Density :=
  ⟨fun x => f x • D.matrix x, fun x => (D.positive x).smul (hf x)⟩

@[simp] theorem windowDensity_charge (D : Density) (f : Position → ℝ) (hf) (x) :
    (windowDensity D f hf).charge x = f x * D.charge x := by
  simp [Density.charge,windowDensity,Matrix.trace_smul,Complex.real_smul]

def windowRootGradient (a : Position → ℝ) (g : Position → Position)
    (M : Position → SpinMatrix) (S : MatrixGradient) : MatrixGradient :=
  fun x i => a x • S x i + (g x i) • M x

/-- Local scalar Sobolev product rule. The square-integrability of the
candidate derivative is checked before invoking the rule. -/
def WeakScalarMatrixProduct : Prop :=
  ∀ (a : Position → ℝ) (g : Position → Position) (M : Position → SpinMatrix) (S : MatrixGradient),
    (∃ b, ∀ x, |a x| ≤ b) →
    (∀ i, WeakPartialOn Set.univ i a (fun x => g x i)) → IsMatrixGradientOn Set.univ M S →
    MemLp (matrixGradNorm (windowRootGradient a g M S)) 2 →
    IsMatrixGradientOn Set.univ (fun x => a x • M x) (windowRootGradient a g M S)

theorem windowRootGradient_sq (D : Density) (S : MatrixGradient) (f : Position → ℝ)
    (hf : ∀ x, 0 ≤ f x) (g : Position → Position) (x : Position) :
    kineticDensity (windowRootGradient (fun y => √(f y)) g (D.power (1/2)) S) x ≤
      2*(f x*kineticDensity S x) + 2*(D.charge x*‖g x‖^2) := by
  have sq (G : MatrixGradient) : kineticDensity G x = ∑ i, ∑ j, ∑ k, ‖G x i j k‖^2 :=
    Real.sq_sqrt (by positivity)
  have point (i : Fin 3) (j k : Fin 2) : ‖(√(f x)) • S x i j k + (g x i) • D.power (1/2) x j k‖^2 ≤
      2*(f x*‖S x i j k‖^2) + 2*(‖g x i‖^2*‖D.power (1/2) x j k‖^2) := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le ((√(f x)) • S x i j k) ((g x i) • D.power (1/2) x j k)) 2
    simp only [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hh
    nlinarith only [hh,sq_nonneg (√(f x)*‖S x i j k‖-‖g x i‖*‖D.power (1/2) x j k‖),
      congrArg (fun t : ℝ => t * ‖S x i j k‖^2) (Real.sq_sqrt (hf x))]
  rw [sq,sq]
  apply (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => point i j k).trans_eq
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,sqrt_hilbertSchmidt_sq,← Finset.sum_mul,PiLp.norm_sq_eq_of_L2]
  ring

theorem window_product_integrable {f u : Position → ℝ} {b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc 0 b) (meas : AEMeasurable f volume) (hu : Integrable u) :
    Integrable (fun x => f x*u x) := by
  apply (hu.norm.const_mul b).mono' (meas.mul hu.aemeasurable).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖f x*u x‖ ≤ b*‖u x‖
    rw [norm_mul,Real.norm_of_nonneg (hf x).1]
    exact mul_le_mul_of_nonneg_right (hf x).2 (norm_nonneg _)

theorem window_measurable (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x) {g : Position → Position}
    (weak : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i)) : AEMeasurable f volume := by
  have h := ((locallyIntegrableOn_univ.mp (weak 0).1).aestronglyMeasurable.aemeasurable).pow_const 2
  simpa only [Real.sq_sqrt (hf _)] using h

theorem window_root_regular (product : WeakScalarMatrixProduct) {D : Density} {S : MatrixGradient}
    (reg : SqrtRegular D S) {f : Position → ℝ} {b : ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 b)
    {g : Position → Position} (weak : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i))
    (fisher : Integrable fun x => D.charge x*‖g x‖^2) :
    let Z := windowRootGradient (fun x => √(f x)) g (D.power (1/2)) S
    SqrtRegular (windowDensity D f (fun x => (hf x).1)) Z ∧
    sqrtKinetic Z ≤ 2*(∫ x, f x*kineticDensity S x)+2*(∫ x, D.charge x*‖g x‖^2) := by
  let Z := windowRootGradient (fun x => √(f x)) g (D.power (1/2)) S
  have hf' x := (hf x).1
  have hm := window_measurable f hf' weak
  have base : Integrable (kineticDensity S) := reg.grad.integrable_sq
  have hi := window_product_integrable hf hm base
  have bound := windowRootGradient_sq D S f hf' g
  have zm (i : Fin 3) (j k : Fin 2) : AEMeasurable (fun x => Z x i j k) volume := by
    exact (((locallyIntegrableOn_univ.mp (weak i).1).aestronglyMeasurable.aemeasurable.smul
      (locallyIntegrableOn_univ.mp (reg.weak i j k).2.1).aestronglyMeasurable.aemeasurable).add
      ((locallyIntegrableOn_univ.mp (weak i).2.1).aestronglyMeasurable.aemeasurable.smul
        (locallyIntegrableOn_univ.mp (reg.weak i j k).1).aestronglyMeasurable.aemeasurable))
  have zn : AEMeasurable (matrixGradNorm Z) volume := Real.continuous_sqrt.measurable.comp_aemeasurable <|
    Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      Finset.aemeasurable_fun_sum _ fun k _ => (zm i j k).norm.pow_const 2
  have H := (hi.const_mul 2).add (fisher.const_mul 2)
  have zi : Integrable (kineticDensity Z) := H.mono' (zn.pow_const 2).aestronglyMeasurable <|
    ae_of_all _ fun x => (Real.norm_of_nonneg (sq_nonneg _)).le.trans (bound x)
  have lp : MemLp (matrixGradNorm Z) 2 := (memLp_two_iff_integrable_sq zn.aestronglyMeasurable).2 zi
  have hw := product (fun x => √(f x)) g (D.power (1/2)) S
    ⟨√b,fun x => (abs_of_nonneg (Real.sqrt_nonneg _)).le.trans (Real.sqrt_le_sqrt (hf x).2)⟩ weak reg.weak lp
  have root (x) : (windowDensity D f hf').power (1/2) x = √(f x) • D.power (1/2) x := by
    simpa only [windowDensity,Density.power,Real.sqrt_eq_rpow] using SSW.positive_power_smul (D.positive x) (hf' x) (1/2)
  refine ⟨⟨?_,?_,lp⟩,?_⟩
  · rw [show (windowDensity D f hf').charge = _ from funext (windowDensity_charge D f hf')]
    exact window_product_integrable hf hm reg.charge
  · rw [funext root]
    exact hw
  · have h := integral_mono zi H bound
    simpa only [sqrtKinetic,Z,Pi.add_apply,integral_add (hi.const_mul 2) (fisher.const_mul 2),integral_const_mul] using h

theorem window_charge_moment {D : Density} {f : Position → ℝ} {b a : ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 b)
    (hm : AEMeasurable f volume) (hq : Integrable fun x => D.charge x ^ a) (ha : 1 ≤ a) :
    let N := windowDensity D f fun x => (hf x).1
    Integrable (fun x => N.charge x ^ a) ∧ chargeMoment N a ≤ b^(a-1)*(∫ x, f x*D.charge x^a) := by
  let N := windowDensity D f fun x => (hf x).1
  have bound (x) : N.charge x^a ≤ b^(a-1)*(f x*D.charge x^a) := by
    rw [show N.charge x = f x * D.charge x from windowDensity_charge ..,
      Real.mul_rpow (hf x).1 (D.charge_nonneg x)]
    have factor : (f x)^a = (f x)^(a-1)*f x := by
      simpa only [sub_add_cancel] using Real.rpow_add_one' (y := a-1) (hf x).1 (by linarith)
    rw [factor,mul_assoc]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hf x).1 (hf x).2 (by linarith)) <|
      mul_nonneg (hf x).1 (Real.rpow_nonneg (D.charge_nonneg x) _)
  have hi := (window_product_integrable hf hm hq).const_mul (b^(a-1))
  have nm : AEMeasurable (fun x => N.charge x ^ a) volume := by
    simp only [N,windowDensity_charge,Real.mul_rpow (hf _).1 (D.charge_nonneg _)]
    exact (hm.pow_const a).mul hq.aemeasurable
  have ni := hi.mono' nm.aestronglyMeasurable <| ae_of_all _ fun x =>
    (Real.norm_of_nonneg (Real.rpow_nonneg (N.charge_nonneg x) _)).le.trans (bound x)
  exact ⟨ni,(integral_mono ni hi bound).trans_eq (integral_const_mul ..)⟩

/-- The same quasi-free trial works for a boundary window, a skeleton or a
large-oscillation tile. Only the density power sees the amplitude cap. -/
theorem FiniteEnergyInputs.window_trial (H : FiniteEnergyInputs) (product : WeakScalarMatrixProduct)
    {D : Density} {S : MatrixGradient} (reg : SqrtRegular D S) {f : Position → ℝ} {b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc 0 b) {g : Position → Position}
    (weak : ∀ i, WeakPartialOn Set.univ i (fun x => √(f x)) (fun x => g x i))
    (fisher : Integrable fun x => D.charge x*‖g x‖^2)
    (power : Integrable fun x => D.charge x^(5/3:ℝ)) :
    let N := windowDensity D f fun x => (hf x).1
    ∃ Γ : MixedState, feasible N.matrix Γ ∧ Γ.interaction ≤ hartree N.charge ∧
      Γ.kinetic ≤ H.interiorConstant*(b^(2/3:ℝ)*(∫ x, f x*D.charge x^(5/3:ℝ)) +
        2*(∫ x, f x*kineticDensity S x)+2*(∫ x, D.charge x*‖g x‖^2)) := by
  let N := windowDensity D f fun x => (hf x).1
  obtain ⟨nr,grad⟩ := window_root_regular product reg hf weak fisher
  obtain ⟨ni,moment⟩ := window_charge_moment hf (window_measurable f (fun x => (hf x).1) weak) power (by norm_num)
  obtain ⟨Γ,hΓ,hT,hC⟩ := H.exists_island_state N _ nr ni
  refine ⟨Γ,hΓ,hC,hT.trans (mul_le_mul_of_nonneg_left ?_ H.interiorConstant_nonneg)⟩
  rw [show (5/3:ℝ)-1=2/3 by norm_num] at moment
  linarith only [grad,moment]

end TSGA.ManyBody
