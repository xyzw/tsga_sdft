import TSGA.IslandLocalization
import TSGA.PhysicalTSGA

/-! # Spatial Fock restriction outside the Poisson islands

The operator input is geometric localization by an arbitrary scalar mask,
with the one- and two-body density formulas and the kinetic product rule.
Stationarity cancels its first-derivative term on averaging. The remaining
kinetic cost is the Fisher intensity of the mask times the background mass.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization TSGA.Islands

/-- The three kinetic integrands for a real multiplier `√χ`. The field
`j` is twice the real orbital-gradient pairing. -/
def maskFisher (g : Position → Fin 3 → ℝ) (x : Position) := ∑ i, (g x i)^2
def maskDrift (χ : Position → ℝ) (g : Position → Fin 3 → ℝ) (i : Fin 3) (x : Position) :=
  Real.sqrt (χ x) * g x i

/-- Scalar multiplication on the one- and two-particle reduced densities of
a Fock state. The kinetic formula is the weak product rule on the original
one-body density matrix. This law is independent of any island process. -/
structure SpatialFockRestriction (Γ : MixedState) (B : Density) where
  state : (Position → ℝ) → MixedState
  tau : Position → ℝ
  j : Fin 3 → Position → ℝ
  tau_int : Integrable tau
  j_int : ∀ i, Integrable (j i)
  kinetic_trace : (∫ x, tau x) = Γ.kinetic
  restrict : ∀ (χ : Position → ℝ) (g : Position → Fin 3 → ℝ),
    feasible B.matrix Γ → (∀ x, χ x ∈ Set.Icc 0 1) →
    (∀ i, WeakPartialOn Set.univ i (fun x => Real.sqrt (χ x)) (fun x => g x i)) →
    Integrable (fun x => maskFisher g x * B.charge x) →
    feasible (fun x => χ x • B.matrix x) (state χ) ∧
    ((state χ).pairKernel =ᵐ[pairVolume] fun z => Γ.pairKernel z * (χ z.1 * χ z.2)) ∧
    (state χ).kinetic = (∫ x, χ x * tau x) + (∑ i, ∫ x, maskDrift χ g i x * j i x) +
      ∫ x, maskFisher g x * B.charge x

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Scalar statistics of a stationary exterior mask. The first derivative
has zero mean, as also follows by differentiating its constant first moment.
The Fisher estimate follows from the single-island shell bound and Campbell's formula. -/
structure ExteriorMask (μ : Measure Ω) (χ : Ω → Position → ℝ) (v fisher : ℝ) where
  gradient : Ω → Position → Fin 3 → ℝ
  range : ∀ ω x, χ ω x ∈ Set.Icc 0 1
  measurable : Measurable (fun z : Ω × Position => χ z.1 z.2)
  gradient_measurable : ∀ i, Measurable (fun z : Ω × Position => gradient z.1 z.2 i)
  weak_gradient : ∀ᵐ ω ∂μ, ∀ i, WeakPartialOn Set.univ i
    (fun x => Real.sqrt (χ ω x)) (fun x => gradient ω x i)
  first : ∀ᵐ x, (∫ ω, χ ω x ∂μ) = Real.exp (-v)
  drift : ∀ᵐ x, ∀ i, (∫ ω, maskDrift (χ ω) (gradient ω) i x ∂μ) = 0
  fisher_int : ∀ᵐ x, Integrable (fun ω => maskFisher (gradient ω) x) μ
  fisher_le : ∀ᵐ x, (∫ ω, maskFisher (gradient ω) x ∂μ) ≤ fisher

private theorem weighted_random_integrable {X : Type*} [MeasurableSpace X] {m : Measure X} [SFinite m]
    {u : Ω → X → ℝ} {f : X → ℝ} {C : ℝ}
    (hm : Measurable (fun z : Ω × X => u z.1 z.2)) (hf : Integrable f m)
    (hu : ∀ᵐ x ∂m, Integrable (fun ω => u ω x) μ)
    (hc : ∀ᵐ x ∂m, (∫ ω, ‖u ω x‖ ∂μ) ≤ C) :
    Integrable (fun z : Ω × X => u z.1 z.2 * f z.2) (μ.prod m) := by
  have hme : AEStronglyMeasurable (fun z : Ω × X => u z.1 z.2 * f z.2) (μ.prod m) :=
    hm.aestronglyMeasurable.mul hf.1.comp_snd
  apply (integrable_prod_iff' hme).2
  refine ⟨hu.mono (fun x hx => hx.mul_const (f x)), (hf.norm.const_mul C).mono' hme.norm.prod_swap.integral_prod_right' ?_⟩
  filter_upwards [hc] with x hx
  simp only [norm_mul, integral_mul_const]
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),norm_norm]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

namespace ExteriorMask
variable {χ : Ω → Position → ℝ} {v fisher : ℝ} (m : ExteriorMask μ χ v fisher)

include m

omit [IsProbabilityMeasure μ] in
private theorem fisher_nonneg (ω : Ω) (x : Position) : 0 ≤ maskFisher (m.gradient ω) x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [IsProbabilityMeasure μ] in
private theorem fisher_meas : Measurable (fun z : Ω × Position => maskFisher (m.gradient z.1) z.2) :=
  Finset.measurable_fun_sum _ fun i _ => (m.gradient_measurable i).pow_const _

private theorem fisher_weighted {f : Position → ℝ} (hf : Integrable f) :
    Integrable (fun z : Ω × Position => maskFisher (m.gradient z.1) z.2 * f z.2) (μ.prod volume) := by
  apply weighted_random_integrable m.fisher_meas hf m.fisher_int (C := fisher)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (m.fisher_nonneg _ _)] using m.fisher_le

private theorem drift_weighted (i : Fin 3) {f : Position → ℝ} (hf : Integrable f) :
    Integrable (fun z : Ω × Position => maskDrift (χ z.1) (m.gradient z.1) i z.2 * f z.2)
      (μ.prod volume) := by
  have hme : Measurable (fun z : Ω × Position => maskDrift (χ z.1) (m.gradient z.1) i z.2) :=
    m.measurable.sqrt.mul (m.gradient_measurable i)
  have bound (ω x) : ‖maskDrift (χ ω) (m.gradient ω) i x‖ ≤ 1 + maskFisher (m.gradient ω) x := by
    have hs := (Real.sqrt_le_one.mpr (m.range ω x).2)
    have hsq : (m.gradient ω x i)^2 ≤ maskFisher (m.gradient ω) x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (m.gradient ω x j)) (Finset.mem_univ i)
    rw [maskDrift,norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (abs_nonneg _) hs).trans
    nlinarith only [sq_nonneg (|m.gradient ω x i|-1), sq_abs (m.gradient ω x i), hsq, sq_nonneg (m.gradient ω x i)]
  have h₁ : ∀ᵐ x, Integrable (fun ω => maskDrift (χ ω) (m.gradient ω) i x) μ := by
    filter_upwards [m.fisher_int] with x hx
    apply ((integrable_const (1 : ℝ)).add hx).mono' (hme.comp measurable_prodMk_right).aestronglyMeasurable
    exact ae_of_all _ fun ω => bound ω x
  apply weighted_random_integrable hme hf h₁ (C := 1+fisher)
  filter_upwards [h₁,m.fisher_int,m.fisher_le] with x hx hi hl
  calc
    _ ≤ ∫ ω, 1+maskFisher (m.gradient ω) x ∂μ := integral_mono hx.norm ((integrable_const _).add hi) fun ω => bound ω x
    _ ≤ _ := by rw [integral_add (integrable_const _) hi]; simpa

private theorem mask_weighted {f : Position → ℝ} (hf : Integrable f) :
    Integrable (fun z : Ω × Position => χ z.1 z.2 * f z.2) (μ.prod volume) := by
  apply (hf.comp_snd μ).norm.mono' (m.measurable.aestronglyMeasurable.mul hf.1.comp_snd)
  apply ae_of_all
  intro z
  change ‖χ z.1 z.2 * f z.2‖ ≤ ‖f z.2‖
  rw [norm_mul,Real.norm_of_nonneg (m.range z.1 z.2).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (m.range z.1 z.2).2

/-- Fubini and the Fisher intensity put almost every localized state in
the kinetic form domain. -/
theorem restrict_ae {Γ : MixedState} {B : Density} (R : SpatialFockRestriction Γ B)
    (hΓ : feasible B.matrix Γ) (mass : Integrable B.charge) :
    ∀ᵐ ω ∂μ, feasible (fun x => χ ω x • B.matrix x) (R.state (χ ω)) ∧
      ((R.state (χ ω)).pairKernel =ᵐ[pairVolume] fun z => Γ.pairKernel z * (χ ω z.1 * χ ω z.2)) ∧
      (R.state (χ ω)).kinetic = (∫ x, χ ω x * R.tau x) +
        (∑ i, ∫ x, maskDrift (χ ω) (m.gradient ω) i x * R.j i x) +
        ∫ x, maskFisher (m.gradient ω) x * B.charge x := by
  filter_upwards [m.weak_gradient,(m.fisher_weighted mass).prod_right_ae] with ω hω hi
  exact R.restrict _ _ hΓ (m.range ω) hω hi

theorem kinetic_integrable {Γ : MixedState} {B : Density} (R : SpatialFockRestriction Γ B)
    (hΓ : feasible B.matrix Γ) (mass : Integrable B.charge) :
    Integrable (fun ω => (R.state (χ ω)).kinetic) μ := by
  have h := ((m.mask_weighted R.tau_int).integral_prod_left.add
    (integrable_finsetSum Finset.univ (fun i _ => (m.drift_weighted i (R.j_int i)).integral_prod_left))).add
      (m.fisher_weighted mass).integral_prod_left
  apply h.congr
  exact (m.restrict_ae R hΓ mass).mono fun _ h => h.2.2.symm

/-- The constant first moment preserves the indicated fraction of the original
kinetic energy. The drift of a stationary real mask disappears for each spin. -/
theorem kinetic_le {Γ : MixedState} {B : Density} (R : SpatialFockRestriction Γ B)
    (hΓ : feasible B.matrix Γ) (mass : Integrable B.charge) :
    (∫ ω, (R.state (χ ω)).kinetic ∂μ) ≤ Real.exp (-v)*Γ.kinetic + fisher*(∫ x, B.charge x) := by
  have hτ := m.mask_weighted R.tau_int
  have hj (i : Fin 3) := m.drift_weighted i (R.j_int i)
  have hg := m.fisher_weighted mass
  erw [integral_congr_ae ((m.restrict_ae R hΓ mass).mono fun _ h => h.2.2),
    integral_add (hτ.integral_prod_left.add (integrable_finsetSum Finset.univ fun i _ => (hj i).integral_prod_left)) hg.integral_prod_left,
    integral_add hτ.integral_prod_left (integrable_finsetSum Finset.univ fun i _ => (hj i).integral_prod_left),
    integral_finsetSum _ (fun i _ => (hj i).integral_prod_left)]
  have swap {f : Ω → Position → ℝ} {T : Position → ℝ} (hi : Integrable (fun z : Ω × Position => f z.1 z.2 * T z.2) (μ.prod volume)) :
      (∫ ω, ∫ x, f ω x * T x ∂volume ∂μ) = ∫ x, (∫ ω, f ω x ∂μ) * T x := by
    rw [integral_integral_swap (f := fun ω x => f ω x*T x) hi]
    simp only [integral_mul_const]
  rw [swap hτ,integral_congr_ae (m.first.mono fun x hx => congrArg (· * R.tau x) hx),integral_const_mul,R.kinetic_trace]
  have cross (i : Fin 3) : (∫ ω, ∫ x, maskDrift (χ ω) (m.gradient ω) i x * R.j i x ∂volume ∂μ) = 0 := by
    rw [swap (hj i)]
    apply integral_eq_zero_of_ae
    filter_upwards [m.drift] with x hx
    rw [hx i,zero_mul]
    rfl
  simp_rw [cross]
  simp only [Finset.sum_const_zero, add_zero]
  rw [swap hg,← integral_const_mul]
  apply add_le_add_right
  have hfi : Integrable (fun x => (∫ ω, maskFisher (m.gradient ω) x ∂μ) * B.charge x) := by
    simpa only [integral_mul_const] using hg.integral_prod_right
  exact integral_mono_ae hfi (mass.const_mul _) (m.fisher_le.mono fun x hx =>
    mul_le_mul_of_nonneg_right hx (B.charge_nonneg x))

/-- Multiplying an integrable pair kernel by the two retained fractions
gives an integrable random kernel on the full product space. -/
theorem pair_weighted {f : PairSpace → ℝ} (hf : Integrable f pairVolume) :
    Integrable (fun a : Ω × PairSpace => f a.2 * (χ a.1 a.2.1 * χ a.1 a.2.2)) (μ.prod pairVolume) := by
  have h₁ : Measurable (fun z : Ω × PairSpace => χ z.1 z.2.1) :=
    m.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h₂ : Measurable (fun z : Ω × PairSpace => χ z.1 z.2.2) :=
    m.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply (hf.comp_snd μ).norm.mono' (hf.1.comp_snd.mul (h₁.mul h₂).aestronglyMeasurable)
  apply ae_of_all
  rintro ⟨ω,x,y⟩
  change ‖f (x,y) * (χ ω x * χ ω y)‖ ≤ ‖f (x,y)‖
  rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (m.range ω x).1 (m.range ω y).1)]
  exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (m.range ω x).2 (m.range ω y).1 (m.range ω y).2)

theorem interaction_integrable {Γ : MixedState} {B : Density} (R : SpatialFockRestriction Γ B)
    (hΓ : feasible B.matrix Γ) (mass : Integrable B.charge) :
    Integrable (fun ω => (R.state (χ ω)).interaction) μ := by
  apply (m.pair_weighted Γ.integral_pairKernel.1).integral_prod_left.congr
  filter_upwards [m.restrict_ae R hΓ mass] with ω hω
  exact (integral_congr_ae hω.2.1.symm).trans (R.state (χ ω)).integral_pairKernel.2

theorem outside_energy_eq {Γ : MixedState} {B D : Density} (R : SpatialFockRestriction Γ B)
    (hΓ : feasible B.matrix Γ) (mass : Integrable B.charge)
    (t : IslandTrial μ (B.matrix+D.matrix)) (hout : ∀ᵐ ω ∂μ, t.outside ω = R.state (χ ω))
    (direct : Integrable (directKernel B.charge B.charge) pairVolume) :
    t.outsideEnergy = (∫ ω, (t.outside ω).kinetic ∂μ) + ∫ ω, ∫ z,
      (Γ.pairKernel z - directKernel B.charge B.charge z / 2)*(χ ω z.1*χ ω z.2) ∂pairVolume ∂μ := by
  let d := fun z => directKernel B.charge B.charge z/2
  have hdi : Integrable d pairVolume := direct.div_const 2
  have hki := (m.kinetic_integrable R hΓ mass).congr (hout.mono fun _ h => congrArg MixedState.kinetic h.symm)
  have hpair := m.pair_weighted Γ.integral_pairKernel.1
  have hd := m.pair_weighted direct
  have hs := m.pair_weighted (Γ.integral_pairKernel.1.sub hdi)
  erw [IslandTrial.outsideEnergy, ← integral_add hki hs.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [hout,m.restrict_ae R hΓ mass,t.f_density,hpair.prod_right_ae,hd.prod_right_ae] with ω hω hR hf hp hD
  have he : t.f ω =ᵐ[volume] fun x => χ ω x * B.charge x := by
    filter_upwards [hf,hR.1] with x hx hB
    rw [hx,hω,hB,Matrix.trace_smul]
    simp [Complex.real_smul,Density.charge]
  have hd' (z : PairSpace) : directKernel (fun x => χ ω x*B.charge x) (fun x => χ ω x*B.charge x) z =
      directKernel B.charge B.charge z * (χ ω z.1 * χ ω z.2) := by unfold directKernel; ring
  have ihd : Integrable (directKernel (fun x => χ ω x*B.charge x) (fun x => χ ω x*B.charge x)) pairVolume := by
    exact hD.congr (ae_of_all _ fun z => (hd' z).symm)
  rw [hartree_congr he, hartree_eq_pair _ ihd, hω, ← (R.state (χ ω)).integral_pairKernel.2, integral_congr_ae hR.2.1]
  rw [integral_congr_ae (ae_of_all _ hd')]
  have e (z : PairSpace) : (Γ.pairKernel z-directKernel B.charge B.charge z/2)*(χ ω z.1*χ ω z.2) =
      Γ.pairKernel z*(χ ω z.1*χ ω z.2) - (directKernel B.charge B.charge z*(χ ω z.1*χ ω z.2))/2 := by ring
  change _ = (R.state (χ ω)).kinetic + ∫ z, (Γ.pairKernel z-directKernel B.charge B.charge z/2)*(χ ω z.1*χ ω z.2) ∂pairVolume
  rw [integral_congr_ae (ae_of_all _ e)]
  rw [integral_sub hp (hD.div_const 2), integral_div]
  ring

end ExteriorMask

/-- Coefficient controlling the background's indirect energy at a minimizer.
It depends only on the finite one-body trial and the Lieb–Oxford constant. -/
def exteriorFormConstant (H : FiniteEnergyInputs) : ℝ :=
  H.loCoeff + H.cTF*(1+H.κ₁) + 8*(1+H.κ₂)

private theorem background_parts {B : Density} {S : MatrixGradient} (hm : Integrable B.charge)
    (hs : Integrable (fun x => B.charge x^2)) :
    0 ≤ (∫ x, B.charge x) ∧ 0 ≤ (∫ x, B.charge x^2) ∧ 0 ≤ sqrtKinetic S ∧
      (∫ x, B.charge x) + (∫ x, B.charge x^2) + sqrtKinetic S = islandBackground B S := by
  exact ⟨integral_nonneg B.charge_nonneg, integral_nonneg (fun _ => sq_nonneg _),
    integral_nonneg (fun _ => sq_nonneg _), by rw [islandBackground,integral_add hm hs]⟩

theorem exterior_indirect_of_minimizer (H : FiniteEnergyInputs) {Γ : MixedState} {B : Density} {S : MatrixGradient}
    (reg : SqrtRegular B S) (sq : Integrable (fun x => B.charge x^2)) (hΓ : feasible B.matrix Γ)
    (minimizes : Γ.kinetic + Γ.interaction = levyLieb B.matrix)
    (direct : Integrable (directKernel B.charge B.charge) pairVolume) :
    |∫ z, Γ.pairKernel z - directKernel B.charge B.charge z/2 ∂pairVolume| ≤ exteriorFormConstant H * islandBackground B S := by
  rw [integral_sub Γ.integral_pairKernel.1 (direct.div_const 2),Γ.integral_pairKernel.2,integral_div,← hartree_eq_pair _ direct]
  let M := ∫ x, B.charge x + B.charge x^2
  have hM : 0 ≤ M := integral_nonneg fun x => add_nonneg (B.charge_nonneg _) (sq_nonneg _)
  have hS : 0 ≤ sqrtKinetic S := integral_nonneg fun _ => sq_nonneg _
  have pw (x : Position) (a : ℝ) (ha : a ∈ Set.Icc 1 2) : B.charge x ^ a ≤ B.charge x + B.charge x^2 := by
    rcases (B.charge_nonneg x).eq_or_lt with hx|hx
    · simp [← hx,Real.zero_rpow (show a ≠ 0 by linarith [ha.1])]
    · exact BulkRegime.density_power_le hx ha
  have i43 : chargeMoment B (4/3) ≤ M := integral_mono_of_nonneg
    (ae_of_all _ fun x => Real.rpow_nonneg (B.charge_nonneg x) _) (reg.charge.add sq)
    (ae_of_all _ fun x => pw x _ (by constructor <;> norm_num))
  have i53 : traceMoment B (5/3) ≤ M := integral_mono_of_nonneg (ae_of_all _ fun x => tracePower_nonneg B x _)
    (reg.charge.add sq) (ae_of_all _ fun x => (tracePower_le_charge B x (by norm_num)).trans
      (pw x _ (by constructor <;> norm_num)))
  have h := kinetic_and_energy_upper H.cTF_nonneg H.trials H.quasiFree reg (ε := 1) zero_lt_one
  have hu := h.1.trans h.2
  norm_num only [Real.sqrt_one,mul_one,div_one] at hu
  change levyLieb B.matrix - hartree B.charge ≤ _ at hu
  let A := H.cTF*(1+H.κ₁)
  let J := 8*(1+H.κ₂)
  have hA : 0 ≤ A := mul_nonneg H.cTF_nonneg (by linarith [H.κ₁_nonneg])
  have hJ : 0 ≤ J := by dsimp [J]; linarith [H.κ₂_nonneg]
  have upper : Γ.interaction - hartree B.charge ≤ A*M + J*sqrtKinetic S := by
    dsimp only [A,J]
    nlinarith only [hu,minimizes,Γ.kinetic_nonneg,mul_le_mul_of_nonneg_left i53 hA]
  have lower := H.liebOxford B Γ hΓ
  change |Γ.interaction - hartree B.charge| ≤ (H.loCoeff + A + J)*(M + sqrtKinetic S)
  rw [abs_le]
  constructor <;> nlinarith only [lower,upper,mul_le_mul_of_nonneg_left i43 H.lo_nonneg,
    mul_nonneg hA hS,mul_nonneg hA hM,mul_nonneg hJ hS,mul_nonneg hJ hM,mul_nonneg H.lo_nonneg hM,mul_nonneg H.lo_nonneg hS]

/-- The joint Poisson exterior probability, expressed in finite windows
containing the islands that can cover either test point. -/
structure ExteriorOverlap (μ : Measure Ω) {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    [IsProbabilityMeasure ν] (χ : Ω → Position → ℝ) (v : ℝ) where
  w : PairSpace → MarkPair ν
  h : PairSpace → ℝ
  measurable : Measurable h
  range : ∀ᵐ z ∂pairVolume, h z ∈ Set.Icc 0 1
  law : ∀ᵐ z ∂pairVolume, (∫ ω, χ ω z.1 * χ ω z.2 ∂μ) = (w z).pairMean
  marks : ∀ᵐ z ∂pairVolume, ((w z).rate:ℝ)*(∫ y, (w z).b y ∂ν) = v ∧
    ((w z).rate:ℝ)*(∫ y, (w z).c y ∂ν) = v ∧ (w z).overlap = v*h z

/-- Smeared Graf–Schenker for the indirect two-body kernel, in the
normalization of Lewin, Lieb and Seiringer, equation (53). -/
def IslandSmearedGrafSchenker (h : PairSpace → ℝ) (r δ G : ℝ) : Prop :=
  ∀ (Γ : MixedState) (B : Density), feasible B.matrix Γ → Integrable B.charge →
    Integrable (fun x => B.charge x^2) → Integrable (directKernel B.charge B.charge) pairVolume →
    (1-G*δ/r) * (∫ z, h z*(Γ.pairKernel z-directKernel B.charge B.charge z/2) ∂pairVolume) -
        ((G/r)*(∫ x, B.charge x) + (G*δ^3/r)*(∫ x, B.charge x^2)) ≤
      ∫ z, Γ.pairKernel z-directKernel B.charge B.charge z/2 ∂pairVolume

private theorem bounded_mult_integrable {X : Type*} [MeasurableSpace X] {m : Measure X} {f w : X → ℝ}
    (hi : Integrable f m) (hm : Measurable w) {A : ℝ} (hb : ∀ᵐ x ∂m, ‖w x‖ ≤ A) :
    Integrable (fun x => w x * f x) m := by
  apply (hi.norm.const_mul A).mono' (hm.aestronglyMeasurable.mul hi.1)
  filter_upwards [hb] with x hx
  change ‖w x * f x‖ ≤ A * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- Realize the normalized exterior input to the island comparison using
the selected restricted states. The scale bounds can be supplied by
`choose_island_width`. The truncated direct integral is a scalar Young
estimate, and every other interaction bound comes from Graf–Schenker,
Lieb–Oxford and the finite-system trial. -/
noncomputable def ExteriorMask.toLocalization {χ : Ω → Position → ℝ} {ε fisher : ℝ}
    (m : ExteriorMask μ χ (ε/2) fisher) {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    [IsProbabilityMeasure ν] (o : ExteriorOverlap μ ν χ (ε/2)) {Γ : MixedState} {B D : Density}
    {S : MatrixGradient} (H : FiniteEnergyInputs) (reg : SqrtRegular B S)
    (sq : Integrable (fun x => B.charge x^2)) (hΓ : feasible B.matrix Γ)
    (minimizes : Γ.kinetic + Γ.interaction = levyLieb B.matrix)
    (direct : Integrable (directKernel B.charge B.charge) pairVolume)
    (R : SpatialFockRestriction Γ B) (t : IslandTrial μ (B.matrix+D.matrix))
    (hout : ∀ᵐ ω ∂μ, t.outside ω = R.state (χ ω)) {r δ G C : ℝ}
    (he : 0 ≤ ε) (hr : 1 ≤ r) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (hG : 0 ≤ G) (hGC : G ≤ C)
    (hκ : G*δ/r ≤ 1/2) (hs : fisher ≤ C*ε) (hEC : exteriorFormConstant H ≤ C)
    (gs : IslandSmearedGrafSchenker o.h r δ G)
    (truncated_direct : (∫ z, o.h z * (directKernel B.charge B.charge z/2) ∂pairVolume)
      ≤ C*r^2 * (∫ x, B.charge x^2)) : ExteriorLocalization t S ν ε r C := by
  let d := fun z => directKernel B.charge B.charge z/2
  have hd : Integrable d pairVolume := direct.div_const 2
  have hi : Integrable (fun z => Γ.pairKernel z-d z) pairVolume := Γ.integral_pairKernel.1.sub hd
  have hh : ∀ᵐ z ∂pairVolume, ‖o.h z‖ ≤ 1 :=
    o.range.mono fun z hz => (Real.norm_of_nonneg hz.1).le.trans hz.2
  have hex : ∀ᵐ z ∂pairVolume, ‖Real.exp ((ε/2)*o.h z)‖ ≤ Real.exp (ε/2) :=
    o.range.mono fun z hz => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_of_le_one_right (by linarith) hz.2)
  obtain ⟨mpos,spos,kpos,geb⟩ := background_parts (S := S) reg.charge sq
  have bpos : 0 ≤ islandBackground B S := by linarith
  have hC := hG.trans hGC
  let X := (G/r)*(∫ x, B.charge x) + (G*δ^3/r)*(∫ x, B.charge x^2)
  have rpos : 0 < r := by linarith
  refine {
    original := Γ, w := o.w, χ := χ, p := Γ.pairKernel, d := d, h := o.h,
    κ := G*δ/r, X := X, K := ∫ ω, (t.outside ω).kinetic ∂μ,
    hκ := hκ, hdirect := rfl, pair_density := rfl, direct_integrable := direct, hh := o.range,
    hj := bounded_mult_integrable hi o.measurable hh,
    hk := bounded_mult_integrable hd o.measurable hh,
    hw := bounded_mult_integrable hi ((measurable_const.mul o.measurable).exp) hex,
    joint := m.pair_weighted hi, law := o.law, marks := o.marks,
    localized := m.outside_energy_eq R hΓ reg.charge t hout direct,
    gs := gs Γ B hΓ reg.charge sq direct, represents := hΓ, minimizes := minimizes, kinetic_trace := rfl,
    ims := ?_, hX := ?_, hX' := ?_, young := ?_, indirect := ?_
  }
  · rw [integral_congr_ae (hout.mono fun _ h => congrArg MixedState.kinetic h)]
    apply (m.kinetic_le R hΓ reg.charge).trans
    apply add_le_add_right
    exact (mul_le_mul_of_nonneg_right hs mpos).trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC he))
  · dsimp [X]
    positivity
  · have h1 : G/r ≤ C := (div_le_self hG hr).trans hGC
    have h2 : G*δ^3/r ≤ C :=
      ((div_le_self (mul_nonneg hG (pow_nonneg hδ _)) hr).trans
        (mul_le_of_le_one_right hG (pow_le_one₀ hδ hδ'))).trans hGC
    dsimp [X]
    nlinarith only [mul_le_mul_of_nonneg_right h1 mpos, mul_le_mul_of_nonneg_right h2 spos,
      congrArg (fun a : ℝ => C*a) geb,mul_nonneg hC kpos]
  · refine truncated_direct.trans ?_
    rw [mul_right_comm C (r^2)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) (sq_nonneg r)
  · exact (exterior_indirect_of_minimizer H reg sq hΓ minimizes direct).trans (mul_le_mul_of_nonneg_right hEC bpos)

end TSGA.ManyBody
