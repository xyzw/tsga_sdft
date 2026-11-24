import TSGA.CoulombPairDensity
import TSGA.Subadditivity
import TSGA.PoissonIslands
import TSGA.IslandExterior

/-! # Microscopic estimates for the island trial

Each pair of spatial points only sees a bounded window of the marked
Poisson process. Windows may vary with the pair even on unbounded space.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization TSGA.Islands
open scoped NNReal

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsProbabilityMeasure ν]

/-- Cutoff values sampled at two test points by a single mark. -/
structure MarkPair (ν : Measure Y) where
  rate : ℝ≥0
  b : Y → ℝ
  c : Y → ℝ
  hb : Integrable b ν
  hc : Integrable c ν
  hbc : Integrable (fun y => b y*c y) ν
  range : ∀ᵐ y ∂ν, b y ∈ Set.Icc 0 1 ∧ c y ∈ Set.Icc 0 1

def MarkPair.pairMean (w : MarkPair ν) := expect w.rate ν (fun n y => uncovered w.b n y * uncovered w.c n y)

def MarkPair.covariance (w : MarkPair ν) :=
  w.pairMean - expect w.rate ν (uncovered w.b) * expect w.rate ν (uncovered w.c)

def MarkPair.overlap (w : MarkPair ν) := (w.rate:ℝ) * ∫ y, w.b y*w.c y ∂ν

theorem MarkPair.cov_le (w : MarkPair ν) : w.covariance ≤ w.overlap :=
  (covariance_le_overlap w.rate w.hb w.hc w.hbc w.range).2

theorem MarkPair.mean_eq (w : MarkPair ν) {v h : ℝ}
    (hb : (w.rate:ℝ)*(∫ y, w.b y ∂ν) = v) (hc : (w.rate:ℝ)*(∫ y, w.c y ∂ν) = v)
    (hov : w.overlap = v*h) :
    w.pairMean = Real.exp (-(2*v))*Real.exp (v*h) := by
  unfold MarkPair.pairMean
  unfold MarkPair.overlap at hov
  rw [expect_uncovered_pair w.rate w.hb w.hc w.hbc, neg_mul, mul_add, hb, hc, hov]
  rw [show -(v+v) = -(2*v) by ring]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrating the local two-point law computes the average outside
indirect interaction. The signed kernel is the pair density minus the
direct density, including the Coulomb weight. -/
theorem outside_indirect_trace (w : PairSpace → MarkPair ν)
    (χ : Ω → Position → ℝ) (k h : PairSpace → ℝ) {v : ℝ}
    (joint : Integrable (fun p : Ω × PairSpace => k p.2*(χ p.1 p.2.1*χ p.1 p.2.2)) (μ.prod pairVolume))
    (law : ∀ᵐ z ∂pairVolume, (∫ ω, χ ω z.1*χ ω z.2 ∂μ) = (w z).pairMean)
    (marks : ∀ᵐ z ∂pairVolume, ((w z).rate:ℝ)*(∫ y, (w z).b y ∂ν) = v ∧
      ((w z).rate:ℝ)*(∫ y, (w z).c y ∂ν) = v ∧ (w z).overlap = v*h z) :
    (∫ ω, ∫ z, k z*(χ ω z.1*χ ω z.2) ∂pairVolume ∂μ) =
      Real.exp (-(2*v))*(∫ z, Real.exp (v*h z)*k z ∂pairVolume) := by
  rw [integral_integral_swap (f := fun ω z => k z*(χ ω z.1*χ ω z.2)) joint, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [law, marks] with z hz hm
  rw [integral_const_mul, hz, (w z).mean_eq hm.1 hm.2.1 hm.2.2]
  ring

/-- The Hartree energy of a centered island field is controlled by the
overlap of two cutoffs. The bound on that last deterministic integral
is the HLS or Young estimate in Appendix C. -/
theorem fluctuation_of_overlap (w : PairSpace → MarkPair ν) (F : Ω → Position → ℝ)
    (ρ : Position → ℝ) (c : ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (joint : JointDirectIntegrable μ (fun ω x => c*F ω x*ρ x))
    (law : ∀ᵐ z ∂pairVolume, (∫ ω, F ω z.1*F ω z.2 ∂μ) = (w z).covariance)
    (hi : Integrable (fun z => c^2*directKernel ρ ρ z*(w z).overlap) pairVolume) :
    (∫ ω, hartree (fun x => c*F ω x*ρ x) ∂μ) ≤
      (∫ z, c^2*directKernel ρ ρ z*(w z).overlap ∂pairVolume)/2 := by
  rw [expect_hartree_as_pair joint]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply integral_mono_ae joint.integral_prod_right hi
  filter_upwards [law] with z hz
  have he ω : directKernel (fun x => c*F ω x*ρ x) (fun x => c*F ω x*ρ x) z =
      (c^2*directKernel ρ ρ z)*(F ω z.1*F ω z.2) := by unfold directKernel; ring
  simp_rw [he]
  rw [integral_const_mul, hz]
  exact mul_le_mul_of_nonneg_left (w z).cov_le
    (mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg (hρ _) (hρ _)) (norm_nonneg _)))

/-- Compare the normalized exterior expectation with the energy of the
original state. The Poisson law, localization trace, Graf–Schenker error,
IMS error and truncated-direct bound enter separately. -/
structure ExteriorLocalization {B D : Density} (t : IslandTrial μ (B.matrix+D.matrix))
    (S : MatrixGradient) (ν : Measure Y) [IsProbabilityMeasure ν] (ε r C : ℝ) where
  original : MixedState
  w : PairSpace → MarkPair ν
  χ : Ω → Position → ℝ
  p : PairSpace → ℝ
  d : PairSpace → ℝ
  h : PairSpace → ℝ
  κ : ℝ
  X : ℝ
  K : ℝ
  hκ : κ ≤ 1/2
  hdirect : d = fun z => directKernel B.charge B.charge z / 2
  pair_density : p = original.pairKernel
  direct_integrable : Integrable (directKernel B.charge B.charge) pairVolume
  hh : ∀ᵐ z ∂pairVolume, h z ∈ Set.Icc 0 1
  hj : Integrable (fun z => h z*(p z-d z)) pairVolume
  hk : Integrable (fun z => h z*d z) pairVolume
  hw : Integrable (fun z => Real.exp ((ε/2)*h z)*(p z-d z)) pairVolume
  joint : Integrable (fun a : Ω × PairSpace => (p a.2-d a.2)*(χ a.1 a.2.1*χ a.1 a.2.2)) (μ.prod pairVolume)
  law : ∀ᵐ z ∂pairVolume, (∫ ω, χ ω z.1*χ ω z.2 ∂μ) = (w z).pairMean
  marks : ∀ᵐ z ∂pairVolume, ((w z).rate:ℝ)*(∫ y, (w z).b y ∂ν) = ε/2 ∧
      ((w z).rate:ℝ)*(∫ y, (w z).c y ∂ν) = ε/2 ∧ (w z).overlap = (ε/2)*h z
  localized : t.outsideEnergy = K + ∫ ω, ∫ z, (p z-d z)*(χ ω z.1*χ ω z.2) ∂pairVolume ∂μ
  ims : K ≤ Real.exp (-(ε/2))*original.kinetic + C*ε*islandBackground B S
  gs : (1-κ)*(∫ z, h z*(p z-d z) ∂pairVolume) - X ≤ ∫ z, p z-d z ∂pairVolume
  hX : 0 ≤ X
  hX' : X ≤ C*islandBackground B S
  young : (∫ z, h z*d z ∂pairVolume) ≤ C*islandBackground B S*r^2
  indirect : |∫ z, p z-d z ∂pairVolume| ≤ C*islandBackground B S
  represents : feasible B.matrix original
  minimizes : original.kinetic + original.interaction = levyLieb B.matrix
  kinetic_trace : K = ∫ ω, (t.outside ω).kinetic ∂μ

theorem ExteriorLocalization.bound {B D : Density} {t : IslandTrial μ (B.matrix+D.matrix)}
    {S : MatrixGradient} {ε r C : ℝ} (H : ExteriorLocalization t S ν ε r C)
    (he : 0 < ε) (he' : ε ≤ 1) (hC : 0 ≤ C) (hr : ε*r^2 ≤ 1) :
    t.outsideEnergy ≤ energy B.matrix + 6*C*ε*islandBackground B S := by
  rcases H with ⟨original, w, χ, p, d, h, κ, X, K, hκ, hdirect, hpdef, hid, hh, hj, hk, hw, joint, law, marks, localized, ims, gs, hX, hX', young, indirect, _, minimizes, _⟩
  obtain ⟨hip,hpair⟩ : Integrable p pairVolume ∧ (∫ z, p z ∂pairVolume) = original.interaction :=
    hpdef ▸ original.integral_pairKernel
  have hbg : 0 ≤ islandBackground B S := add_nonneg
    (integral_nonneg fun x => add_nonneg (B.charge_nonneg x) (sq_nonneg _))
    (integral_nonneg fun _ => sq_nonneg _)
  have hd : ∀ᵐ z ∂pairVolume, 0 ≤ d z := by
    apply ae_of_all
    intro z
    rw [hdirect]
    exact div_nonneg (div_nonneg (mul_nonneg (B.charge_nonneg _) (B.charge_nonneg _)) (norm_nonneg _)) (by norm_num)
  have hp : ∀ᵐ z ∂pairVolume, 0 ≤ p z := hpdef ▸ ae_of_all _ original.pairKernel_nonneg
  have hdint : Integrable d pairVolume := hdirect ▸ hid.div_const 2
  have hi : Integrable (fun z => p z-d z) pairVolume := hip.sub hdint
  have ground : original.kinetic + (∫ z, p z-d z ∂pairVolume) = energy B.matrix := by
    rw [integral_sub hip hdint, hpair, hdirect, integral_div, ← hartree_eq_pair _ hid]
    change _ = levyLieb B.matrix - hartree B.charge
    linarith only [minimizes]
  have ht := outside_indirect_trace w χ (fun z => p z-d z) h joint law marks
  have hmain := exterior_indirect_bound (by linarith : 0 ≤ ε/2) (by linarith : ε/2 ≤ 1/2)
    hκ original.kinetic_nonneg hX hh hp hd hi hj hk hw gs
  rw [localized, ht, ← ground]
  have hscaled := mul_le_mul_of_nonneg_left young (sq_nonneg (ε/2))
  have hsmall := mul_le_mul_of_nonneg_left hr (mul_nonneg (mul_nonneg hC hbg) he.le)
  have hcost := mul_le_mul_of_nonneg_left (add_le_add indirect hX') (show 0 ≤ 4*(ε/2) by linarith)
  nlinarith only [ims, hmain, hscaled, hsmall, hcost, mul_nonneg (mul_nonneg hC hbg) he.le]

/-- A centered, scaled cutoff multiplying a deterministic charge. -/
structure CutoffCharge (μ : Measure Ω) (ν : Measure Y) [IsProbabilityMeasure ν] (ρ : Position → ℝ) where
  factor : ℝ
  field : Ω → Position → ℝ
  marks : PairSpace → MarkPair ν
  joint : JointDirectIntegrable μ (fun ω x => factor*field ω x*ρ x)
  law : ∀ᵐ z ∂pairVolume, (∫ ω, field ω z.1*field ω z.2 ∂μ) = (marks z).covariance
  weighted_integrable : Integrable (fun z => factor^2 * directKernel ρ ρ z * (marks z).overlap) pairVolume

def CutoffCharge.charge {ρ : Position → ℝ} (u : CutoffCharge μ ν ρ) (ω : Ω) (x : Position) :=
  u.factor*u.field ω x*ρ x

def CutoffCharge.hartreeMean {ρ : Position → ℝ} (u : CutoffCharge μ ν ρ) :=
  ∫ ω, hartree (fun x => u.factor*u.field ω x*ρ x) ∂μ

def CutoffCharge.overlapCost {ρ : Position → ℝ} (u : CutoffCharge μ ν ρ) :=
  (∫ z, u.factor^2 * directKernel ρ ρ z * (u.marks z).overlap ∂pairVolume)/2

theorem CutoffCharge.hartree_le {ρ : Position → ℝ} (u : CutoffCharge μ ν ρ) (hρ : ∀ x, 0 ≤ ρ x) :
    u.hartreeMean ≤ u.overlapCost :=
  fluctuation_of_overlap u.marks u.field ρ u.factor hρ u.joint u.law u.weighted_integrable

/-- HLS and Young bounds act on deterministic overlap kernels. The shell
majorant is obtained from the one- and two-island Campbell formulas. -/
structure IslandFluctuations {B D : Density} (t : IslandTrial μ (B.matrix+D.matrix))
    (S : MatrixGradient) (ν : Measure Y) [IsProbabilityMeasure ν] (ε r C : ℝ) where
  first : CutoffCharge μ ν B.charge
  added : CutoffCharge μ ν D.charge
  shell : Ω → Position → ℝ
  shell_joint : JointDirectIntegrable μ shell
  shellKernel : PairSpace → ℝ
  shell_integrable : Integrable shellKernel pairVolume
  campbell : ∀ᵐ z ∂pairVolume, (∫ ω, directKernel (shell ω) (shell ω) z ∂μ) ≤ shellKernel z
  decomposition : ∀ᵐ ω ∂μ, (fun x => (t.f ω+t.g ω) x - ((B.matrix+D.matrix) x).trace.re) =ᵐ[volume]
    first.charge ω + shell ω + added.charge ω
  domain : ∀ᵐ ω ∂μ, TripleDirectIntegrable (first.charge ω) (shell ω) (added.charge ω)
  positive : ∀ u, Integrable (directKernel u u) pairVolume → 0 ≤ hartree u
  denominator : ℝ
  denominator_ge : 1 ≤ denominator
  width : ℝ
  width_eq : width = r^(-(1/5:ℝ))/denominator
  mass : Integrable B.charge
  square : MemLp B.charge 2
  hls_first : first.overlapCost ≤ C*(ε/2)*width^2*(∫ x, B.charge x^2)
  young_shell : (∫ z, shellKernel z ∂pairVolume)/2 ≤
    C*(ε/2)*(r^(1/3:ℝ)*width^(5/3:ℝ)+width^2)*(∫ x, B.charge x^2)
  hls_added : added.overlapCost ≤ 2*C*(r^2/ε)*(∫ x, D.charge x^2)

theorem IslandFluctuations.bound {B D : Density} {t : IslandTrial μ (B.matrix+D.matrix)}
    {S : MatrixGradient} {ε r C : ℝ} (H : IslandFluctuations t S ν ε r C)
    (he : 0 < ε) (he' : ε ≤ 1) (hr : 1 ≤ r) (hmax : ε*r^2 ≤ 1) (hC : 0 ≤ C) :
    t.fluctuation ≤ 12*C*ε*islandBackground B S + 6*C*(r^2/ε)*(∫ x, D.charge x^2) := by
  have hs : (∫ ω, hartree (H.shell ω) ∂μ) ≤ (∫ z, H.shellKernel z ∂pairVolume)/2 := by
    rw [expect_hartree_as_pair H.shell_joint]
    exact div_le_div_of_nonneg_right
      (integral_mono_ae H.shell_joint.integral_prod_right H.shell_integrable H.campbell) (by norm_num)
  have h₁ : Integrable (fun ω => hartree (H.first.charge ω)) μ := integrable_hartree_of_joint H.first.joint
  have h₂ := integrable_hartree_of_joint H.shell_joint
  have h₃ : Integrable (fun ω => hartree (H.added.charge ω)) μ := integrable_hartree_of_joint H.added.joint
  have hsplit : t.fluctuation ≤ 3*(H.first.hartreeMean + (∫ ω, hartree (H.shell ω) ∂μ) + H.added.hartreeMean) := by
    change _ ≤ 3*((∫ ω, hartree (H.first.charge ω) ∂μ) + _ + (∫ ω, hartree (H.added.charge ω) ∂μ))
    erw [← integral_add h₁ h₂, ← integral_add (h₁.add h₂) h₃, ← integral_const_mul]
    apply integral_mono_ae (integrable_hartree_of_joint t.hc) (((h₁.add h₂).add h₃).const_mul 3)
    filter_upwards [H.decomposition, H.domain] with ω hsum hdom
    exact (hartree_congr hsum).le.trans (hartree_three_le hdom H.positive)
  have hw := choose_island_width he he' hr hmax H.denominator_ge
  rw [← H.width_eq] at hw
  obtain ⟨_,_,hδ,_,_,htotal⟩ := hw
  have hr' : 0 ≤ r := zero_le_one.trans hr
  have hwpos : 0 ≤ r^(1/3:ℝ)*H.width^(5/3:ℝ) :=
    mul_nonneg (Real.rpow_nonneg hr' _) (Real.rpow_nonneg hδ.le _)
  have hother : 0 ≤ H.width^3/r + (ε/2)*r^2 :=
    add_nonneg (div_nonneg (pow_nonneg hδ.le _) hr') (mul_nonneg (by linarith) (sq_nonneg _))
  have h₄ : r^(1/3:ℝ)*H.width^(5/3:ℝ) + H.width^2 ≤ 4 := by linarith only [htotal,hother]
  have h₄' : H.width^2 ≤ 4 := by linarith only [h₄,hwpos]
  let m := ∫ x, B.charge x^2
  have hm : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  have hmb : m ≤ islandBackground B S := by
    unfold islandBackground
    rw [integral_add H.mass H.square.integrable_sq]
    change (∫ x, B.charge x^2) ≤ _
    linarith only [show 0 ≤ (∫ x, B.charge x) from integral_nonneg (fun x => B.charge_nonneg x),
      show 0 ≤ sqrtKinetic S from integral_nonneg fun _ => sq_nonneg _]
  have scale : 0 ≤ C*(ε/2)*m := mul_nonneg (mul_nonneg hC (by linarith)) hm
  have a := mul_le_mul_of_nonneg_left h₄' scale
  have b := mul_le_mul_of_nonneg_left h₄ scale
  have mcost := mul_le_mul_of_nonneg_left hmb (mul_nonneg hC he.le)
  dsimp only [m] at a b mcost
  linarith only [hsplit, (H.first.hartree_le B.charge_nonneg).trans H.hls_first,
    hs.trans H.young_shell, (H.added.hartree_le D.charge_nonneg).trans H.hls_added, a, b, mcost]

/-- Weak representatives of the two square-root gradients in Lemma C.1.
The added density may have a singular square-root gradient. -/
structure IslandGradients (B D : Density) (ε : ℝ) where
  background : MatrixGradient
  background_regular : SqrtRegular B background
  combined : Density
  combined_matrix : ∀ x, combined.matrix x = D.matrix x + ε • B.matrix x
  mixed : MatrixGradient
  mixed_regular : SqrtRegular combined mixed

/-- Quasi-free trial in the islands and the two local field estimates
for its charge and its square-root gradient. -/
structure IslandInterior {B D : Density} (t : IslandTrial μ (B.matrix+D.matrix))
    {ε : ℝ} (G : IslandGradients B D ε) (r C : ℝ) where
  localDensity : Ω → Density
  density_eq : ∀ᵐ ω ∂μ, (localDensity ω).matrix =ᵐ[volume] (t.inside ω).matrixDensity
  grad : Ω → MatrixGradient
  regular : ∀ᵐ ω ∂μ, SqrtRegular (localDensity ω) (grad ω)
  quasi_free : t.insideEnergy ≤ C*((∫ ω, chargeMoment (localDensity ω) (5/3) ∂μ) + (∫ ω, sqrtKinetic (grad ω) ∂μ))
  thomas_fermi : (∫ ω, chargeMoment (localDensity ω) (5/3) ∂μ) ≤
    C*(ε*islandBackground B G.background + ε^(-(2/3:ℝ))*chargeMoment D (5/3))
  matrix_gradient : (∫ ω, sqrtKinetic (grad ω) ∂μ) ≤
    C*(ε*islandBackground B G.background + sqrtKinetic G.mixed + r⁻¹^2*(∫ x, D.charge x))

/-- Constrained-search subadditivity from one random trial. The only
electrostatic errors supplied as estimates are the Graf–Schenker, HLS,
Young and shell bounds on the underlying kernels. -/
theorem subadditivity_from_fluctuation_bound {B D : Density} {ε r C : ℝ} (G : IslandGradients B D ε)
    (t : IslandTrial μ (B.matrix+D.matrix)) (outside : ExteriorLocalization t G.background ν ε r C)
    (inside : IslandInterior t G r C) (hx : t.fluctuation ≤ 12*C*ε*islandBackground B G.background + 6*C*(r^2/ε)*(∫ x, D.charge x^2))
    (he : 0 < ε) (he' : ε ≤ 1) (hC : 0 ≤ C) (hr : ε*r^2 ≤ 1) :
    energy (B.matrix+D.matrix) ≤ energy B.matrix +
      (12*C+2*C^2)*(3*ε*islandBackground B G.background + sqrtKinetic G.mixed + islandAdded D ε r) := by
  let a := ε*islandBackground B G.background
  let g := sqrtKinetic G.mixed
  let f := ε^(-(2/3:ℝ))*chargeMoment D (5/3)
  let k := r⁻¹^2*(∫ x, D.charge x)
  let j := (r^2/ε)*(∫ x, D.charge x^2)
  have ha : 0 ≤ a := mul_nonneg he.le (add_nonneg
    (integral_nonneg fun x => add_nonneg (B.charge_nonneg x) (sq_nonneg _)) (integral_nonneg fun _ => sq_nonneg _))
  have hg : 0 ≤ g := integral_nonneg fun _ => sq_nonneg _
  have hf : 0 ≤ f := mul_nonneg (Real.rpow_nonneg he.le _) (integral_nonneg fun x => Real.rpow_nonneg (D.charge_nonneg x) _)
  have hk : 0 ≤ k := mul_nonneg (sq_nonneg _) (integral_nonneg D.charge_nonneg)
  have hj : 0 ≤ j := mul_nonneg (div_nonneg (sq_nonneg _) he.le) (integral_nonneg fun _ => sq_nonneg _)
  have ho := outside.bound he he' hC hr
  have hin := inside.quasi_free.trans (mul_le_mul_of_nonneg_left (add_le_add inside.thomas_fermi inside.matrix_gradient) hC)
  change t.insideEnergy ≤ C*(C*(a+f) + C*(a+g+k)) at hin
  have ho' : t.outsideEnergy ≤ energy B.matrix+6*C*a := by dsimp [a]; linarith only [ho]
  have hx' : t.fluctuation ≤ 12*C*a+6*C*j := by dsimp [a,j]; linarith only [hx]
  change energy (B.matrix+D.matrix) ≤ energy B.matrix+(12*C+2*C^2)*(3*ε*islandBackground B G.background+g+(f+k+j))
  rw [mul_assoc 3 ε]
  change _ ≤ energy B.matrix + (12*C+2*C^2)*(3*a+g+(f+k+j))
  have hpos := mul_nonneg hC (show 0 ≤ a+g+f+k+j by linarith)
  nlinarith only [t.energy_le, ho', hx', hin, hpos,
    mul_nonneg hC ha, mul_nonneg hC hg, mul_nonneg hC hf, mul_nonneg hC hk, mul_nonneg hC hj,
    mul_nonneg (sq_nonneg C) ha, mul_nonneg (sq_nonneg C) hg, mul_nonneg (sq_nonneg C) hf,
    mul_nonneg (sq_nonneg C) hk, mul_nonneg (sq_nonneg C) hj]

/-- Constrained-search subadditivity from one random trial. The only
electrostatic errors supplied as estimates are the Graf–Schenker, HLS,
Young and shell bounds on the underlying kernels. -/
theorem subadditivity_from_localization {B D : Density} {ε r C : ℝ} (G : IslandGradients B D ε)
    (t : IslandTrial μ (B.matrix+D.matrix)) (outside : ExteriorLocalization t G.background ν ε r C)
    (inside : IslandInterior t G r C) (fluct : IslandFluctuations t G.background ν ε r C)
    (he : 0 < ε) (he' : ε ≤ 1) (hC : 0 ≤ C) (hr₀ : 1 ≤ r) (hr : ε*r^2 ≤ 1) :
    energy (B.matrix+D.matrix) ≤ energy B.matrix +
      (12*C+2*C^2)*(3*ε*islandBackground B G.background + sqrtKinetic G.mixed + islandAdded D ε r) := by
  exact subadditivity_from_fluctuation_bound G t outside inside (fluct.bound he he' hr₀ hr hC) he he' hC hr

/-- The form used for bounded local replacements. The same physical
constant works at every admissible radius, so the radius can be chosen
after seeing the essential bound on the added density. -/
theorem subadditivity_bounded_from_localization {B D : Density} {ε cap C : ℝ}
    (G : IslandGradients B D ε) (he : 0 < ε) (he' : ε ≤ 1) (hC : 0 ≤ C)
    (hcap : 0 ≤ cap) (bounded_charge : ∀ᵐ x, D.charge x ≤ cap) (mass : Integrable D.charge)
    (trials : ∀ r : ℝ, 1 ≤ r → ε*r^2 ≤ 1 → ∃ t : IslandTrial μ (B.matrix+D.matrix),
      Nonempty (ExteriorLocalization t G.background ν ε r C) ∧ Nonempty (IslandInterior t G r C) ∧
      Nonempty (IslandFluctuations t G.background ν ε r C)) :
    energy (B.matrix+D.matrix) ≤ energy B.matrix + (12*C+2*C^2)*
      (3*ε*islandBackground B G.background + sqrtKinetic G.mixed +
      3*(ε + Real.sqrt (cap/ε) + cap/ε)*(∫ x, D.charge x)) := by
  apply subadditivity_of_bounded_charge he he' (by positivity) hcap bounded_charge mass
  intro r hr hmax
  obtain ⟨t, ⟨out⟩, ⟨inside⟩, ⟨fl⟩⟩ := trials r hr hmax
  exact subadditivity_from_localization G t out inside fl he he' hC hr hmax

end TSGA.ManyBody
