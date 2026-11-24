import TSGA.SmallBallReplacementPairs

/-! # Signed freezing of the finite Coulomb energy on a physical window -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW Metric Set Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

/-- A common explicit upper bound on the two island costs. -/
def frozenAdditionCost {K : Set Position} (t : SpiralTaper K) (S : MatrixGradient)
    (g : Position → Position) (ε C dist r : ℝ) :=
  let V := ∫ x, t.shape x
  let bg := affineSpiralKinetic t S g 1 (2*r)
  let mixed := affineSpiralKinetic t S g ε⁻¹ (2*dist+ε*(2*r))
  (12*C+2*C^2)*(3*ε*((2*r+(2*r)^2)*V+bg) + mixed +
    3*(ε+√(2*dist/ε)+2*dist/ε)*(2*dist*V))

private theorem ordered_cost {K : Set Position} {t : SpiralTaper K} {B D : Density} {ε dist C r : ℝ}
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Y} [IsProbabilityMeasure ν]
    (A : OrderedSpiralAddition μ ν t B D ε dist C) (treg : FrozenTaperRegular t) (S : MatrixGradient)
    (he : 0 < ε) (hd : 0 ≤ dist) (hC : 0 ≤ C) (cap : ∀ x ∈ K, B.charge x ≤ 2*r)
    (domain : IslandDensityDomain (t.field B) (t.residual B D A.order))
    (bg : sqrtKinetic A.gradients.background ≤ affineSpiralKinetic t S treg.grad 1 (2*r))
    (mix : sqrtKinetic A.gradients.mixed ≤ affineSpiralKinetic t S treg.grad ε⁻¹ (2*dist+ε*(2*r))) :
    A.cost ≤ frozenAdditionCost t S treg.grad ε C dist r := by
  have massI := A.gradients.background_regular.charge.add domain.background_square.integrable_sq
  have hm := integral_mono massI (treg.mass.const_mul (2*r+(2*r)^2)) (fun x => by
    simp only [Pi.add_apply,t.field_charge]
    by_cases mem : x ∈ K
    · have hf := t.range x
      have h1 := mul_le_mul_of_nonneg_left (cap x mem) hf.1
      have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (B.charge_nonneg _) (cap x mem) 2) hf.1
      have hv := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hf.1 hf.2) (sq_nonneg (B.charge x))
      change t.shape x * B.charge x + (t.shape x * B.charge x)^2 ≤ _
      nlinarith only [h1,h2,hv]
    · simp [t.outside x mem])
  rw [integral_const_mul] at hm
  have ib := add_le_add hm bg
  have re := A.residual_mass treg.mass
  unfold OrderedSpiralAddition.cost frozenAdditionCost islandBackground
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left ib (by positivity)) mix)
    (mul_le_mul_of_nonneg_left re (by positivity))) (by positivity)

private theorem axes_gauge {c : Position} {R : ℝ} {t : SpiralTaper (closedBall c R)}
    {N D : Density} {W : ℝ} (axes : TileAxisChoice t N D W) (F : FiniteEnergyInputs)
    (spin : LocalSpinCalculus) (rep : ∃ Γ, feasible (t.field D).matrix Γ) :
    ∃ G : GaugeComparison (t.field D) (t.field N) F.loCoeff, G.forwardCost = W ∧ G.inverseCost = W := by
  cases axes with
  | unchanged => exact ⟨GaugeComparison.identity F _ rep,rfl,rfl⟩
  | polarized radius hr sob cap peak minor small ha ha' osc weak charge shape root kin =>
    obtain ⟨G,hf,hb⟩ := gapped_alignmentGauge radius hr t F spin sob cap peak minor small ha ha' osc
      weak charge shape root kin rep
    exact ⟨G,hf,hb.trans hf⟩

/-- Concrete island witnesses for both directions, with a common scalar
majorant for their costs. The two rotation costs are identified exactly. -/
theorem small_ball_replacement {c : Position} {R : ℝ} {t : SpiralTaper (closedBall c R)}
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Measure Z} [SFinite ι] {ε dist C r W p v : ℝ} {lo hi : SpinMatrix}
    {φ : Phase} {N D : Density} {S : MatrixGradient} (F : IslandFockInputs μ)
    (radii : CoulombIslandRadii μ ι ε C) (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct)
    (sob : SobolevLipschitzComposition) (treg : FrozenTaperRegular t) (reg : SqrtRegular N S)
    (cont : Continuous N.matrix) (power : Continuous (N.power 1)) (axes : TileAxisChoice t N D W)
    (pl : lo.PosSemidef) (ph : hi.PosSemidef) (hφ : φ.Regular p)
    (small : ∀ x ∈ closedBall c R, lo ≤ D.matrix x ∧ D.matrix x ≤ hi ∧
      hilbertSchmidt (D.matrix x-lo) ≤ dist ∧ hilbertSchmidt (hi-D.matrix x) ≤ dist)
    (cap : ∀ x ∈ closedBall c R, lo.trace.re ≤ 2*r ∧ N.charge x ≤ 2*r)
    (osc : ∀ x ∈ closedBall c R, ‖φ.grad x-t.wavevector‖ ≤ v) (he : 0 < ε) (hle : ε ≤ 1)
    (hd : 0 ≤ dist) (hE : exteriorFormConstant F.oneBody ≤ C) (hI : F.oneBody.interiorConstant ≤ C) :
    ∃ A : CoulombTileReplacement μ islandFairCoin N φ t lo hi ε dist C F.oneBody.loCoeff,
      A.aligned = D ∧ sqrtKinetic A.upper.gradients.background ≤ affineSpiralKinetic t S treg.grad 1 (2*r) ∧
      A.lower.cost ≤ frozenAdditionCost t S treg.grad ε C dist r ∧
      A.upper.cost ≤ frozenAdditionCost t S treg.grad ε C dist r ∧
      A.gauge.forwardCost = W ∧ A.gauge.inverseCost = W ∧
      A.phaseGauge.forwardCost = v^2/4*(∫ x, t.shape x*N.charge x) ∧
      A.phaseGauge.inverseCost = v^2/4*(∫ x, t.shape x*N.charge x) := by
  have field : ∃ U : MatrixGradient, SqrtRegular D U ∧ (∀ᵐ x, kineticDensity U x ≤ kineticDensity S x) ∧
      Continuous D.matrix ∧ D.charge = N.charge := by
    cases axes with
    | unchanged => exact ⟨S,reg,ae_of_all _ fun _ => le_rfl,cont,rfl⟩
    | polarized =>
      obtain ⟨U,u,h⟩ := referenceDensity_sqrt_regular sob reg c
      exact ⟨U,u,h,continuous_referenceDensity c power,funext (referenceDensity_charge N c)⟩
  obtain ⟨U,regU,cmp,continuous,charge⟩ := field
  have cD := fun x hx => (charge ▸ (cap x hx).2 : D.charge x ≤ 2*r)
  obtain ⟨pairs,bgL,bgU,mixL,mixU⟩ := frozen_island_pairs (isCompact_closedBall c R) treg F.fisher chain continuous
    regU reg.grad.integrable_sq cmp pl ph he hle small (fun x hx => ⟨(cap x hx).1,cD x hx⟩)
  let spin := LocalSpinCalculus.of_leibniz leibniz
  obtain ⟨G,hf,hb⟩ := axes_gauge axes F.oneBody spin (F.oneBody.representable pairs.upper_grad.background_regular)
  have mass : Integrable (fun x => t.shape x*N.charge x) := by
    have eq : (t.field D).charge = fun x => t.shape x*N.charge x := funext fun x => by rw [t.field_charge,charge]
    rw [← eq]
    exact pairs.upper_grad.background_regular.charge
  let P := t.phaseGauge N spin F.oneBody chain hφ G.output_rep mass osc
  let A := CoulombTileReplacement.of_poisson F radii N D φ t lo hi pl ph pairs.lower pairs.upper
    pairs.lower_dist pairs.upper_dist pairs.lower_grad pairs.upper_grad pairs.lower_domain pairs.upper_domain G P he hle hE hI
  have hC := F.oneBody.interiorConstant_nonneg.trans hI
  exact ⟨A,rfl,bgU,ordered_cost A.lower treg S he hd hC (fun x hx => (cap x hx).1) pairs.lower_domain bgL mixL,
    ordered_cost A.upper treg S he hd hC cD pairs.upper_domain bgU mixU,hf,hb,rfl,rfl⟩

end TSGA.ManyBody
