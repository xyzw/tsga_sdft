import TSGA.AlignmentGaugeComparison
import TSGA.ConstantWavevectorRotation
import TSGA.IslandTrialAssembly

/-! # The two local rotation costs in the signed Coulomb replacement -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization
open scoped ComplexOrder MatrixOrder

/-- The two branches of the comparison-matrix construction. The last index
is the kinetic cost of aligning the spin axes before Young's inequality. -/
inductive TileAxisChoice {c : Position} {R : ℝ} (t : SpiralTaper (Metric.closedBall c R))
    (M : Density) : Density → ℝ → Prop where
  | unchanged : TileAxisChoice t M M 0
  | polarized {r a ω : ℝ} {S : MatrixGradient} (radius : 0 < R) (hr : 0 < r)
      (sob : SobolevCompositionOn (Metric.closedBall c R)) (cap : ∀ x ∈ Metric.closedBall c R, M.charge x ≤ r)
      (peak : ∃ z ∈ Metric.closedBall c R, M.charge z = r)
      (minor : ∃ y ∈ Metric.closedBall c R, ∃ i : Fin 2, (M.positive y).1.eigenvalues i ≤ r/8)
      (small : ∀ x ∈ Metric.closedBall c R, ∀ y ∈ Metric.closedBall c R, hilbertSchmidt (M.matrix x-M.matrix y) ≤ r/64)
      (ha : 0 < a) (ha' : a ≤ 1)
      (osc : ∀ x ∈ Metric.closedBall c R, hilbertSchmidt (M.power a x-M.power a c) ≤ ω)
      (weak : IsMatrixGradientOn (Metric.closedBall c R) (M.power (1/2)) S)
      (charge : AEMeasurable M.charge volume) (shape : Integrable t.shape)
      (root : AEMeasurable (kineticDensity S) volume) (kin : Integrable fun x => t.shape x*kineticDensity S x) :
      TileAxisChoice t M (referenceDensity M c) (alignmentCost t S r ((96/a)*(ω/r^a)))

variable {c : Position} {R : ℝ} {t : SpiralTaper (Metric.closedBall c R)} {M aligned : Density} {W : ℝ}

private theorem TileAxisChoice.comparison (axes : TileAxisChoice t M aligned W) (F : FiniteEnergyInputs)
    (spin : LocalSpinCalculus) (rep : ∃ Γ, feasible (t.field aligned).matrix Γ) :
    ∃ G : GaugeComparison (t.field aligned) (t.field M) F.loCoeff, G.forwardCost = W ∧ G.inverseCost = W := by
  cases axes with
  | unchanged => exact ⟨GaugeComparison.identity F _ rep,rfl,rfl⟩
  | polarized radius hr sob cap peak minor small ha ha' osc weak charge shape root kin =>
    obtain ⟨G,hf,hb⟩ := gapped_alignmentGauge radius hr t F spin sob cap peak minor small ha ha' osc
      weak charge shape root kin rep
    exact ⟨G,hf,hb.trans hf⟩

/-- The ordered matrix data and analytic domains needed for the Poisson
island trials. Both their energies and the local rotation errors are derived. -/
structure TileIslandPairs {K : Set Position} (t : SpiralTaper K) (aligned : Density)
    (lo hi : SpinMatrix) (ε η : ℝ) where
  low_pos : lo.PosSemidef
  high_pos : hi.PosSemidef
  lower : ∀ x ∈ K, (constantSpinDensity lo low_pos).matrix x ≤ aligned.matrix x
  upper : ∀ x ∈ K, aligned.matrix x ≤ (constantSpinDensity hi high_pos).matrix x
  lower_dist : ∀ x ∈ K, hilbertSchmidt (aligned.matrix x-(constantSpinDensity lo low_pos).matrix x) ≤ η
  upper_dist : ∀ x ∈ K, hilbertSchmidt ((constantSpinDensity hi high_pos).matrix x-aligned.matrix x) ≤ η
  lower_grad : IslandGradients (t.field (constantSpinDensity lo low_pos)) (t.residual (constantSpinDensity lo low_pos) aligned lower) ε
  upper_grad : IslandGradients (t.field aligned) (t.residual aligned (constantSpinDensity hi high_pos) upper) ε
  lower_domain : IslandDensityDomain (t.field (constantSpinDensity lo low_pos)) (t.residual (constantSpinDensity lo low_pos) aligned lower)
  upper_domain : IslandDensityDomain (t.field aligned) (t.residual aligned (constantSpinDensity hi high_pos) upper)

/-- Build the signed comparison for the physical phase using the same
Poisson geometry for both density additions. The coefficients of the rotation
errors are exhibited for both signs of the comparison. -/
theorem coulomb_tile_replacement_from_rotations {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {ε η C : ℝ}
    {lo hi : SpinMatrix} {φ : Phase} {p ω : ℝ} (F : IslandFockInputs μ)
    (radii : CoulombIslandRadii μ ι ε C) (leibniz : LocalSectorLeibniz) (chain : WeakPhaseProduct)
    (axes : TileAxisChoice t M aligned W) (pairs : TileIslandPairs t aligned lo hi ε η) (hφ : φ.Regular p)
    (osc : ∀ x ∈ Metric.closedBall c R, ‖φ.grad x-t.wavevector‖ ≤ ω) (he : 0 < ε) (he' : ε ≤ 1)
    (hη : 0 ≤ η) (hE : exteriorFormConstant F.oneBody ≤ C) (hI : F.oneBody.interiorConstant ≤ C) :
    ∃ D : CoulombTileReplacement μ islandFairCoin M φ t lo hi ε η C F.oneBody.loCoeff,
      D.gauge.forwardCost = W ∧ D.gauge.inverseCost = W ∧
      D.phaseGauge.forwardCost = ω^2/4*(∫ x, t.shape x*M.charge x) ∧
      D.phaseGauge.inverseCost = ω^2/4*(∫ x, t.shape x*M.charge x) ∧
      ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        σ*energy (t.phaseField M φ).matrix ≤ σ*energy (SSW.cutoffSpiral t.shape
          (if σ = 1 then lo else hi) t.wavevector) + D.error σ := by
  let spin := LocalSpinCalculus.of_leibniz leibniz
  let reg := pairs.upper_grad.background_regular
  obtain ⟨G,hf,hb⟩ := axes.comparison F.oneBody spin (F.oneBody.representable reg)
  have eqcharge (x : Position) : (t.field aligned).charge x = t.shape x*M.charge x := by
    rw [← conjugated_charge _ G.U x]
    change ((conjugatedDensity (t.field aligned) G.U).matrix x).trace.re = _
    rw [G.target]
    exact t.field_charge M x
  have mass := reg.charge.congr (ae_of_all _ eqcharge)
  let P := t.phaseGauge M spin F.oneBody chain hφ G.output_rep mass osc
  let D := CoulombTileReplacement.of_poisson F radii M aligned φ t lo hi pairs.low_pos pairs.high_pos
    pairs.lower pairs.upper pairs.lower_dist pairs.upper_dist pairs.lower_grad pairs.upper_grad
    pairs.lower_domain pairs.upper_domain G P he he' hE hI
  exact ⟨D,hf,hb,rfl,rfl,fun _ hσ => D.signed he he' hη (F.oneBody.interiorConstant_nonneg.trans hI) hσ⟩

end TSGA.ManyBody
