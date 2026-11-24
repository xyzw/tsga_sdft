import TSGA.LayerGradient
import TSGA.HoffmannOstenhof
import TSGA.DensityMeasurability
import TSGA.MatrixChainRule
import TSGA.AxialKinetic
import TSGA.SSWGas
import TSGA.SSWRate
import TSGA.TSGATheorem

/-! # The TSGA for the grand-canonical constrained-search energy

The rotated energy and the finite energies defining the SSW gas come from
the same Coulomb functional. The whole-space a priori estimate is obtained
from one-body trials, the indirect-energy bound and the rotation formula.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory TSGA.Localization SSW
open scoped ComplexOrder

/-- Inputs of the finite-system energy bounds. The constants refer to the
one-body trial and the indirect Coulomb energy, before the constrained search. -/
structure FiniteEnergyInputs where
  cTF : ℝ
  κ₁ : ℝ
  κ₂ : ℝ
  loCoeff : ℝ
  cTF_nonneg : 0 ≤ cTF
  κ₁_nonneg : 0 ≤ κ₁
  κ₂_nonneg : 0 ≤ κ₂
  lo_nonneg : 0 ≤ loCoeff
  construction : LayerConstruction cTF κ₁ κ₂
  layer_sobolev : FamilySobolevComposition
  quasiFree : QuasiFreeRealization
  liebOxford : ∀ D : Density, ∀ Γ : MixedState, feasible D.matrix Γ →
    hartree D.charge - loCoeff * chargeMoment D (4/3) ≤ Γ.interaction

theorem FiniteEnergyInputs.trials (H : FiniteEnergyInputs) : LayerTrials H.cTF H.κ₁ H.κ₂ :=
  H.construction.trials H.layer_sobolev

/-- A positive density with finite charge and square-root kinetic energy is
represented by a grand-canonical Coulomb state. -/
theorem FiniteEnergyInputs.representable (H : FiniteEnergyInputs) {D : Density}
    {S : MatrixGradient} (hD : SqrtRegular D S) : ∃ Γ, feasible D.matrix Γ := by
  obtain ⟨w, _, _⟩ := H.construction D S hD 1 zero_lt_one
  obtain ⟨Γ, hΓ, _, _⟩ := H.quasiFree w.gamma
  exact ⟨Γ, hΓ.trans w.density⟩

/-- The lower Coulomb bound with the matrix gradient coefficient one half.
Lieb–Thirring is used for the one-body marginal and Lieb–Oxford for each
trial ensemble before taking the infimum. -/
theorem FiniteEnergyInputs.lower_bound (H : FiniteEnergyInputs) {cLT : ℝ}
    (ltBound : ∀ (γ : OneBody) (D : Density), γ.matrixDensity =ᵐ[volume] D.matrix →
      cLT * chargeMoment D (5/3) ≤ γ.kinetic)
    (chain : RankOneRootChain) (convex : CountableFisherConvexity) (marg : OneBodyMarginals)
    {D : Density} {S : MatrixGradient} (hD : SqrtRegular D S) :
    max (cLT * chargeMoment D (5/3)) (sqrtKinetic S / 2) - H.loCoeff * chargeMoment D (4/3) ≤
      energy D.matrix := by
  apply lower_energy (ltCoeff := cLT) (loCoeff := H.loCoeff) _ hD (H.representable hD)
  refine ⟨H.liebOxford, ?_, hoffmann_ostenhof_state chain convex marg⟩
  intro A Γ hΓ
  obtain ⟨γ, hρ, hk⟩ := marg.marginal Γ
  exact (ltBound γ A (hρ.trans hΓ)).trans_eq hk

private theorem rpow_le_mass {r a : ℝ} (hr : 0 ≤ r) (ha : a ∈ Set.Icc 1 2) : r ^ a ≤ r + r^2 := by
  rcases hr.eq_or_lt with hr | hr
  · simp [← hr, Real.zero_rpow (show a ≠ 0 by linarith [ha.1])]
  · exact BulkRegime.density_power_le hr ha

/-- A uniform constant for the absolute energy of a density under a local
axial rotation. The proof only uses the finite kinetic energy of the phase. -/
theorem FiniteEnergyInputs.rotated_bound (H : FiniteEnergyInputs) (chain : WeakPhaseProduct) :
    ∃ B ≥ 0, ∀ {D : Density} {φ : Phase} {p θ : ℝ} {S T : MatrixGradient},
      DensityRegular D p θ S T → φ.Regular p → Integrable (fun x => D.charge x * ‖φ.grad x‖^2) →
      |energy (fun x => rotate (φ.value x) (D.matrix x))| ≤
        B * ((∫ x, massDensity D φ x) + sqrtKinetic S) := by
  let A := H.cTF * (1 + H.κ₁)
  let J := 8 * (1 + H.κ₂)
  have hA : 0 ≤ A := mul_nonneg H.cTF_nonneg (by linarith [H.κ₁_nonneg])
  have hJ : 0 ≤ J := by dsimp [J]; linarith [H.κ₂_nonneg]
  refine ⟨H.loCoeff + A + 2 * J, by linarith [H.lo_nonneg], ?_⟩
  intro D φ p θ S T hD hφ hkin
  let R := rotatedDensity D φ
  have hc (x : Position) : R.charge x = D.charge x := rotated_charge D φ x
  have hs : Integrable (fun x => D.charge x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hD.charge_L2.integrable_norm_pow (p := 2) (by decide)
  have hmass : Integrable (massDensity D φ) := (hD.charge_L1.add hs).add hkin
  let M := ∫ x, massDensity D φ x
  let P := ∫ x, D.charge x * ‖φ.grad x‖ ^ 2
  have hM : 0 ≤ M := integral_nonneg (massDensity_nonneg D φ)
  have hS : 0 ≤ sqrtKinetic S := integral_nonneg fun x => sq_nonneg _
  have hP : P ≤ M := integral_mono hkin hmass fun x => by
    unfold massDensity
    linarith [D.charge_nonneg x, sq_nonneg (D.charge x)]
  have hpw (x : Position) (a : ℝ) (ha : a ∈ Set.Icc 1 2) : R.charge x ^ a ≤ massDensity D φ x := by
    rw [hc]
    exact (rpow_le_mass (D.charge_nonneg x) ha).trans
      (le_add_of_nonneg_right (mul_nonneg (D.charge_nonneg x) (sq_nonneg _)))
  have h43 : chargeMoment R (4/3) ≤ M := integral_mono_of_nonneg
    (ae_of_all _ fun x => Real.rpow_nonneg (R.charge_nonneg x) _) hmass
    (ae_of_all _ fun x => hpw x _ (by constructor <;> norm_num))
  have h53 : traceMoment R (5/3) ≤ M := integral_mono_of_nonneg
    (ae_of_all _ fun x => tracePower_nonneg R x _) hmass (ae_of_all _ fun x =>
      (tracePower_le_charge R x (by norm_num)).trans (hpw x _ (by constructor <;> norm_num)))
  obtain ⟨Z, hw, hZ, hcost⟩ := rotated_sqrt_kinetic chain hD hφ hkin
  have hr : SqrtRegular R Z := ⟨by simpa only [show R.charge = D.charge from funext hc] using hD.charge_L1, hw, hZ⟩
  have hu := kinetic_and_energy_upper H.cTF_nonneg H.trials H.quasiFree hr (ε := 1) zero_lt_one
  have hup := hu.1.trans hu.2
  norm_num only [Real.sqrt_one, mul_one, div_one] at hup
  have huz : energy R.matrix ≤ A * traceMoment R (5/3) + J * sqrtKinetic Z := by
    apply hup.trans_eq
    dsimp [A, J]
    ring
  have hlow : hartree R.charge - H.loCoeff * chargeMoment R (4/3) ≤ levyLieb R.matrix :=
    le_levyLieb (H.representable hr) fun s hs => (H.liebOxford R s hs).trans
      (le_add_of_nonneg_left s.kinetic_nonneg)
  change sqrtKinetic Z ≤ 2 * sqrtKinetic S + 2 * P at hcost
  change |energy R.matrix| ≤ (H.loCoeff + A + 2 * J) * (M + sqrtKinetic S)
  refine abs_le.mpr ⟨?_, ?_⟩
  · change _ ≤ levyLieb R.matrix - hartree R.charge
    nlinarith only [hlow, mul_le_mul_of_nonneg_left h43 H.lo_nonneg,
      mul_nonneg H.lo_nonneg hS, mul_nonneg hA (add_nonneg hM hS), mul_nonneg hJ (add_nonneg hM hS)]
  · nlinarith only [huz, mul_le_mul_of_nonneg_left h53 hA, mul_le_mul_of_nonneg_left hcost hJ,
      mul_le_mul_of_nonneg_left hP hJ, mul_nonneg hA hS, mul_nonneg H.lo_nonneg (add_nonneg hM hS)]

/-- Borel dependence of a single finite tetrahedron at each integer length.
This condition involves no thermodynamic reference energy. -/
def FiniteTileMeasurable (η : Mollifier) : Prop := ∀ n : ℕ,
  Measurable (fun z : SpinMatrix × Position => tileEnergy energy η z.1 (n : ℝ) 1 z.2)

theorem FiniteTileMeasurable.averaged {η : Mollifier} (h : FiniteTileMeasurable η) (n : ℕ) :
    Measurable (fun z : SpinMatrix × Position => averagedTile energy η z.1 z.2 (n : ℝ) 1) := by
  let Ω := Metric.sphere (0 : Position) 1
  have hm : Measurable (fun z : (SpinMatrix × Position) × Ω =>
      (z.1.1, ‖z.1.2‖ • (z.2 : Position))) := by fun_prop
  have hi := ((h n).comp hm).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure Position).toSphere)
  simp only [averagedTile, directionAverage, average_eq, smul_eq_mul]
  exact measurable_const.mul hi.measurable

theorem physical_aPriori_of_local_measurable {η : Mollifier} {K : ℝ} (H : FiniteEnergyInputs)
    (chain : WeakPhaseProduct) (rate : FiniteRateTiling energy η K)
    (meas : ∀ {D : Density} {φ : Phase} {p θ : ℝ} {S T : MatrixGradient},
      3 < p → 0 < θ → DensityRegular D p θ S T → φ.Regular p →
      AEStronglyMeasurable (localEnergy (referenceEnergies energy η) D φ) volume) :
    ∃ A ≥ 0, APriori (referenceEnergies energy η) A := by
  obtain ⟨a, ha, hgas⟩ := rate.gas_growth
  obtain ⟨b, hb, henergy⟩ := H.rotated_bound chain
  refine ⟨max a b, ha.trans (le_max_left _ _), ?_⟩
  constructor
  · intro M hM q
    have hr : 0 ≤ M.trace.re := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
    exact (hgas M hM q).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact meas
  · intro D φ p θ S T G _ _ hD hφ
    exact (henergy hD hφ.regular hφ.kinetic).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg (integral_nonneg (massDensity_nonneg D φ)) (integral_nonneg fun _ => sq_nonneg _)))

theorem physical_aPriori {η : Mollifier} {K : ℝ} (H : FiniteEnergyInputs) (chain : WeakPhaseProduct)
    (rate : FiniteRateTiling energy η K) (meas : FiniteTileMeasurable η)
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q) :
    ∃ A ≥ 0, APriori (referenceEnergies energy η) A := by
  apply physical_aPriori_of_local_measurable H chain rate
  intro D φ p θ S T _ _ hD hφ
  apply local_ssw_aestronglyMeasurable energy_vacuum loc
  intro n
  exact ((meas.averaged n).comp_aemeasurable
      (hD.aemeasurable_matrix.prodMk hφ.continuous_grad.aemeasurable)).aestronglyMeasurable

/-- The extended form of Theorem 3.3 with the Coulomb Levy–Lieb functional
and its own thermodynamic reference energies. -/
theorem levyLieb_tsga {η : Mollifier} {K : ℝ} (H : FiniteEnergyInputs) (chain : WeakPhaseProduct)
    (sobolev : SobolevLipschitzComposition) (rate : FiniteRateTiling energy η K)
    (meas : FiniteTileMeasurable η) (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re →
      ∀ q : Position, FiniteLocalization energy η M q) (tiles : TSGALocalization (referenceEnergies energy η)) :
    MainExtendedTSGAEstimate (referenceEnergies energy η) := by
  obtain ⟨A, hA, rough⟩ := physical_aPriori H chain rate meas loc
  exact tsga_theorem_extended rough hA tiles (weakPowerComparison_of_sobolev sobolev)

end TSGA.ManyBody
