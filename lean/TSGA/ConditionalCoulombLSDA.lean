import TSGA.CoulombLocalToGlobal
import TSGA.ConditionalUEG
import TSGA.ConditionalSmallTile

/-! # The conditional LSDA improvement at full polarization -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization PhaseLocalization SSW Metric
open scoped ComplexOrder

/-- Under the linear endpoint conjecture the matrix Lipschitz
estimate extends to full polarization and the better LSDA exponent applies to
all spin densities. The endpoint constant is fixed before the LSDA parameters. -/
theorem CoulombModelInputs.lsda_of_endpoint {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}
    (P : CoulombModelInputs μ ι η) {E : ℝ} (hE : 0 ≤ E) (endpoint : UEGEndpointBound η E) :
    (∃ J > 0, ∀ A B : SpinMatrix, A.PosSemidef → B.PosSemidef →
      let r := max A.trace.re B.trace.re
      |uniformEnergy energy η A - uniformEnergy energy η B| ≤
        J*(r^(1/3:ℝ)+r^(2/3:ℝ))*hilbertSchmidt (A-B)) ∧
    ∀ p θ : ℝ, 3 < p → 2/p ≤ θ → θ < 1 → ∃ C > 0,
      LSDAEstimate (referenceEnergies energy η) (fun _ => True) p θ (polarizedBulkExponent p θ) C := by
  obtain ⟨K,⟨L⟩⟩ := P.gas.2
  obtain ⟨J,hJ,lip⟩ := L.ueg_lipschitz_of_endpoint P.fock.oneBody P.difference endpoint hE
  refine ⟨⟨J,hJ,?_⟩,?_⟩
  · intro A B hA hB
    simpa only [sswEnergy_zero_wavevector] using lip A B hA hB
  intro p θ hp hlo hhi
  have hp₀ : 0 < p := by linarith
  have hθ : 0 < θ := (div_pos (by norm_num : (0:ℝ)<2) hp₀).trans_le hlo
  have hpθ : 2 ≤ p*θ := by simpa only [mul_comm θ p] using (div_le_iff₀ hp₀).mp hlo
  obtain ⟨C,hC,M⟩ := P.matrixMorrey p hp
  obtain ⟨V,hV,vec⟩ := P.vectorMorrey p hp
  obtain ⟨a,ha,area⟩ := tileCutoffAreaBound_of_sobolev P.difference P.directional.toDifferenceBounds η
  obtain ⟨A,hA,small⟩ := actual_small_oscillation_of_zero_phase_lipschitz L P.fock ((subset_tsupport _).trans P.support)
    P.poisson P.poisson_nonneg P.leibniz P.phaseProduct P.product (levyLiebBorel_of_lowerSemicontinuous P.lowerSemicontinuity)
    P.composition P.window P.orientations P.frames P.difference P.directional.toDifferenceBounds P.ballComposition
    ha area M vec hC hV hp hθ hhi.le hpθ J hJ lip
  have localBound : SmallBallBoundFor P.orientations P.frames η .minority 0 p θ C K A
      (fun φ G => φ=Phase.zero ∧ G=0) := by
    intro D φ S T G reg _ _ allowed ε he hle had side profile tiles F cut c test
    obtain ⟨rfl,rfl⟩ := allowed
    exact small reg he hle had side profile cut c test
  obtain ⟨B,hB,τ,hτ,allCenters⟩ := P.integrate_balls L .minority hp hθ hpθ M hC ha area hA localBound
  obtain ⟨A₀,hA₀,rough⟩ := L.aPriori P.fock.oneBody P.phaseProduct P.difference
  apply lsda_of_unrestricted_small_scale rough hA₀ hp hθ hB hτ
  intro D S T reg
  have hr : RegimeHyp .minority 0 D 0 p := ae_of_all _ fun x => by
    simpa only [zero_mul,Complex.ofReal_zero,zero_smul,sub_zero] using D.positive x
  exact allCenters D Phase.zero S T 0 reg (phaseAdmissible_zero D hp₀ 0) hr ⟨rfl,rfl⟩

end TSGA.ManyBody
