import TSGA.CoulombFixedTraceRoot
import TSGA.RootTraceRegularity

/-! # The matrix-root estimate for the Coulomb spin spiral gas -/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization
open scoped ComplexOrder

/-- Proposition E.2(vi). The constant is uniform in both charges, both
spin directions and the wavevector. A matrix may have a zero eigenvalue. -/
theorem coulomb_ssw_root_lipschitz {η : Mollifier} {J K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3:ℝ)) ≤ indirectAt D.matrix Γ) {p : ℝ} (hp : 3 ≤ p) :
    ∃ C > 0, ∀ {A B : SpinMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef), ∀ q : Position,
      let r := max A.trace.re B.trace.re
      0 < r → |sswEnergy energy η A q - sswEnergy energy η B q| ≤ C*holderGrowth r q *
        (hilbertSchmidt (hA.1.cfc (fun t => t^(1/p:ℝ)) - hB.1.cfc (fun t => t^(1/p:ℝ))) / r^(1/p:ℝ)) := by
  obtain ⟨L, hL, heq⟩ := coulomb_ssw_equal_trace_root loc states rate removal hc lo hp
  let R := 2*(cLO+2*K)+2*(2*K+1)
  have hK := zero_le_one.trans rate.one_le
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hp' : 0 < p := by linarith
  refine ⟨L*(1+4*p)+2*p*R, by positivity, ?_⟩
  intro A B hA hB q r hr
  apply root_lipschitz_of_equal_charge (fun M => sswEnergy energy η M q) q hp hL.le hR (heq q) _ hA hB hr
  intro P hP α ha ha'
  let gas := coulomb_sswGas η loc states
  exact gas.ray_lipschitz rate hc hP q ha ha' (ssw_scaling gas hc lo P hP q
    (fun n => SpiralKinematics.representable states P hP n q) ha ha')

end TSGA.ManyBody
