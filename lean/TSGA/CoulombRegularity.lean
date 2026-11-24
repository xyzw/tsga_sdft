import TSGA.CoulombGas
import TSGA.GasScaling
import TSGA.RayRegularity

/-! # Matrix regularity of the Coulomb SSW gas

The fixed-charge interpolation, wavevector estimate and coordinate scaling
use the same physical energy. Representability of the spiral cutoffs for
scaling follows from the finite-spin hypotheses of the thermodynamic theorem.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory SSW TSGA.Localization
open scoped ComplexOrder

/-- Proposition E.2(iv) for the Coulomb gas, with a universal numerator in
the Lipschitz constant. The trace of either matrix may be zero. -/
theorem coulomb_minority_lipschitz {η : Mollifier} {K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3 : ℝ)) ≤ indirectAt D.matrix Γ)
    {ν : ℝ} (hν : 0 < ν) (hν' : ν ≤ 1/2) (q : Position)
    {M N : SpinMatrix} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (mM : (M - ((ν*M.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef)
    (mN : (N - ((ν*N.trace.re : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef) :
    let r := max M.trace.re N.trace.re
    |sswEnergy energy η M q - sswEnergy energy η N q| ≤
      (4*cLO + 22*K + 4)/ν * (r^(1/3:ℝ) + r^(2/3:ℝ) + ‖q‖^2) * hilbertSchmidt (M-N) := by
  let gas := coulomb_sswGas η loc states
  apply gas.matrix_lipschitz rate hc q (fun _ hr => coulomb_ssw_convex_fixed_charge η loc states hr q)
    _ hν hν' hM hN mM mN
  intro P hP α hα hα'
  exact ssw_scaling gas hc lo P hP q (fun n => SpiralKinematics.representable states P hP n q) hα hα'

end TSGA.ManyBody
