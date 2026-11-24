import TSGA.SectorFourierDensity
import TSGA.SectorSpectralResolution
import TSGA.SpinFockIsometry
import TSGA.CoulombSpinPair
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Bounded reduced-density tests for geometric Fock localization

The finite-sector input is the spectral form of geometric localization by
partial trace (Lewin, *Geometric methods for nonlinear many-body quantum
systems*, Proposition 3.1, equation (3.2)). Its tests are bounded one- and two-body multipliers. The
unbounded kinetic, Coulomb and current tests are recovered below.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Filter Matrix
open scoped Kronecker MatrixOrder ComplexOrder InnerProductSpace Matrix.Norms.L2Operator Topology

/-- Expectation of the matrix coefficients of a bounded reduced-density test. -/
def sectorProbe {ι : Type*} (d : SectorSpectralResolution) (A : PureState → Matrix ι ι ℂ) :
    Matrix ι ι ℂ := fun i j => ∑' k, (d.weight k : ℂ) * A (d.component k) i j

/-- The bounded-observable version of the finite-sector geometric
localization theorem. The **same** spectrum realizes all three families of
probes. The retained block of the doubled one-particle spin space is
`U.active`. Both spatial and momentum spectral projections commute with U.
Pair probes act diagonally in position and can resolve all four spin indices.
The occupation bound includes the vacuum and all sectors below the input. -/
structure RetainedSectorTests (F : SectorFourierTransform) (s : PureState) (U : SpinSplitter)
    (d : SectorSpectralResolution) : Prop where
  support : ∀ k, d.weight k ≠ 0 → (d.component k).particles ≤ s.particles
  position_trace : ∀ E, MeasurableSet E → ∀ A : SpinMatrix,
    (A * sectorProbe d (fun t => positionProbe E t.matrixDensity)).trace =
      ((U.conjTranspose * retainedSpinTest A * U) * positionProbe E s.matrixDensity).trace
  momentum_trace : ∀ E, MeasurableSet E → ∀ A : SpinMatrix,
    (A * sectorProbe d (fun t => positionProbe E (F.profile t))).trace =
      ((U.conjTranspose * retainedSpinTest A * U) * positionProbe E (F.profile s)).trace
  pair_trace : ∀ b : PairSpace → ℂ, Measurable b → (∃ C : ℝ, ∀ z, ‖b z‖ ≤ C) → ∀ A : PairSpinMatrix,
    (A * sectorProbe d (fun t => pairProbe b t.pairDensitySpin)).trace =
      (((U ⊗ₖ U).conjTranspose * retainedPairTest A * (U ⊗ₖ U)) * pairProbe b s.pairDensitySpin).trace

def FiniteSectorGeometricLocalization (F : SectorFourierTransform) : Prop :=
  ∀ (s : PureState) (U : SpinSplitter), U.Isometry → ∃ d, RetainedSectorTests F s U d

/-- Conjugation by a fixed spin matrix on one- or two-particle matrices. -/
def spinCongruence {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ := LinearMap.toContinuousLinearMap {
  toFun := fun A => S * A * star S
  map_add' := fun A B => by simp [mul_add,add_mul]
  map_smul' := fun r A => by simp }

private theorem positionProbe_integral {P : Position → SpinMatrix} (h : Integrable P)
    (E : Set Position) : positionProbe E P = ∫ x in E, P x := by
  ext i j
  exact (spinEntry i j).integral_comp_comm h.integrableOn

private theorem ae_of_spinProbes {P Q : Position → SpinMatrix} (hP : Integrable P) (hQ : Integrable Q)
    (S : SpinMatrix) (h : ∀ E, MeasurableSet E → positionProbe E Q = S * positionProbe E P * star S) :
    Q =ᵐ[volume] fun x => S * P x * star S := by
  let L := spinCongruence S
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hQ (L.integrable_comp hP)
  intro E hE _
  rw [← positionProbe_integral hQ, h E hE, positionProbe_integral hP]
  exact (L.integral_comp_comm hP.integrableOn).symm

namespace RetainedSectorTests
variable {F : SectorFourierTransform} {s : PureState} {U : SpinSplitter} {d : SectorSpectralResolution}

private theorem trace_dual {ι : Type*} [Fintype ι] (S X Y : Matrix ι ι ℂ)
    (h : ∀ A, (A * Y).trace = ((star S * A * S) * X).trace) : Y = S * X * star S := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro A
  rw [h]
  calc
    _ = (star S * (A * (S * X))).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem position (r : RetainedSectorTests F s U d) (E : Set Position) (hE : MeasurableSet E) :
    sectorProbe d (fun t => positionProbe E t.matrixDensity) = U.active * positionProbe E s.matrixDensity * star U.active :=
  trace_dual _ _ _ fun A => by simpa only [U.compress_one] using r.position_trace E hE A

theorem momentum (r : RetainedSectorTests F s U d) (E : Set Position) (hE : MeasurableSet E) :
    sectorProbe d (fun t => positionProbe E (F.profile t)) = U.active * positionProbe E (F.profile s) * star U.active :=
  trace_dual _ _ _ fun A => by simpa only [U.compress_one] using r.momentum_trace E hE A

theorem pair (r : RetainedSectorTests F s U d) (b : PairSpace → ℂ) (hb : Measurable b)
    (bound : ∃ C : ℝ, ∀ z, ‖b z‖ ≤ C) : sectorProbe d (fun t => pairProbe b t.pairDensitySpin) =
    (U.active ⊗ₖ U.active) * pairProbe b s.pairDensitySpin * star (U.active ⊗ₖ U.active) :=
  trace_dual _ _ _ fun A => by simpa only [U.compress_two] using r.pair_trace b hb bound A

theorem density (r : RetainedSectorTests F s U d) (pl : SectorPlancherelMoments F) :
    feasible (fun x => U.active * s.matrixDensity x * star U.active) d.toMixedState := by
  apply ae_of_spinProbes (pl.pure s).spatial_integrable (d.toMixedState.spinMomentumDistribution F.profile pl.pure).spatial_integrable
  intro E hE
  rw [← r.position E hE]
  ext i j
  exact (mixedPosition_setIntegral_hasSum d.toMixedState F.profile pl.pure E i j).tsum_eq.symm

theorem momentum_density (r : RetainedSectorTests F s U d) (pl : SectorPlancherelMoments F) :
    mixedSpinMomentumProfile d.toMixedState F.profile =ᵐ[volume] fun p => U.active * F.profile s p * star U.active := by
  apply ae_of_spinProbes (pl.pure s).integrable (d.toMixedState.spinMomentumDistribution F.profile pl.pure).integrable
  intro E hE
  rw [← r.momentum E hE]
  ext i j
  exact (mixedMomentum_setIntegral_hasSum d.toMixedState F.profile pl.pure E i j).tsum_eq.symm

theorem particleMean_le (r : RetainedSectorTests F s U d) : d.toMixedState.particleMean ≤ s.particles := by
  calc
    _ ≤ ∑' k, d.weight k * (s.particles : ℝ) := by
      apply d.particles_summable.tsum_le_tsum _ (d.normalized.summable.mul_right _)
      intro k
      by_cases hk : d.weight k = 0
      · simp [hk]
      · exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (r.support k hk)) (d.weight_nonneg _)
    _ = _ := by rw [tsum_mul_right, d.normalized.tsum_eq,one_mul]

end RetainedSectorTests
end TSGA.ManyBody
