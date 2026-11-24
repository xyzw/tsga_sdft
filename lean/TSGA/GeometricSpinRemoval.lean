import TSGA.OrderedCoulombFrame
import TSGA.GeometricSpinTests
import TSGA.SpinMomentumFlatten
import TSGA.CoulombSpinPairEnsemble

/-! # Removal of electrons by spin, Lemma E.1

A bounded-test partial trace is realized in the mixed-state constrained
search. One localized ensemble gives the position and momentum marginals,
the Coulomb-weighted pair matrix and every axial-current direction.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Filter Matrix
open scoped Kronecker MatrixOrder ComplexOrder InnerProductSpace Matrix.Norms.L2Operator Topology

namespace RetainedSectorTests
variable {F : SectorFourierTransform} {s : PureState} {U : SpinSplitter} {d : SectorSpectralResolution}

theorem coulomb_matrix (r : RetainedSectorTests F s U d) : d.toMixedState.coulombPairMatrix =
    (U.active ⊗ₖ U.active) * s.coulombPairMatrix * star (U.active ⊗ₖ U.active) := by
  let L := spinCongruence (U.active ⊗ₖ U.active)
  have he (n : ℕ) : pairProbe (pairCutoffWeight n) d.toMixedState.pairDensitySpin =
      L (pairProbe (pairCutoffWeight n) s.pairDensitySpin) := by
    change _ = (U.active ⊗ₖ U.active) * _ * _
    rw [← r.pair _ (measurable_pairCutoffWeight n) ⟨n,norm_pairCutoffWeight_le n⟩]
    ext i j
    exact (d.toMixedState.pairCutoffWeight_hasSum n i j).tsum_eq.symm
  have hin : Tendsto (fun n => L (pairProbe (pairCutoffWeight n) s.pairDensitySpin)) atTop
      (𝓝 (L s.coulombPairMatrix)) := (L.continuous.tendsto _).comp s.coulombPairMatrix_tendsto
  have hout := d.toMixedState.coulombPairMatrix_tendsto
  have hlim := hin.congr (fun n => (he n).symm)
  ext i j
  exact tendsto_nhds_unique (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hout i) j)
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j)

private theorem kinetic_matrix (r : RetainedSectorTests F s U d) (pl : SectorPlancherelMoments F) :
    momentumKinetic (mixedSpinMomentumProfile d.toMixedState F.profile) =
    U.active * momentumKinetic (F.profile s) * star U.active := by
  let L := spinCongruence U.active
  change (∫ p, ‖p‖^2 • mixedSpinMomentumProfile d.toMixedState F.profile p) = L (∫ p, ‖p‖^2 • F.profile s p)
  rw [← L.integral_comp_comm (pl.pure s).second_integrable]
  apply integral_congr_ae
  filter_upwards [r.momentum_density pl] with p hp
  rw [map_smul,hp]
  rfl

theorem kinetic_le (r : RetainedSectorTests F s U d) (pl : SectorPlancherelMoments F)
    (h : star U.active * U.active ≤ 1) : d.toMixedState.kinetic ≤ s.kinetic := by
  have hk : (momentumKinetic (F.profile s)).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply integral_nonneg_of_ae
    exact (pl.pure s).positive.mono fun p hp => smul_nonneg (sq_nonneg ‖p‖) hp.nonneg
  rw [← (d.toMixedState.spinMomentumDistribution F.profile pl.pure).kinetic, ← (pl.pure s).kinetic]
  change (momentumKinetic (mixedSpinMomentumProfile d.toMixedState F.profile)).trace.re ≤ _
  rw [r.kinetic_matrix pl,Matrix.trace_mul_cycle]
  exact contraction_trace_le h hk

end RetainedSectorTests

private theorem pair_energy {Λ : MixedState} {S : SpinMatrix} {W : PairSpinMatrix}
    (hW : Λ.coulombPairMatrix = (S ⊗ₖ S) * W * star (S ⊗ₖ S)) :
    Λ.interaction = (((star S * S) ⊗ₖ (star S * S)) * W).trace.re := by
  rw [← Λ.trace_coulombPairMatrix,hW,Matrix.trace_mul_cycle]
  have h : star (S ⊗ₖ S) * (S ⊗ₖ S) = (star S * S) ⊗ₖ (star S * S) := by
    change (S ⊗ₖ S).conjTranspose * (S ⊗ₖ S) = _
    rw [Matrix.conjTranspose_kronecker,Matrix.mul_kronecker_mul]
    rfl
  rw [h]

/-- Realization of the reduced densities on the full countable ensemble.
All equalities hold for one output state, including for singular S. -/
theorem geometric_spin_marginals {F : SectorFourierTransform} (pl : SectorPlancherelMoments F)
    (geo : FiniteSectorGeometricLocalization F) (Γ : MixedState) (S : SpinMatrix) (hS : star S * S ≤ 1) :
    ∃ Λ : MixedState, feasible (fun x => S * Γ.matrixDensity x * star S) Λ ∧
      mixedSpinMomentumProfile Λ F.profile =ᵐ[volume] (fun p => S * mixedSpinMomentumProfile Γ F.profile p * star S) ∧
      Λ.coulombPairMatrix = (S ⊗ₖ S) * Γ.coulombPairMatrix * star (S ⊗ₖ S) := by
  choose d hd using fun k => geo (Γ.component k) (spinDilation S) (spinDilation_isometry hS)
  let states := fun k => (d k).toMixedState
  have hV (k) : (states k).interaction ≤ (Γ.component k).interaction := by
    have e := pair_energy ((hd k).coulomb_matrix)
    rw [e, ← (Γ.component k).trace_coulombPairMatrix]
    exact contraction_trace_le (contraction_pair_le_one (star_mul_self_nonneg S).posSemidef hS)
      (Γ.component k).coulombPairMatrix_posSemidef
  obtain ⟨hN,hT,hW⟩ := Γ.summable_localized_moments states (fun k => (hd k).particleMean_le)
    (fun k => (hd k).kinetic_le pl hS) hV
  refine ⟨Γ.flatten states hN hT hW,mixedPosition_flatten_localized Γ states hN hT hW S (fun k => (hd k).density pl),
    mixedSpinMomentumProfile_flatten_localized Γ states hN hT hW F.profile pl.pure S (fun k => (hd k).momentum_density pl),?_⟩
  let L := spinCongruence (S ⊗ₖ S)
  have hmap := Γ.coulombPairMatrix_hasSum.mapL L
  apply (Γ.coulombPairMatrix_flatten states hN hT hW).unique
  apply hmap.congr_fun
  intro k
  rw [map_smul, (hd k).coulomb_matrix]
  rfl

/-- Exact localized kinetic, Coulomb and axial-current identities. The
witness depends on Γ and S and works simultaneously for every q. -/
theorem geometric_spin_removal {F : SectorFourierTransform} (pl : SectorPlancherelMoments F)
    (geo : FiniteSectorGeometricLocalization F) (Γ : MixedState) (S : SpinMatrix) (hS : star S * S ≤ 1) :
    let D := Γ.spinMomentumDistribution F.profile pl.pure
    ∃ Λ : MixedState, feasible (fun x => S * Γ.matrixDensity x * star S) Λ ∧
      Λ.kinetic = ((star S * S) * momentumKinetic D.profile).trace.re ∧
      Λ.interaction = (((star S * S) ⊗ₖ (star S * S)) * Γ.coulombPairMatrix).trace.re ∧
      ∀ q : Position, ⟪q,Λ.axialCurrent⟫_ℝ = D.form q S S := by
  intro D
  obtain ⟨Λ,hd,hp,hW⟩ := geometric_spin_marginals pl geo Γ S hS
  let E := Λ.spinMomentumDistribution F.profile pl.pure
  exact ⟨Λ,hd,D.kinetic_localize E S hp,pair_energy hW,D.current_localize E S hp⟩

theorem geometric_fockSpinCurrentTraces {F : SectorFourierTransform} (pl : SectorPlancherelMoments F)
    (geo : FiniteSectorGeometricLocalization F) : FockSpinCurrentTraces := by
  intro Γ q
  let D := Γ.spinMomentumDistribution F.profile pl.pure
  refine ⟨⟨momentumKinetic D.profile,Γ.coulombPairMatrix,D.kinetic_pos,Γ.coulombPairMatrix_posSemidef,
    D.kinetic,Γ.trace_coulombPairMatrix,D.form q,D.form_symm q,D.axial_identity q,D.gram q,?_⟩⟩
  intro S hS
  obtain ⟨Λ,hd,hk,hw,hj⟩ := geometric_spin_removal pl geo Γ S hS
  exact ⟨Λ,hd,hk,hw,hj q⟩

/-- Lemma E.1 for the concrete grand-canonical constrained search. -/
theorem levyLieb_spin_removal_of_geometric_localization {F : SectorFourierTransform}
    (pl : SectorPlancherelMoments F) (geo : FiniteSectorGeometricLocalization F)
    {M : Position → SpinMatrix} (rep : ∃ Γ, feasible M Γ) (S : SpinMatrix) (hS : star S * S ≤ 1) :
    levyLieb (fun x => S * M x * star S) ≤ levyLieb M :=
  levyLieb_spin_removal (geometric_fockSpinCurrentTraces pl geo).toFockSpinLocalization rep S hS

theorem energy_ordered_cutoff_of_geometric_localization {F : SectorFourierTransform}
    (pl : SectorPlancherelMoments F) (geo : FiniteSectorGeometricLocalization F)
    {A B : SpinMatrix} (hA : A.PosSemidef) (hAB : A ≤ B) (f : Position → ℝ)
    (rep : ∃ Γ, feasible (fun x => f x • B) Γ) :
    energy (fun x => f x • A) ≤ energy (fun x => f x • B) + (B.trace.re^2 - A.trace.re^2) * hartree f :=
  energy_ordered_cutoff (geometric_fockSpinCurrentTraces pl geo).toFockSpinLocalization hA hAB f rep

end TSGA.ManyBody
