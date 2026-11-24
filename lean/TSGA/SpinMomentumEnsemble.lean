import TSGA.SpinMomentumDistribution
import TSGA.ParticleNumber
import TSGA.MarginalPositivity
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! # Spin momentum moments of a countable ensemble -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator ENNReal

/-- The spin-resolved position and momentum moments of one normalized wave or the vacuum. -/
structure PureSpinMomentumDistribution (s : PureState) (P : Position → SpinMatrix) : Prop where
  positive : ∀ᵐ p, (P p).PosSemidef
  integrable : Integrable P
  second_integrable : Integrable (fun p => ‖p‖^2 • P p)
  spatial_integrable : Integrable s.matrixDensity
  mass : (∫ p, P p) = ∫ x, s.matrixDensity x
  kinetic : (momentumKinetic P).trace.re = s.kinetic
  current : ∀ q, ⟪q,s.spinMomentum 0 - s.spinMomentum 1⟫_ℝ = momentumAxial q P

def mixedSpinMomentumProfile (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (p : Position) : SpinMatrix := ∑' k, Γ.weight k • P (Γ.component k) p

theorem spin_norm_le_trace {A : SpinMatrix} (h : A.PosSemidef) : ‖A‖ ≤ A.trace.re := by
  let H := h.isHermitian
  have hnorm : ‖A‖ = ‖fun i => (H.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [H.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have ht : A.trace.re = H.eigenvalues 0 + H.eigenvalues 1 := by
    rw [H.trace_eq_sum_eigenvalues, Fin.sum_univ_two, Complex.add_re]
    rfl
  rw [hnorm,ht,pi_norm_le_iff_of_nonneg (add_nonneg (h.eigenvalues_nonneg 0) (h.eigenvalues_nonneg 1))]
  intro i
  simp only [Complex.norm_real, Real.norm_of_nonneg (h.eigenvalues_nonneg i)]
  fin_cases i <;> simp [h.eigenvalues_nonneg]

private theorem spin_norm_integral_le_trace {F : Position → SpinMatrix} (hi : Integrable F)
    (hp : ∀ᵐ x, (F x).PosSemidef) : (∫ x, ‖F x‖) ≤ (∫ x, F x).trace.re := by
  change _ ≤ spinRealTrace (∫ x, F x)
  rw [← spinRealTrace.integral_comp_comm hi]
  exact integral_mono_ae hi.norm (spinRealTrace.integrable_comp hi)
    (hp.mono fun _ hx => spin_norm_le_trace hx)

private theorem pure_spatial_trace (s : PureState) :
    (∫ x, (s.matrixDensity x).trace.re) = (s.particles : ℝ) := by
  cases s with
  | vacuum => simp [PureState.particles,PureState.matrixDensity]
  | occupied ψ => simpa [PureState.matrixDensity, PureState.particles] using ψ.particleNumber.2

namespace PureSpinMomentumDistribution
variable {s : PureState} {P : Position → SpinMatrix} (d : PureSpinMomentumDistribution s P)
include d

private theorem trace_mass : (∫ x, s.matrixDensity x).trace.re = s.particles := by
  change spinRealTrace (∫ x, s.matrixDensity x) = _
  rw [← spinRealTrace.integral_comp_comm d.spatial_integrable]
  exact pure_spatial_trace s

theorem spatial_norm : (∫ x, ‖s.matrixDensity x‖) ≤ s.particles :=
  (spin_norm_integral_le_trace d.spatial_integrable s.matrixDensity_posSemidef).trans_eq d.trace_mass

theorem mass_norm : (∫ p, ‖P p‖) ≤ s.particles := by
  refine (spin_norm_integral_le_trace d.integrable d.positive).trans_eq ?_
  rw [d.mass,d.trace_mass]

theorem kinetic_norm : (∫ p, ‖‖p‖^2 • P p‖) ≤ s.kinetic :=
  (spin_norm_integral_le_trace d.second_integrable
    (d.positive.mono fun p hp => hp.smul (sq_nonneg ‖p‖))).trans_eq d.kinetic

theorem first_norm (q : Position) :
    (∫ p, ‖⟪q,p⟫_ℝ • P p‖) ≤ ‖q‖ * ((s.particles : ℝ) + s.kinetic) := by
  have h := integral_mono ((spinFirst_integrable d.integrable d.second_integrable q).norm)
    ((d.integrable.norm.add d.second_integrable.norm).const_mul ‖q‖) (spinFirst_norm_bound P q)
  calc
    _ ≤ ∫ p, ‖q‖ * (‖P p‖ + ‖‖p‖^2 • P p‖) := h
    _ = ‖q‖ * ((∫ p, ‖P p‖) + ∫ p, ‖‖p‖^2 • P p‖) := by rw [integral_const_mul,integral_add d.integrable.norm d.second_integrable.norm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add d.mass_norm d.kinetic_norm) (norm_nonneg q)

end PureSpinMomentumDistribution

private structure EnsembleSeries (Γ : MixedState) (F : PureState → Position → SpinMatrix) : Prop where
  integrable : ∀ s, Integrable (F s)
  norm_sum : Summable (fun k => ∫ x, ‖Γ.weight k • F (Γ.component k) x‖)

private theorem series_of_bound (Γ : MixedState) (F : PureState → Position → SpinMatrix)
    (I : ∀ s, Integrable (F s)) (b : PureState → ℝ)
    (B : ∀ s, (∫ x, ‖F s x‖) ≤ b s) (hs : Summable fun k => Γ.weight k * b (Γ.component k)) :
    EnsembleSeries Γ F := by
  refine ⟨I,hs.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)⟩
  simp only [norm_smul,Real.norm_of_nonneg (Γ.weight_nonneg k),integral_const_mul]
  exact mul_le_mul_of_nonneg_left (B _) (Γ.weight_nonneg k)

namespace EnsembleSeries
variable {Γ : MixedState} {F : PureState → Position → SpinMatrix} (h : EnsembleSeries Γ F)
include h
private theorem term (k : ℕ) : Integrable fun x => Γ.weight k • F (Γ.component k) x :=
  (h.integrable _).smul (Γ.weight k)

private theorem aeHasSumL1 :
    ∀ᵐ x, HasSum (fun k => Γ.weight k • F (Γ.component k) x)
      ((∑' k, (h.term k).toL1 _) x) := by
  have hfin : ∑' k, ‖(h.term k).toL1 _‖ₑ ≠ ⊤ := by
    simp only [Integrable.enorm_toL1, ← ofReal_integral_norm_eq_lintegral_enorm (h.term _)]
    exact h.norm_sum.tsum_ofReal_ne_top
  have hco : ∀ᵐ x, ∀ k, (h.term k).toL1 _ x = Γ.weight k • F (Γ.component k) x :=
    ae_all_iff.mpr fun k => (h.term k).coeFn_toL1
  filter_upwards [Lp.hasSum_coeFn_tsum hfin,hco] with x hx he
  simpa only [he] using hx

private theorem summable_ae :
    ∀ᵐ x, Summable (fun k => Γ.weight k • F (Γ.component k) x) :=
  h.aeHasSumL1.mono fun _ hx => hx.summable

private theorem integrable_profile : Integrable (mixedSpinMomentumProfile Γ F) :=
  (L1.integrable_coeFn _).congr (h.aeHasSumL1.mono fun _ hx => hx.tsum_eq.symm)

private theorem integrated : HasSum (fun k => Γ.weight k • ∫ x, F (Γ.component k) x)
    (∫ x, mixedSpinMomentumProfile Γ F x) := by
  simpa only [integral_smul,mixedSpinMomentumProfile] using! hasSum_integral_of_summable_integral_norm h.term h.norm_sum

end EnsembleSeries

private theorem spatialProfile (Γ : MixedState) :
    mixedSpinMomentumProfile Γ PureState.matrixDensity =ᵐ[volume] Γ.matrixDensity := by
  filter_upwards [Γ.density_summable] with x hx
  apply HasSum.tsum_eq
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  exact (hx i j).hasSum

private theorem multiplyProfile {Γ : MixedState} {P : PureState → Position → SpinMatrix}
    (d : EnsembleSeries Γ P) (w : Position → ℝ) :
    (fun p => w p • mixedSpinMomentumProfile Γ P p) =ᵐ[volume]
      mixedSpinMomentumProfile Γ (fun s p => w p • P s p) := by
  filter_upwards [d.summable_ae] with p hp
  exact ((hp.hasSum.const_smul (w p)).congr_fun
    (fun k => smul_comm (Γ.weight k) (w p) _)).tsum_eq.symm

private theorem momentumSeries (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) : EnsembleSeries Γ P :=
  series_of_bound Γ P (fun s => (h s).integrable) (fun s => (s.particles : ℝ)) (fun s => (h s).mass_norm) Γ.particles_summable

private theorem spatialSeries (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) : EnsembleSeries Γ PureState.matrixDensity :=
  series_of_bound Γ _ (fun s => (h s).spatial_integrable) (fun s => (s.particles : ℝ)) (fun s => (h s).spatial_norm) Γ.particles_summable

theorem mixedMomentum_summable_ae (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) :
    ∀ᵐ p, Summable (fun k => Γ.weight k • P (Γ.component k) p) :=
  (momentumSeries Γ P h).summable_ae

private theorem hasSum_axial (Γ : MixedState) (q : Position) :
    HasSum (fun k => Γ.weight k * ⟪q,(Γ.component k).spinMomentum 0 -
      (Γ.component k).spinMomentum 1⟫_ℝ) ⟪q,Γ.axialCurrent⟫_ℝ := by
  have ha (a : Fin 2) : HasSum (fun k => Γ.weight k * ⟪q,(Γ.component k).spinMomentum a⟫_ℝ)
      ⟪q,Γ.spinMomentum a⟫_ℝ := by
    have h (j : Fin 3) := (Γ.spinMomentum_summable a j).hasSum.mul_right (q j)
    simpa only [MixedState.spinMomentum_apply,PiLp.inner_apply,Real.inner_apply,Finset.mul_sum,
      mul_assoc,mul_comm (q _)] using hasSum_sum (s := Finset.univ) (fun j _ => h j)
  simpa only [MixedState.axialCurrent,inner_sub_right,mul_sub] using (ha 0).sub (ha 1)

def MixedState.spinMomentumDistribution (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) : SpinMomentumDistribution Γ := by
  let D := momentumSeries Γ P h
  let X := spatialSeries Γ P h
  have K : EnsembleSeries Γ (fun s p => ‖p‖^2 • P s p) :=
    series_of_bound Γ _ (fun s => (h s).second_integrable) PureState.kinetic (fun s => (h s).kinetic_norm) Γ.kinetic_summable
  have hK := multiplyProfile D (fun p => ‖p‖^2)
  refine ⟨mixedSpinMomentumProfile Γ P, ?_, D.integrable_profile, K.integrable_profile.congr hK.symm,
    X.integrable_profile.congr (spatialProfile Γ), ?_, ?_, ?_⟩
  · have hp := ae_all_iff.mpr (fun k => (h (Γ.component k)).positive)
    filter_upwards [hp,D.summable_ae] with p hpos hsum
    exact Matrix.nonneg_iff_posSemidef.mp (tsum_nonneg (fun k => smul_nonneg (Γ.weight_nonneg k)
      (hpos k).nonneg))
  · rw [← D.integrated.tsum_eq,← integral_congr_ae (spatialProfile Γ), ← X.integrated.tsum_eq]
    exact tsum_congr fun k => by rw [(h _).mass]
  · change spinRealTrace (∫ p, ‖p‖^2 • mixedSpinMomentumProfile Γ P p) = _
    rw [integral_congr_ae hK]
    apply HasSum.unique (K.integrated.mapL spinRealTrace)
    simpa only [MixedState.kinetic,map_smul,smul_eq_mul,show ∀ s, spinRealTrace (∫ p, ‖p‖^2 • P s p) = s.kinetic
      from fun s => (h s).kinetic] using Γ.kinetic_summable.hasSum
  · intro q
    have J : EnsembleSeries Γ (fun s p => ⟪q,p⟫_ℝ • P s p) := by
      apply series_of_bound Γ _ (fun s => spinFirst_integrable (h s).integrable (h s).second_integrable q)
        (fun s => ‖q‖ * (s.particles + s.kinetic)) (fun s => (h s).first_norm q)
      simpa only [mul_add,mul_left_comm] using
        (Γ.particles_summable.add Γ.kinetic_summable).mul_left ‖q‖
    change ⟪q,Γ.axialCurrent⟫_ℝ = spinAxialCLM (∫ p, ⟪q,p⟫_ℝ • mixedSpinMomentumProfile Γ P p)
    rw [integral_congr_ae (multiplyProfile D _)]
    apply (hasSum_axial Γ q).unique
    have eqn (s : PureState) : spinAxialCLM (∫ p, ⟪q,p⟫_ℝ • P s p) =
        ⟪q,s.spinMomentum 0-s.spinMomentum 1⟫_ℝ := ((h s).current q).symm
    simpa only [map_smul,smul_eq_mul,eqn] using J.integrated.mapL spinAxialCLM

/-- Real-linear evaluation of one spin-matrix entry. -/
def spinEntry (i j : Fin 2) : SpinMatrix →L[ℝ] ℂ := LinearMap.toContinuousLinearMap {
  toFun := fun A => A i j
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl }

theorem spinEntry_setIntegral_bound (F : Position → SpinMatrix) (h : Integrable F)
    (E : Set Position) (i j : Fin 2) :
    ‖∫ x in E, F x i j‖ ≤ ‖spinEntry i j‖ * ∫ x, ‖F x‖ := by
  change ‖∫ x in E, spinEntry i j (F x)‖ ≤ _
  rw [(spinEntry i j).integral_comp_comm (h.restrict (s := E))]
  exact ((spinEntry i j).le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans
      (setIntegral_le_integral h.norm (ae_of_all _ fun _ => norm_nonneg _))) (norm_nonneg _))

theorem PureSpinMomentumDistribution.momentum_setIntegral_bound {s : PureState} {P : Position → SpinMatrix}
    (d : PureSpinMomentumDistribution s P) (E : Set Position) (i j : Fin 2) :
    ‖∫ p in E, P p i j‖ ≤ ‖spinEntry i j‖ * s.particles :=
  (spinEntry_setIntegral_bound P d.integrable E i j).trans (mul_le_mul_of_nonneg_left d.mass_norm (norm_nonneg _))

theorem PureSpinMomentumDistribution.position_setIntegral_bound {s : PureState} {P : Position → SpinMatrix}
    (d : PureSpinMomentumDistribution s P) (E : Set Position) (i j : Fin 2) :
    ‖∫ x in E, s.matrixDensity x i j‖ ≤ ‖spinEntry i j‖ * s.particles :=
  (spinEntry_setIntegral_bound _ d.spatial_integrable E i j).trans (mul_le_mul_of_nonneg_left d.spatial_norm (norm_nonneg _))

private theorem entry_setIntegral_hasSum {Γ : MixedState} {F : PureState → Position → SpinMatrix}
    (d : EnsembleSeries Γ F) (E : Set Position) (i j : Fin 2) :
    HasSum (fun k => (Γ.weight k : ℂ) * ∫ x in E, F (Γ.component k) x i j)
      (∫ x in E, mixedSpinMomentumProfile Γ F x i j) := by
  let μ := volume.restrict E
  have hs : Summable (fun k => ∫ x, ‖Γ.weight k • F (Γ.component k) x‖ ∂μ) :=
    d.norm_sum.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => setIntegral_le_integral (d.term k).norm (ae_of_all _ fun _ => norm_nonneg _))
  have hv := hasSum_integral_of_summable_integral_norm (fun k => (d.term k).restrict (s := E)) hs
  have ht := hv.mapL (spinEntry i j)
  have hr : Integrable (mixedSpinMomentumProfile Γ F) μ := d.integrable_profile.restrict
  have H := (spinEntry i j).integral_comp_comm hr
  change (∫ x in E, mixedSpinMomentumProfile Γ F x i j) = _ at H
  rw [H]
  apply ht.congr_fun
  intro k
  rw [integral_smul,map_smul,← (spinEntry i j).integral_comp_comm ((d.integrable _).restrict (s := E))]
  rfl

theorem mixedMomentum_setIntegral_hasSum (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) (E : Set Position) (i j : Fin 2) :
    HasSum (fun k => (Γ.weight k : ℂ) * ∫ x in E, P (Γ.component k) x i j)
      (∫ x in E, mixedSpinMomentumProfile Γ P x i j) :=
  entry_setIntegral_hasSum (momentumSeries Γ P h) E i j

theorem mixedPosition_setIntegral_hasSum (Γ : MixedState) (P : PureState → Position → SpinMatrix)
    (h : ∀ s, PureSpinMomentumDistribution s (P s)) (E : Set Position) (i j : Fin 2) :
    HasSum (fun k => (Γ.weight k : ℂ) * ∫ x in E, (Γ.component k).matrixDensity x i j)
      (∫ x in E, Γ.matrixDensity x i j) := by
  have he := (ae_restrict_of_ae (s := E) (spatialProfile Γ)).mono fun x hx =>
    congrArg (fun M : SpinMatrix => M i j) hx
  rw [← integral_congr_ae he]
  exact entry_setIntegral_hasSum (spatialSeries Γ P h) E i j

end TSGA.ManyBody
