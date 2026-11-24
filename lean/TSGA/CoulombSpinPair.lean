import TSGA.CoulombPairDensity
import TSGA.MarginalPositivity
import TSGA.SpinRemoval
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Spin-resolved Coulomb pair marginal of a Fock ensemble

The factor N(N-1)/2 counts unordered pairs. Contracting both exposed spin
indices and tracing recovers the interaction of the localized ensemble.
-/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Set Matrix Filter
open scoped ComplexOrder ComplexConjugate Kronecker Topology

abbrev PairSpinMatrix := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The pair-spin matrix obtained by testing the two selected positions. -/
def pairProbe (b : PairSpace → ℂ) (W : PairSpace → PairSpinMatrix) : PairSpinMatrix :=
  fun i j => ∫ z, b z * W z i j ∂pairVolume

/-- Each entry of a positive matrix is controlled by its trace. -/
theorem spinEntry_le_trace {ι : Type*} [Fintype ι] {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (i j : ι) : ‖A i j‖ ≤ A.trace.re := by
  classical
  obtain ⟨m,v,rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  rw [Matrix.trace_sum]
  simp only [Matrix.sum_apply, Matrix.trace, Matrix.diag_apply, Complex.re_sum,
    Matrix.vecMulVec_apply,Pi.star_apply,Complex.star_def,Complex.mul_conj,Complex.ofReal_re]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul,Complex.norm_conj]
  have hi := Finset.single_le_sum (s:=Finset.univ) (fun (a : ι) _ => Complex.normSq_nonneg (v k a)) (Finset.mem_univ i)
  have hj := Finset.single_le_sum (s:=Finset.univ) (fun (a : ι) _ => Complex.normSq_nonneg (v k a)) (Finset.mem_univ j)
  rw [← Complex.sq_norm] at hi hj
  nlinarith only [hi,hj,sq_nonneg (‖v k i‖-‖v k j‖)]

def splitPair (n : ℕ) : PairSpace × Space n ≃ᵐ Space (n+2) :=
  (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl Position).prodCongr
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Position) 0).symm)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => Position) 0).symm

theorem splitPair_preserving (n : ℕ) :
    MeasurePreserving (splitPair n) (pairVolume.prod volume) volume := by
  let u := fun k => MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => Position) 0
  have hu (k) : MeasurePreserving (u k).symm := (volume_preserving_piFinSuccAbove _ 0).symm
  rw [show pairVolume = (volume : Measure PairSpace) from (Measure.volume_eq_prod Position Position).symm]
  exact (hu (n+1)).comp (((MeasurePreserving.id (μ := (volume : Measure Position))).prod (hu n)).comp volume_preserving_prodAssoc)

theorem splitPair_apply {n : ℕ} (p : PairSpace × Space n) :
    splitPair n p = Fin.cons p.1.1 (Fin.cons p.1.2 p.2) := by
  let u := fun k => MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => Position) 0
  have hu (k : ℕ) (z : Position × Space k) : (u k).symm z = Fin.cons z.1 z.2 := by
    simp [u,MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  change (u _).symm (p.1.1,(u _).symm (p.1.2,p.2)) = _
  simp only [hu]

def pairAmplitude {n : ℕ} (ψ : Wave (n+2)) (s : Spins n) (i : (Fin 2 × Fin 2))
    (z : PairSpace) (y : Space n) :=
  ψ.value (Fin.cons i.1 (Fin.cons i.2 s)) (Fin.cons z.1 (Fin.cons z.2 y))

theorem pairAmplitude_L2 {n : ℕ} (ψ : Wave (n+2)) (s : Spins n) (i : (Fin 2 × Fin 2)) :
    MemLp (fun p : PairSpace × Space n => pairAmplitude ψ s i p.1 p.2) 2 (pairVolume.prod volume) := by
  simpa only [pairAmplitude, Function.comp_def, splitPair_apply] using
    (ψ.square_integrable (Fin.cons i.1 (Fin.cons i.2 s))).comp_measurePreserving (splitPair_preserving n)

private theorem pairAmplitude_slice {n : ℕ} (ψ : Wave (n+2)) :
    ∀ᵐ z ∂pairVolume, ∀ s i, MemLp (pairAmplitude ψ s i z) 2 := by
  apply ae_all_iff.mpr
  intro s
  apply ae_all_iff.mpr
  intro i
  have h := pairAmplitude_L2 ψ s i
  filter_upwards [(h.integrable_norm_pow (p:=2) (by decide)).prod_right_ae,
    h.aestronglyMeasurable.prodMk_left] with z hz hm
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hz

/-- Spin pair marginal in the convention ψᵢ times the conjugate of ψⱼ. -/
def Wave.pairDensitySpin {n : ℕ} (ψ : Wave (n+2)) (z : PairSpace) : PairSpinMatrix :=
  (((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)/2) • ∑ s : Spins n, Matrix.of (fun i j =>
    ∫ y, pairAmplitude ψ s i z y * conj (pairAmplitude ψ s j z y))

theorem Wave.pairDensitySpin_posSemidef {n : ℕ} (ψ : Wave (n+2)) :
    ∀ᵐ z ∂pairVolume, (ψ.pairDensitySpin z).PosSemidef := by
  filter_upwards [pairAmplitude_slice ψ] with z hz
  apply Matrix.PosSemidef.smul _ (by positivity : 0 ≤ ((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)/2)
  apply Matrix.posSemidef_sum
  intro s _
  let V (i : (Fin 2 × Fin 2)) := (hz s i).toLp (pairAmplitude ψ s i z)
  have eqn : (Matrix.of fun i j => ∫ y, pairAmplitude ψ s i z y * conj (pairAmplitude ψ s j z y)) =
      (Matrix.gram ℂ V).transpose := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply,Matrix.gram_apply,L2.inner_def,RCLike.inner_apply]
    apply integral_congr_ae
    filter_upwards [(hz s i).coeFn_toLp,(hz s j).coeFn_toLp] with y hi hj
    rw [show V i y = _ from hi, show V j y = _ from hj]
  rw [eqn]
  exact (Matrix.posSemidef_gram ℂ V).transpose

private theorem sum_pair_spins {n : ℕ} (f : Spins (n+2) → ℝ) :
    ∑ i : (Fin 2 × Fin 2), ∑ s : Spins n, f (Fin.cons i.1 (Fin.cons i.2 s)) = ∑ t, f t := by
  rw [Fintype.sum_prod_type]
  let e := fun k => Fin.consEquiv (fun _ : Fin (k+1) => Fin 2)
  have step (k : ℕ) (g : Spins (k+1) → ℝ) :
      ∑ a, ∑ s, g (Fin.cons a s) = ∑ t, g t := by
    have he := (e k).sum_comp g
    rw [Fintype.sum_prod_type] at he
    exact he
  calc
    _ = ∑ a, ∑ t, f (Fin.cons a t) := Finset.sum_congr rfl fun a _ => step n (fun t => f (Fin.cons a t))
    _ = _ := step (n+1) f
  
theorem Wave.trace_pairDensitySpin {n : ℕ} (ψ : Wave (n+2)) (z : PairSpace) :
    (ψ.pairDensitySpin z).trace.re = ψ.pairDensity z.1 z.2/2 := by
  have diag (s : Spins n) (i : (Fin 2 × Fin 2)) :
      (∫ y, pairAmplitude ψ s i z y * conj (pairAmplitude ψ s i z y)).re =
      ∫ y, ‖pairAmplitude ψ s i z y‖^2 := by
    simp only [Complex.mul_conj,← Complex.sq_norm,integral_complex_ofReal,Complex.ofReal_re]
  simp only [Wave.pairDensitySpin,Matrix.trace,Matrix.diag_apply,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.of_apply,Complex.real_smul,Complex.re_sum,Complex.re_ofReal_mul,diag,← Finset.mul_sum]
  unfold pairAmplitude Wave.pairDensity
  rw [sum_pair_spins (fun s => ∫ y : Space n, ‖ψ.value s (Fin.cons z.1 (Fin.cons z.2 y))‖^2)]
  ring

def PureState.pairDensitySpin : PureState → PairSpace → PairSpinMatrix
  | .vacuum, _ => 0
  | .occupied (n:=0) _, _ => 0
  | .occupied (n:=_+1) ψ,z => ψ.pairDensitySpin z

theorem PureState.trace_pairDensitySpin (s : PureState) (z : PairSpace) :
    (s.pairDensitySpin z).trace.re = s.pairDensity z.1 z.2/2 := by
  cases s with
  | vacuum => simp [pairDensitySpin,pairDensity]
  | @occupied n ψ => cases n with
    | zero => simp [pairDensitySpin,pairDensity]
    | succ n => exact ψ.trace_pairDensitySpin z

theorem PureState.pairDensitySpin_posSemidef (s : PureState) :
    ∀ᵐ z ∂pairVolume, (s.pairDensitySpin z).PosSemidef := by
  cases s with
  | vacuum => exact ae_of_all _ fun _ => Matrix.PosSemidef.zero
  | @occupied n ψ => cases n with
    | zero => exact ae_of_all _ fun _ => Matrix.PosSemidef.zero
    | succ n => exact ψ.pairDensitySpin_posSemidef

theorem PureState.pairDensitySpin_entry_integrable (s : PureState) (i j : (Fin 2 × Fin 2)) :
    Integrable (fun z => s.pairDensitySpin z i j) pairVolume := by
  cases s with
  | vacuum => simp [pairDensitySpin]
  | @occupied n ψ => cases n with
    | zero => simp [pairDensitySpin]
    | succ n =>
      simp only [pairDensitySpin,Wave.pairDensitySpin,Matrix.smul_apply,Matrix.sum_apply,Matrix.of_apply,
        Complex.real_smul,Finset.mul_sum]
      apply integrable_finsetSum
      intro t _
      apply Integrable.const_mul
      have hj := pairAmplitude_L2 ψ t j
      have hc : MemLp (fun p : PairSpace × Space n => conj (pairAmplitude ψ t j p.1 p.2)) 2 (pairVolume.prod volume) :=
        hj.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hj.1) (ae_of_all _ fun _ => (Complex.norm_conj _).le)
      exact ((pairAmplitude_L2 ψ t i).integrable_mul hc).integral_prod_left

/-- The spin pair density in the spectral ensemble representation. -/
def MixedState.pairDensitySpin (Γ : MixedState) (z : PairSpace) : PairSpinMatrix := fun i j =>
  ∑' k, (Γ.weight k : ℂ) * (Γ.component k).pairDensitySpin z i j

/-- The Coulomb multiplier on the two selected positions. -/
def pairWeight (z : PairSpace) : ℝ := ‖z.1-z.2‖⁻¹

theorem pairWeight_nonneg (z : PairSpace) : 0 ≤ pairWeight z := inv_nonneg.mpr (norm_nonneg _)

theorem measurable_pairWeight : Measurable pairWeight := by unfold pairWeight; fun_prop

private def componentPairMass (Γ : MixedState) (k : ℕ) (z : PairSpace) : ℝ :=
  Γ.weight k * ((Γ.component k).pairDensity z.1 z.2 / (2*‖z.1-z.2‖))

private theorem componentPairMass_nonneg (Γ : MixedState) (k : ℕ) (z : PairSpace) :
    0 ≤ componentPairMass Γ k z := mul_nonneg (Γ.weight_nonneg k)
  (div_nonneg ((Γ.component k).pairDensity_nonneg _ _) (mul_nonneg (by norm_num) (norm_nonneg _)))

private theorem sum_componentPairMass (Γ : MixedState) (z : PairSpace) :
    ∑' k, componentPairMass Γ k z = Γ.pairKernel z := by
  simp only [componentPairMass,MixedState.pairKernel,div_eq_mul_inv,← mul_assoc,tsum_mul_right]

private theorem ae_summable_componentPairMass (Γ : MixedState) :
    ∀ᵐ z ∂pairVolume, Summable (fun k => componentPairMass Γ k z) := by
  let F := componentPairMass Γ
  have hi (k) : Integrable (F k) pairVolume := ((Γ.component k).integral_pairDensity.1).const_mul _
  have hp (k) : 0 ≤ᵐ[pairVolume] F k := ae_of_all _ (componentPairMass_nonneg Γ k)
  have hm (k) : eLpNorm (F k) 1 pairVolume = ENNReal.ofReal (Γ.weight k*(Γ.component k).interaction) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      _ = ∫⁻ z, ENNReal.ofReal (F k z) ∂pairVolume := by
        apply lintegral_congr
        intro z
        rw [← ofReal_norm,Real.norm_of_nonneg (componentPairMass_nonneg Γ k z)]
      _ = ENNReal.ofReal (∫ z, F k z ∂pairVolume) := (ofReal_integral_eq_lintegral_ofReal (hi k) (hp k)).symm
      _ = _ := by simp [F,componentPairMass,integral_const_mul,(Γ.component k).integral_pairDensity.2]
  have hn : ∀ᵐ z ∂pairVolume, Summable (fun k => ‖F k z‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl (fun k => (hi k).1)
    simpa only [hm] using Γ.interaction_summable.tsum_ofReal_ne_top
  exact hn.mono fun _ h => h.of_norm

private def weightedComponent (Γ : MixedState) (k : ℕ) (z : PairSpace) : PairSpinMatrix :=
  (pairWeight z * Γ.weight k) • (Γ.component k).pairDensitySpin z

private theorem weightedComponent_entry (Γ : MixedState) (k : ℕ) (z : PairSpace) (i j : (Fin 2 × Fin 2)) :
    weightedComponent Γ k z i j = (pairWeight z : ℂ) * ((Γ.weight k : ℂ) * (Γ.component k).pairDensitySpin z i j) := by
  simp [weightedComponent,Complex.real_smul,mul_assoc]

private theorem weightedComponent_bound (Γ : MixedState) (k : ℕ) :
    ∀ᵐ z ∂pairVolume, ∀ i j, ‖weightedComponent Γ k z i j‖ ≤ componentPairMass Γ k z := by
  filter_upwards [(Γ.component k).pairDensitySpin_posSemidef] with z hz
  intro i j
  have h := mul_le_mul_of_nonneg_left (spinEntry_le_trace hz i j)
    (mul_nonneg (pairWeight_nonneg z) (Γ.weight_nonneg k))
  rw [(Γ.component k).trace_pairDensitySpin] at h
  change ‖(pairWeight z * Γ.weight k) • ((Γ.component k).pairDensitySpin z i j)‖ ≤ _
  rw [norm_smul,Real.norm_of_nonneg (mul_nonneg (pairWeight_nonneg z) (Γ.weight_nonneg k))]
  exact h.trans_eq (by dsimp [componentPairMass,pairWeight]; ring)

private theorem weightedComponent_hasSum (Γ : MixedState) :
    ∀ᵐ z ∂pairVolume, HasSum (fun k => weightedComponent Γ k z) (pairWeight z • Γ.pairDensitySpin z) := by
  filter_upwards [ae_summable_componentPairMass Γ, ae_all_iff.mpr (weightedComponent_bound Γ)] with z hm hbound
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  have h := hm.of_norm_bounded (fun k => hbound k i j)
  apply Eq.subst (motive := fun a => HasSum (fun k => weightedComponent Γ k z i j) a) _ h.hasSum
  change (∑' k, weightedComponent Γ k z i j) = (pairWeight z : ℂ) * ∑' k, (Γ.weight k : ℂ) * (Γ.component k).pairDensitySpin z i j
  simp_rw [weightedComponent_entry,tsum_mul_left]

/-- Absolute integrability of every Coulomb-weighted entry. -/
theorem MixedState.pairDensitySpin_weighted_integrable (Γ : MixedState) (i j : (Fin 2 × Fin 2)) :
    Integrable (fun z => (pairWeight z : ℂ) * Γ.pairDensitySpin z i j) pairVolume := by
  apply Γ.integral_pairKernel.1.mono'
  · exact (Complex.measurable_ofReal.comp measurable_pairWeight).aestronglyMeasurable.mul
      (AEStronglyMeasurable.tsum (fun k => ((Γ.component k).pairDensitySpin_entry_integrable i j).1.const_mul _))
  filter_upwards [weightedComponent_hasSum Γ, ae_all_iff.mpr (weightedComponent_bound Γ),
    ae_summable_componentPairMass Γ] with z hz hb hs
  have h := Pi.hasSum.mp (Pi.hasSum.mp hz i) j
  change HasSum (fun k => weightedComponent Γ k z i j) ((pairWeight z : ℂ)*Γ.pairDensitySpin z i j) at h
  rw [← h.tsum_eq,← sum_componentPairMass]
  exact (norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hb k i j))).trans
    (Summable.tsum_le_tsum (fun k => hb k i j) (hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hb k i j)) hs)

private theorem weighted_pair_positive (Γ : MixedState) :
    ∀ᵐ z ∂pairVolume, (pairWeight z • Γ.pairDensitySpin z).PosSemidef := by
  filter_upwards [weightedComponent_hasSum Γ,ae_all_iff.mpr (fun k => (Γ.component k).pairDensitySpin_posSemidef)] with z hz hp
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hz (Eventually.of_forall fun s =>
    Matrix.posSemidef_sum _ fun k _ => (hp k).smul (mul_nonneg (pairWeight_nonneg z) (Γ.weight_nonneg k)))

private theorem trace_weighted_pair (Γ : MixedState) :
    ∀ᵐ z ∂pairVolume, (pairWeight z • Γ.pairDensitySpin z).trace.re = Γ.pairKernel z := by
  filter_upwards [weightedComponent_hasSum Γ,ae_summable_componentPairMass Γ] with z hz hm
  have e (k) : (weightedComponent Γ k z).trace.re = componentPairMass Γ k z := by
    simp only [weightedComponent,Matrix.trace_smul,Complex.real_smul,Complex.re_ofReal_mul,
      (Γ.component k).trace_pairDensitySpin]
    dsimp [componentPairMass,pairWeight]
    ring
  have hs := Complex.hasSum_re (hasSum_sum fun i (_ : i ∈ Finset.univ) => Pi.hasSum.mp (Pi.hasSum.mp hz i) i)
  change HasSum (fun k => (weightedComponent Γ k z).trace.re) (pairWeight z • Γ.pairDensitySpin z).trace.re at hs
  simp_rw [e] at hs
  exact hs.tsum_eq.symm.trans (sum_componentPairMass Γ z)

private theorem PureState.weighted_entry_bound (s : PureState) (i j : (Fin 2 × Fin 2)) :
    ∀ᵐ z ∂pairVolume, ‖(pairWeight z : ℂ)*s.pairDensitySpin z i j‖ ≤ s.pairDensity z.1 z.2/(2*‖z.1-z.2‖) := by
  filter_upwards [s.pairDensitySpin_posSemidef] with z hz
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pairWeight_nonneg z)]
  exact (mul_le_mul_of_nonneg_left (spinEntry_le_trace hz i j) (pairWeight_nonneg z)).trans_eq (by
    rw [s.trace_pairDensitySpin]; unfold pairWeight; ring)

theorem PureState.pairDensitySpin_weighted_integrable (s : PureState) (i j : (Fin 2 × Fin 2)) :
    Integrable (fun z => (pairWeight z : ℂ)*s.pairDensitySpin z i j) pairVolume :=
  s.integral_pairDensity.1.mono'
    ((Complex.measurable_ofReal.comp measurable_pairWeight).aestronglyMeasurable.mul
      (s.pairDensitySpin_entry_integrable i j).1) (s.weighted_entry_bound i j)

private theorem PureState.pair_test_L1 (s : PureState) (β : PairSpace → ℂ) (hβ : Measurable β)
    (B : ℝ) (bound : ∀ z, ‖β z‖ ≤ B) (i j : (Fin 2 × Fin 2)) :
    let F := fun z => β z * ((pairWeight z : ℂ)*s.pairDensitySpin z i j)
    Integrable F pairVolume ∧ (∫ z, ‖F z‖ ∂pairVolume) ≤ B*s.interaction := by
  intro F
  have H := s.integral_pairDensity.1.const_mul B
  have hp : 0 ≤ B := (norm_nonneg (β 0)).trans (bound 0)
  have hb : ∀ᵐ z ∂pairVolume, ‖F z‖ ≤ B*(s.pairDensity z.1 z.2/(2*‖z.1-z.2‖)) := by
    filter_upwards [s.weighted_entry_bound i j] with z hz
    rw [show ‖F z‖ = _ from norm_mul (β z) _]
    exact mul_le_mul (bound z) hz (norm_nonneg _) hp
  have hi := H.mono' (hβ.aestronglyMeasurable.mul (s.pairDensitySpin_weighted_integrable i j).1) hb
  exact ⟨hi,(integral_mono_ae hi.norm H hb).trans_eq (by rw [integral_const_mul,s.integral_pairDensity.2])⟩

theorem PureState.pair_test_bound (s : PureState) (β : PairSpace → ℂ) (hβ : Measurable β)
    (B : ℝ) (bound : ∀ z, ‖β z‖ ≤ B) (i j : (Fin 2 × Fin 2)) :
    ‖∫ z, β z * ((pairWeight z : ℂ)*s.pairDensitySpin z i j) ∂pairVolume‖ ≤ B*s.interaction :=
  (norm_integral_le_integral_norm _).trans (s.pair_test_L1 β hβ B bound i j).2

/-- A bounded probe of the Coulomb-weighted spin marginal is the same
spectral expectation for every realization of the countable ensemble. -/
theorem MixedState.pair_test_hasSum (Γ : MixedState) (β : PairSpace → ℂ) (hβ : Measurable β)
    (B : ℝ) (bound : ∀ z, ‖β z‖ ≤ B) (i j : (Fin 2 × Fin 2)) :
    HasSum (fun k => (Γ.weight k : ℂ) * ∫ z, β z * ((pairWeight z : ℂ)*
      (Γ.component k).pairDensitySpin z i j) ∂pairVolume)
      (∫ z, β z * ((pairWeight z : ℂ)*Γ.pairDensitySpin z i j) ∂pairVolume) := by
  let F := fun k (z : PairSpace) => β z * ((pairWeight z : ℂ)*(Γ.component k).pairDensitySpin z i j)
  let W := fun k z => (Γ.weight k : ℂ)*F k z
  have h (k) := (Γ.component k).pair_test_L1 β hβ B bound i j
  have hw (k) : Integrable (W k) pairVolume := (h k).1.const_mul _
  have hsum : Summable fun k => ∫ z, ‖W k z‖ ∂pairVolume := by
    apply (Γ.interaction_summable.mul_left B).of_nonneg_of_le (fun k => integral_nonneg fun z => norm_nonneg _)
    intro k
    simp only [W,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Γ.weight_nonneg k),integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (h k).2 (Γ.weight_nonneg k)).trans_eq (by ring)
  have eqn (z : PairSpace) : (∑' k, W k z) = β z * ((pairWeight z : ℂ)*Γ.pairDensitySpin z i j) := by
    simp only [W,F,MixedState.pairDensitySpin,← tsum_mul_left]
    exact tsum_congr fun _ => by ring
  have hi := hasSum_integral_of_summable_integral_norm hw hsum
  simp only [eqn,W,F,integral_const_mul] at hi
  exact hi

/-- Coulomb-weighted two-particle spin matrix. -/
def MixedState.coulombPairMatrix (Γ : MixedState) : PairSpinMatrix := fun i j =>
  ∫ z, (pairWeight z : ℂ) * Γ.pairDensitySpin z i j ∂pairVolume

def PureState.coulombPairMatrix (s : PureState) : PairSpinMatrix := fun i j =>
  ∫ z, (pairWeight z : ℂ) * s.pairDensitySpin z i j ∂pairVolume

theorem PureState.norm_coulombPairMatrix_entry (s : PureState) (i j : Fin 2 × Fin 2) :
    ‖s.coulombPairMatrix i j‖ ≤ s.interaction := by
  simpa only [one_mul, PureState.coulombPairMatrix] using
    s.pair_test_bound (fun _ => 1) measurable_const 1 (fun _ => by simp) i j

theorem MixedState.coulombPairMatrix_hasSum (Γ : MixedState) :
    HasSum (fun k => Γ.weight k • (Γ.component k).coulombPairMatrix) Γ.coulombPairMatrix := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  simpa only [one_mul, Matrix.smul_apply, Complex.real_smul, PureState.coulombPairMatrix,
    MixedState.coulombPairMatrix] using Γ.pair_test_hasSum (fun _ => 1) measurable_const 1
      (fun _ => by simp) i j

theorem MixedState.norm_coulombPairMatrix_entry (Γ : MixedState) (i j : Fin 2 × Fin 2) :
    ‖Γ.coulombPairMatrix i j‖ ≤ Γ.interaction := by
  have h := Pi.hasSum.mp (Pi.hasSum.mp Γ.coulombPairMatrix_hasSum i) j
  have hb (k : ℕ) : ‖Γ.weight k • (Γ.component k).coulombPairMatrix i j‖ ≤ Γ.weight k*(Γ.component k).interaction := by
    rw [norm_smul,Real.norm_of_nonneg (Γ.weight_nonneg k)]
    exact mul_le_mul_of_nonneg_left ((Γ.component k).norm_coulombPairMatrix_entry i j) (Γ.weight_nonneg k)
  rw [← h.tsum_eq]
  exact (norm_tsum_le_tsum_norm (Γ.interaction_summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
    (Summable.tsum_le_tsum hb (Γ.interaction_summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb) Γ.interaction_summable)

/-- Bounded Coulomb multipliers converge on the finite-interaction form domain. -/
def pairCutoffWeight (n : ℕ) (z : PairSpace) : ℂ := if pairWeight z ≤ n then (pairWeight z : ℂ) else 0

theorem measurable_pairCutoffWeight (n : ℕ) : Measurable (pairCutoffWeight n) :=
  (Complex.measurable_ofReal.comp measurable_pairWeight).ite (measurableSet_le measurable_pairWeight measurable_const) measurable_const

theorem norm_pairCutoffWeight_le (n : ℕ) (z : PairSpace) : ‖pairCutoffWeight n z‖ ≤ n := by
  unfold pairCutoffWeight
  split_ifs with h
  · simpa only [Complex.norm_real,Real.norm_of_nonneg (pairWeight_nonneg z)] using h
  · simp

private theorem cutoff_matrix_tendsto (P : PairSpace → PairSpinMatrix)
    (hi : ∀ i j, Integrable (fun z => (pairWeight z : ℂ) * P z i j) pairVolume)
    (hm : ∀ i j, AEStronglyMeasurable (fun z => P z i j) pairVolume) :
    Tendsto (fun n i j => ∫ z, pairCutoffWeight n z * P z i j ∂pairVolume) atTop
      (𝓝 (fun i j => ∫ z, (pairWeight z : ℂ) * P z i j ∂pairVolume)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_integral_of_dominated_convergence (fun z => ‖(pairWeight z : ℂ) * P z i j‖)
    (fun n => (measurable_pairCutoffWeight n).aestronglyMeasurable.mul (hm i j)) (hi i j).norm
  · intro n
    apply ae_of_all
    intro z
    change ‖pairCutoffWeight n z * P z i j‖ ≤ _
    unfold pairCutoffWeight
    split_ifs
    · exact le_rfl
    · rw [zero_mul,norm_zero]
      exact norm_nonneg _
  · apply ae_of_all
    intro z
    obtain ⟨N,hN⟩ := exists_nat_ge (pairWeight z)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    change (pairWeight z : ℂ) * P z i j = pairCutoffWeight n z * P z i j
    simp [pairCutoffWeight,show pairWeight z ≤ (n : ℝ) from hN.trans (by exact_mod_cast hn)]

theorem PureState.coulombPairMatrix_tendsto (s : PureState) :
    Tendsto (fun n i j => ∫ z, pairCutoffWeight n z * s.pairDensitySpin z i j ∂pairVolume) atTop
      (𝓝 s.coulombPairMatrix) :=
  cutoff_matrix_tendsto _ s.pairDensitySpin_weighted_integrable (fun i j => (s.pairDensitySpin_entry_integrable i j).1)

theorem MixedState.coulombPairMatrix_tendsto (Γ : MixedState) :
    Tendsto (fun n i j => ∫ z, pairCutoffWeight n z * Γ.pairDensitySpin z i j ∂pairVolume) atTop
      (𝓝 Γ.coulombPairMatrix) :=
  cutoff_matrix_tendsto _ Γ.pairDensitySpin_weighted_integrable (fun i j =>
    AEStronglyMeasurable.tsum (fun k => ((Γ.component k).pairDensitySpin_entry_integrable i j).1.const_mul _))

theorem MixedState.pairCutoffWeight_hasSum (Γ : MixedState) (n : ℕ) (i j : Fin 2 × Fin 2) :
    HasSum (fun k => (Γ.weight k : ℂ) * ∫ z, pairCutoffWeight n z * (Γ.component k).pairDensitySpin z i j ∂pairVolume)
      (∫ z, pairCutoffWeight n z * Γ.pairDensitySpin z i j ∂pairVolume) := by
  let β := fun z => if pairWeight z ≤ n then (1 : ℂ) else 0
  have hm : Measurable β := Measurable.ite (measurableSet_le measurable_pairWeight measurable_const) measurable_const measurable_const
  have hb (z) : ‖β z‖ ≤ 1 := by simp only [β]; split_ifs <;> simp
  have e (z) (a : ℂ) : β z * ((pairWeight z : ℂ) * a) = pairCutoffWeight n z * a := by
    simp only [β,pairCutoffWeight]; split_ifs <;> simp
  simpa only [e] using Γ.pair_test_hasSum β hm 1 hb i j

private theorem trace_integral_pair (f : PairSpace → PairSpinMatrix)
    (hi : ∀ i j, Integrable (fun z => f z i j) pairVolume) :
    (Matrix.of fun i j => ∫ z, f z i j ∂pairVolume).trace.re = ∫ z, (f z).trace.re ∂pairVolume := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.of_apply,Complex.re_sum]
  calc
    _ = ∑ i, ∫ z, (f z i i).re ∂pairVolume := Finset.sum_congr rfl fun i _ => (integral_re (hi i i)).symm
    _ = _ := (integral_finsetSum _ fun i _ => (hi i i).re).symm

theorem MixedState.trace_coulombPairMatrix (Γ : MixedState) : Γ.coulombPairMatrix.trace.re = Γ.interaction := by
  refine (trace_integral_pair (fun z => pairWeight z • Γ.pairDensitySpin z) Γ.pairDensitySpin_weighted_integrable).trans ?_
  exact (integral_congr_ae (trace_weighted_pair Γ)).trans Γ.integral_pairKernel.2

theorem PureState.trace_coulombPairMatrix (s : PureState) : s.coulombPairMatrix.trace.re = s.interaction := by
  refine (trace_integral_pair (fun z => pairWeight z • s.pairDensitySpin z) s.pairDensitySpin_weighted_integrable).trans ?_
  refine Eq.trans (integral_congr_ae (ae_of_all _ (fun z => ?_))) s.integral_pairDensity.2
  simp only [Matrix.trace_smul,Complex.real_smul,Complex.re_ofReal_mul,s.trace_pairDensitySpin]
  dsimp [pairWeight]
  ring

private theorem integral_pair_positive (f : PairSpace → PairSpinMatrix)
    (hi : ∀ i j, Integrable (fun z => f z i j) pairVolume)
    (hp : ∀ᵐ z ∂pairVolume, (f z).PosSemidef) :
    (Matrix.of fun i j => ∫ z, f z i j ∂pairVolume).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    change conj (∫ z, f z j i ∂pairVolume) = ∫ z, f z i j ∂pairVolume
    rw [← integral_conj]
    exact integral_congr_ae (hp.mono fun z h => h.isHermitian.apply i j)
  · intro v
    have he : star v ⬝ᵥ (Matrix.of fun i j => ∫ z, f z i j ∂pairVolume) *ᵥ v =
        ∫ z, star v ⬝ᵥ f z *ᵥ v ∂pairVolume := by
      have H (i j) := ((hi i j).mul_const (v j)).const_mul (star v i)
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,integral_finsetSum _ (fun i _ =>
        integrable_finsetSum _ fun j _ => H i j),integral_finsetSum _ (fun j _ => H _ j),
        integral_const_mul,integral_mul_const,Matrix.of_apply]
    rw [he]
    exact integral_nonneg_of_ae (hp.mono fun z h => h.dotProduct_mulVec_nonneg v)

theorem PureState.coulombPairMatrix_posSemidef (s : PureState) : s.coulombPairMatrix.PosSemidef :=
  integral_pair_positive (fun z => pairWeight z • s.pairDensitySpin z) s.pairDensitySpin_weighted_integrable
    (s.pairDensitySpin_posSemidef.mono fun z h => h.smul (pairWeight_nonneg z))

theorem MixedState.coulombPairMatrix_posSemidef (Γ : MixedState) : Γ.coulombPairMatrix.PosSemidef :=
  integral_pair_positive (fun z => pairWeight z • Γ.pairDensitySpin z) Γ.pairDensitySpin_weighted_integrable
    (weighted_pair_positive Γ)

/-- Pulling the two spin tests through the localized pair marginal gives its
physical Coulomb interaction. -/
theorem interaction_spin_channel {Γ Λ : MixedState} (S : SpinMatrix)
    (channel : Λ.pairDensitySpin =ᵐ[pairVolume]
      fun z => (S ⊗ₖ S) * Γ.pairDensitySpin z * star (S ⊗ₖ S)) :
    Λ.interaction = (((star S * S) ⊗ₖ (star S * S)) * Γ.coulombPairMatrix).trace.re := by
  let U := S ⊗ₖ S
  have hc : Λ.coulombPairMatrix = U * Γ.coulombPairMatrix * star U := by
    ext i j
    have h (z) (hz : Λ.pairDensitySpin z = U * Γ.pairDensitySpin z * star U) :
        (pairWeight z : ℂ) * Λ.pairDensitySpin z i j =
        ∑ a, ∑ b, U i b * ((pairWeight z : ℂ) * Γ.pairDensitySpin z b a) * star U a j := by
      rw [hz]
      simp only [Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    change (∫ z, (pairWeight z : ℂ)*Λ.pairDensitySpin z i j ∂pairVolume) = _
    rw [integral_congr_ae (channel.mono (fun z hz => h z hz))]
    have hi (a b) := ((Γ.pairDensitySpin_weighted_integrable b a).const_mul (U i b)).mul_const (star U a j)
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
    simp only [integral_finsetSum _ (fun b _ => hi _ b),integral_mul_const,integral_const_mul,
      Matrix.mul_apply,Finset.sum_mul,MixedState.coulombPairMatrix]
  rw [← Λ.trace_coulombPairMatrix,hc,Matrix.trace_mul_cycle]
  have eqn : star U * U = (star S * S) ⊗ₖ (star S * S) := by
    change (S ⊗ₖ S).conjTranspose * (S ⊗ₖ S) = _
    rw [Matrix.conjTranspose_kronecker,Matrix.mul_kronecker_mul]
    rfl
  rw [eqn]

end TSGA.ManyBody
