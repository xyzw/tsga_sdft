import TSGA.LocalSpinTensor
import TSGA.LocalRotationQuadratic
import TSGA.LocalRotationMarginal

/-! # Local multiplication of a concrete fermionic wave -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder ContDiff

abbrev LocalUnitaryMeasurable (U : Position → unitary SpinMatrix) :=
  ∀ i j, AEMeasurable (fun x => (U x : SpinMatrix) i j) volume

def localTensorValue {n : ℕ} (U : Position → unitary SpinMatrix) (f : Spins n → Space n → ℂ)
    (s : Spins n) (x : Space n) : ℂ := (sectorLocalUnitary U x *ᵥ (fun a => f a x)) s

def Wave.localFirst {n : ℕ} (ψ : Wave n) (U : Position → unitary SpinMatrix) : LocalSectorGradient n :=
  fun s x i j => localTensorValue U (fun a z => ψ.gradient a z i j) s x

def Wave.localSecond {n : ℕ} (ψ : Wave n) (U : Position → unitary SpinMatrix) (H : MatrixGradient) : LocalSectorGradient n :=
  fun s x i j => (sectorLocalPartial U H x i j *ᵥ (fun a => ψ.value a x)) s

private theorem spin_tensor_meas {n : ℕ} (A : Space n → Fin n → SpinMatrix)
    (hA : ∀ k i j, AEMeasurable (fun x => A x k i j) volume) (s t : Spins n) :
    AEMeasurable (fun x => sectorSpinTensor n (A x) s t) volume :=
  Finset.aemeasurable_fun_prod _ (fun k _ => hA k (s k) (t k))

private theorem eval_meas {n : ℕ} {f : Position → ℂ} (hf : AEMeasurable f volume) (i : Fin n) :
    AEMeasurable (fun x : Space n => f (x i)) volume :=
  hf.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure Position)) i)

theorem localTensorValue_L2 {n : ℕ} (U : Position → unitary SpinMatrix) (hU : LocalUnitaryMeasurable U)
    (f : Spins n → Space n → ℂ) (hf : ∀ a, MemLp (f a) 2 volume) (s : Spins n) :
    MemLp (localTensorValue U f s) 2 volume := by
  have hm : AEMeasurable (localTensorValue U f s) volume :=
    Finset.aemeasurable_fun_sum _ fun a _ => (spin_tensor_meas _ (fun k i j => eval_meas (hU i j) k) s a).mul (hf a).aemeasurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (integrable_finsetSum Finset.univ (fun a _ => (hf a).integrable_norm_pow (p := 2) (by decide))).mono'
    (hm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _), ← sectorLocalUnitary_norm U x (fun a => f a x)]
  exact Finset.single_le_sum (f := fun t => ‖(sectorLocalUnitary U x *ᵥ (fun a => f a x)) t‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ s)

private theorem Wave.tensor_antisymmetric {n : ℕ} (ψ : Wave n) (U : Position → unitary SpinMatrix)
    (π : Equiv.Perm (Fin n)) (s : Spins n) : ∀ᵐ x, localTensorValue U ψ.value (s ∘ π) (x ∘ π) =
      ((Equiv.Perm.sign π : ℤˣ) : ℤ) * localTensorValue U ψ.value s x := by
  let e := Equiv.arrowCongr π.symm (Equiv.refl (Fin 2))
  filter_upwards [ae_all_iff.mpr (ψ.antisymmetric π)] with x hx
  unfold localTensorValue Matrix.mulVec dotProduct
  rw [← e.sum_comp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (∏ k, (U (x (π k)) : SpinMatrix) (s (π k)) (a (π k))) * ψ.value (a ∘ π) (x ∘ π) = _
  rw [Equiv.prod_comp π (fun k => (U (x k) : SpinMatrix) (s k) (a k)),hx]
  unfold sectorLocalUnitary sectorSpinTensor
  ring

private theorem Wave.tensor_potential {n : ℕ} (ψ : Wave n) (U : Position → unitary SpinMatrix) (hU : LocalUnitaryMeasurable U)
    (a : Space n → ℝ) (ha : Measurable a) (ha' : ∀ x, 0 ≤ a x) (hi : ∀ s, Integrable (fun x => a x*‖ψ.value s x‖^2)) :
    (∀ s, Integrable (fun x => a x*‖localTensorValue U ψ.value s x‖^2)) ∧
      sectorIntegral (fun s x => a x*‖localTensorValue U ψ.value s x‖^2) = sectorIntegral (fun s x => a x*‖ψ.value s x‖^2) := by
  have ht s : Integrable (fun x => a x*‖localTensorValue U ψ.value s x‖^2) := by
    apply (integrable_finsetSum Finset.univ (fun s _ => hi s)).mono'
      (ha.aestronglyMeasurable.mul ((localTensorValue_L2 U hU _ ψ.square_integrable s).aestronglyMeasurable.norm.pow _))
    filter_upwards with x
    change ‖a x*‖localTensorValue U ψ.value s x‖^2‖ ≤ ∑ t, a x*‖ψ.value t x‖^2
    rw [Real.norm_of_nonneg (mul_nonneg (ha' _) (sq_nonneg _)), ← Finset.mul_sum, ← sectorLocalUnitary_norm U x (fun s => ψ.value s x)]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun t => ‖localTensorValue U ψ.value t x‖^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ s)) (ha' _)
  refine ⟨ht,?_⟩
  unfold sectorIntegral
  rw [← integral_finsetSum _ (fun s _ => ht s),← integral_finsetSum _ (fun s _ => hi s)]
  simp only [← Finset.mul_sum,localTensorValue,sectorLocalUnitary_norm]

def cutLocalMatrix (O : Set Position) (H : MatrixGradient) : MatrixGradient := fun x j =>
  O.indicator (fun y => H y j) x

private theorem cutLocal_meas {D : Density} {O U H} (hO : LocalRotationDomain D O)
    (hH : IsMatrixGradientOn O U H) (i j k) : AEMeasurable (fun x => cutLocalMatrix O H x i j k) volume := by
  have hs := (aestronglyMeasurable_indicator_iff hO.measurableSet).mpr (hH i j k).2.1.aestronglyMeasurable
  have eq : (fun x => cutLocalMatrix O H x i j k) = O.indicator (fun x => H x i j k) := by
    funext x
    by_cases hx : x ∈ O <;> simp [cutLocalMatrix,hx]
  rw [eq]
  exact hs.aemeasurable

private theorem cutLocal_bound {D : Density} {O : Set Position} {H : MatrixGradient} {w : Position → ℝ}
    (hO : LocalRotationDomain D O) (hw : ∀ x, 0 ≤ w x)
    (hB : ∀ᵐ x ∂volume.restrict O, (∑ j, star (H x j)*H x j) ≤ (w x : ℂ) • (1 : SpinMatrix)) :
    ∀ᵐ x, (∑ j, star (cutLocalMatrix O H x j)*cutLocalMatrix O H x j) ≤ (w x : ℂ) • (1 : SpinMatrix) := by
  filter_upwards [(ae_restrict_iff' hO.measurableSet).mp hB] with x hx
  by_cases hm : x ∈ O
  · simpa [cutLocalMatrix,hm] using hx hm
  · simp only [cutLocalMatrix,Set.indicator_of_notMem hm,star_zero,zero_mul,Finset.sum_const_zero]
    exact (show (0 : SpinMatrix) ≤ w x • (1 : SpinMatrix) from smul_nonneg (hw x) zero_le_one)

private theorem Wave.localSecond_meas {n : ℕ} (ψ : Wave n) {U} (hU : LocalUnitaryMeasurable U)
    {H : MatrixGradient} (hm : ∀ i j k, AEMeasurable (fun x => H x i j k) volume) (s i j) :
    AEMeasurable (fun x => ψ.localSecond U H s x i j) volume := by
  apply Finset.aemeasurable_fun_sum
  intro a _
  apply AEMeasurable.mul _ (ψ.square_integrable a).aemeasurable
  refine spin_tensor_meas _ ?_ s a
  intro k b c
  by_cases e : k = i
  · subst k
    simpa only [Function.update_self] using eval_meas (hm j b c) i
  · simpa only [Function.update_of_ne e] using eval_meas (hU b c) k

private theorem localForm_integral {n : ℕ} (a : LocalSectorGradient n) (ha : LocalGradientL2 a) :
    localGradientForm a = ∫ x, ∑ i, ∑ j, ∑ s, ‖a s x i j‖^2 := by
  have hi s i j := (ha s i j).integrable_norm_pow (p := 2) (by decide)
  unfold localGradientForm
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Spins n))) (t := (Finset.univ : Finset (Fin 3)))]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun s _ => hi s i j)]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun s _ => hi s _ j),
    integral_finsetSum _ (fun s _ => hi s _ _)]

/-- Weak product rule on configuration space for a bounded tensor multiplier.
The input is an arbitrary finite array of H¹ functions with their weak
partials. The support is contained in an open neighborhood or a closed ball.
No normalization, exchange symmetry, ensemble, or quadratic form occurs. -/
def LocalSectorLeibniz : Prop := ∀ (K O : Set Position), IsClosed K → K ⊆ O →
  (IsOpen O ∨ ∃ c r, 0 < r ∧ O = Metric.closedBall c r) →
  ∀ (U : Position → unitary SpinMatrix) (H : MatrixGradient), LocalUnitaryMeasurable U →
  IsMatrixGradientOn O (fun x => (U x : SpinMatrix)) H →
  ∀ {n : ℕ} (f : Spins n → Space n → ℂ) (df : LocalSectorGradient n),
  (∀ s, MemLp (f s) 2 volume) → LocalGradientL2 df →
  (∀ s i j (g : Space n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
    (∫ x, fderiv ℝ g x (particleDirection i j) • f s x) = -(∫ x, g x • df s x i j)) →
  (∀ᵐ x : Space n, ∀ i, x i ∉ K → ∀ s, f s x = 0) →
  let db : LocalSectorGradient n := fun s x i j => (sectorLocalPartial U (cutLocalMatrix O H) x i j *ᵥ (fun a => f a x)) s
  LocalGradientL2 db → ∀ s i j (g : Space n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
    (∫ x, fderiv ℝ g x (particleDirection i j) • localTensorValue U f s x) =
      -(∫ x, g x • (localTensorValue U (fun a z => df a z i j) s x + db s x i j))

private theorem LocalRotationDomain.shape {D : Density} {O : Set Position} (h : LocalRotationDomain D O) :
    tsupport D.charge ⊆ O ∧ (IsOpen O ∨ ∃ c r, 0 < r ∧ O = Metric.closedBall c r) := by
  rcases h with ⟨ho,hd⟩ | ⟨c,r,hr,rfl,hz⟩
  · exact ⟨hd,Or.inl ho⟩
  · exact ⟨closure_minimal (fun x hx => by by_contra h; exact hx (hz x h)) Metric.isClosed_closedBall,
      Or.inr ⟨c,r,hr,rfl⟩⟩

structure LocalSpinCalculus : Prop where
  marginal : LocalScalarMarginal
  leibniz : LocalSectorLeibniz

/-- Derivation of the sector state and the linear and quadratic parts of its
kinetic change. The correction norm is bounded by the one-particle test w. -/
theorem LocalSectorLeibniz.wave {D : Density} {O : Set Position} {U : Position → unitary SpinMatrix}
    {H : MatrixGradient} {w : Position → ℝ} (c : LocalSectorLeibniz) (hO : LocalRotationDomain D O)
    (hU : LocalUnitaryMeasurable U) (hH : IsMatrixGradientOn O (fun x => (U x : SpinMatrix)) H)
    (hw : ∀ x, 0 ≤ w x) (hB : ∀ᵐ x ∂volume.restrict O, (∑ j, star (H x j)*H x j) ≤ (w x : ℂ) • (1 : SpinMatrix))
    {n : ℕ} (ψ : Wave (n+1)) (hψ : (PureState.occupied ψ).localizedOn (tsupport D.charge))
    (hi : Integrable (ψ.localMassDensity w)) :
    ∃ (χ : Wave (n+1)) (g j : ℝ), (∀ s x, χ.value s x = localTensorValue U ψ.value s x) ∧
      χ.interaction = ψ.interaction ∧ 0 ≤ g ∧ g ≤ (∫ x, ψ.localMassDensity w x) ∧
      (∀ t : ℝ, 0 ≤ ψ.kinetic + 2*t*j + t^2*g) ∧ χ.kinetic = ψ.kinetic + 2*j + g := by
  let a := ψ.localFirst U
  let b := ψ.localSecond U (cutLocalMatrix O H)
  have ha : LocalGradientL2 a := fun s i j => localTensorValue_L2 U hU _ (fun z => ψ.gradient_L2 z i j) s
  have bound : ∀ᵐ x : Space (n+1), (∑ i, ∑ j, ∑ s, ‖b s x i j‖^2) ≤ ψ.localMassDensity w x := by
    have h := cutLocal_bound hO hw hB
    filter_upwards [ae_all_iff.mpr fun i : Fin (n+1) =>
      (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure Position)) i).tendsto_ae h] with x hx
    exact Finset.sum_le_sum fun i _ => sectorLocalPartial_le U _ x i (fun s => ψ.value s x) (hx i)
  have hb : LocalGradientL2 b := by
    intro s i j
    have hm := ψ.localSecond_meas hU (cutLocal_meas hO hH) s i j
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    apply hi.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [bound] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_trans (Finset.single_le_sum (f := fun t => ‖b t x i j‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ s))
      ((Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
        ((Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)).trans hx))
  have hbI (s i j) := (hb s i j).integrable_norm_pow (p := 2) (by decide)
  have hg : localGradientForm b ≤ ∫ x, ψ.localMassDensity w x := by
    rw [localForm_integral b hb]
    exact integral_mono_ae (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun s _ => hbI s i j) hi bound
  have haK : localGradientForm a = ψ.kinetic := by
    rw [ψ.kinetic_eq_localForm,localForm_integral a ha,localForm_integral _ ψ.gradient_L2]
    simp only [a,Wave.localFirst,localTensorValue,sectorLocalUnitary_norm]
  have hV := ψ.tensor_potential U hU coulomb (by unfold coulomb; fun_prop) coulomb_nonneg ψ.interaction_integrable
  have hN := (ψ.tensor_potential U hU (fun _ => 1) measurable_const (fun _ => zero_le_one)
    (fun s => by simpa using (ψ.square_integrable s).integrable_norm_pow (p := 2) (by decide))).2
  let χ : Wave (n+1) := {
    value := localTensorValue U ψ.value
    gradient := fun s x i j => a s x i j + b s x i j
    antisymmetric := ψ.tensor_antisymmetric U
    square_integrable := localTensorValue_L2 U hU _ ψ.square_integrable
    normalized := by simpa only [one_mul] using hN.trans (by simpa only [one_mul] using ψ.normalized)
    gradient_L2 := fun s i j => (ha s i j).add (hb s i j)
    weak_gradient := c _ O (isClosed_tsupport D.charge) hO.shape.1 hO.shape.2 U H hU hH
      ψ.value ψ.gradient ψ.square_integrable ψ.gradient_L2 ψ.weak_gradient hψ hb
    interaction_integrable := hV.1 }
  refine ⟨χ,localGradientForm b,localGradientCross a b,fun _ _ => rfl,hV.2,localGradientForm_nonneg b,hg,?_,?_⟩
  · intro t
    rw [← haK,← localGradientForm_polar a b ha hb t]
    apply localGradientForm_nonneg
  · rw [χ.kinetic_eq_localForm,← haK]
    simpa only [Complex.ofReal_one,one_mul,mul_one,one_pow] using localGradientForm_polar a b ha hb 1

end TSGA.ManyBody
