import TSGA.CoulombModel

/-! # Common form of the three Coulomb gas moduli on a comparison ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization SSW
open scoped ComplexOrder

/-- The pointwise formula for the physical gas modulus. Here `b` selects
the matrix power in the bulk term and `a` is its Hölder exponent. -/
def SmallGasFormula {η : Mollifier} (M : PhysicalTileModulus η) (p b a K J : ℝ) : Prop :=
  ∀ (A B : SpinMatrix) (hA : A.PosSemidef) (hB : B.PosSemidef) (q k : Position),
    let r := max A.trace.re B.trace.re
    let d := fun s : ℝ => hilbertSchmidt (hA.1.cfc (fun z => z^s)-hB.1.cfc (fun z => z^s))/r^s
    M.value A B hA hB q k =
      J*((r^(4/3:ℝ)+r^(5/3:ℝ))*(d b)^a+r*‖q‖^2*d (1/p)) +
      (2*K+1)*(B.trace.re^(7/6:ℝ)+B.trace.re^(4/3:ℝ)+B.trace.re*max ‖q‖ ‖k‖)*‖q-k‖

variable {η : Mollifier} {K : ℝ}

theorem CoulombGasInputs.general_formula (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (S : SobolevDifferenceQuotients) {p θ : ℝ} (hp : 3 ≤ p) (hθ : 0 < θ) :
    ∃ J > 0, SmallGasFormula (L.generalModulus H S hp hθ) p θ (min 1 (1/(3*θ))) K J := by
  let law := coulomb_small_tile_modulus L.localization (L.kinematics H S) L.rate (L.removal H S)
    H.lo_nonneg H.indirect_lower hp hθ
  exact ⟨Classical.choose law, (Classical.choose_spec law).1, fun _ _ _ _ _ _ => rfl⟩

theorem CoulombGasInputs.minority_formula (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (S : SobolevDifferenceQuotients) {p θ ν : ℝ} (hp : 3 ≤ p) (hθ : 0 < θ) (hθ' : θ ≤ 1)
    (hν : 0 < ν) (hν' : ν ≤ 1/2) :
    ∃ J > 0, SmallGasFormula (L.minorityModulus H S hp hθ hθ' hν hν') p θ 1 K J := by
  let law := coulomb_minority_tile_modulus L.localization (L.kinematics H S) L.rate H.lo_nonneg H.indirect_lower
    hp hθ hθ' hν hν'
  refine ⟨Classical.choose law, (Classical.choose_spec law).1, ?_⟩
  intro A B hA hB q k
  dsimp only
  rw [Real.rpow_one]
  rfl

theorem CoulombGasInputs.root_formula (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (S : SobolevDifferenceQuotients) {p : ℝ} (hp : 3 ≤ p) :
    ∃ J > 0, SmallGasFormula (L.rootModulus H S hp) p (1/p) 1 K J := by
  let law := coulomb_root_tile_modulus L.localization (L.kinematics H S) L.rate (L.removal H S)
    H.lo_nonneg H.indirect_lower hp
  refine ⟨Classical.choose law, (Classical.choose_spec law).1, ?_⟩
  intro A B hA hB q k
  dsimp only
  rw [Real.rpow_one]
  change Classical.choose law * holderGrowth _ q * _ + _ = _
  unfold holderGrowth
  ring

/-- A bounded measurable multiplier is integrable against the translated
cutoff. Its average is bounded by its supremum on the cutoff support. -/
theorem bounded_cutoff_integral (P : TileProfile) (c : Position) {f : Position → ℝ}
    (meas : AEStronglyMeasurable f volume) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ᵐ x, P.cutoff (c-x) ≠ 0 → |f x| ≤ b) :
    Integrable (fun x => f x * P.cutoff (c-x)) ∧ cutoffAverage P.cutoff f c ≤ b := by
  let : (volume : Measure Position).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position).measurePreserving.map_eq⟩
  have hi := P.cutoff_integrable.comp_sub_left c
  have nonneg := (quasiMeasurePreserving_sub_left_of_right_invariant volume c).ae P.cutoff_nonneg
  have bound : ∀ᵐ x, ‖f x * P.cutoff (c-x)‖ ≤ b*P.cutoff (c-x) := by
    filter_upwards [h,nonneg] with x hx hn
    by_cases hz : P.cutoff (c-x) = 0
    · simp [hz]
    · rw [norm_mul,Real.norm_of_nonneg hn,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hx hz) hn
  have hi' := (hi.const_mul b).mono' (meas.mul hi.aestronglyMeasurable) bound
  refine ⟨hi', ?_⟩
  change (∫ x, f x * P.cutoff (c-x)) ≤ b
  have hsum := integral_mono_ae hi' (hi.const_mul b)
    (bound.mono fun x hx => (le_abs_self (f x*P.cutoff (c-x))).trans hx)
  rw [integral_const_mul,integral_sub_left_eq_self] at hsum
  exact hsum.trans (mul_le_of_le_one_right hb P.cutoff_mass_le_one)

private theorem continuous_coulomb_gas (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (S : SobolevDifferenceQuotients) :
    Continuous (fun z : {A : SpinMatrix // A.PosSemidef} × Position =>
      sswEnergy energy η z.1.val z.2) := by
  obtain ⟨_,_,hmat⟩ := coulomb_ssw_holder L.localization (L.kinematics H S) L.rate (L.removal H S)
    H.lo_nonneg H.indirect_lower
  exact continuous_ssw_of_holder (coulomb_sswGas η L.localization (L.kinematics H S)) L.rate hmat

/-- The original local gas energy is integrable against the actual cutoff at
each center. On the ball this follows from joint continuity on the PSD cone. -/
theorem CoulombGasInputs.local_cutoff_integrable (L : CoulombGasInputs η K) (H : FiniteEnergyInputs)
    (S : SobolevDifferenceQuotients) {D N : Density} (eq : N.matrix =ᵐ[volume] D.matrix)
    (hc : Continuous N.matrix) {φ : Phase} {p : ℝ} (hφ : φ.Regular p)
    (P : TileProfile) (c : Position) (σ R : ℝ) (hR : 0 < R)
    (support : ∀ x, P.cutoff (c-x) ≠ 0 → x ∈ Metric.closedBall c R) :
    Integrable (fun x => (σ*localEnergy (referenceEnergies energy η) D φ x)*P.cutoff (c-x)) := by
  let F := referenceEnergies energy η
  let f := fun x => σ*localEnergy F N φ x
  have hfield : Continuous (fun x => (⟨N.matrix x, N.positive x⟩ : {A : SpinMatrix // A.PosSemidef})) :=
    hc.subtype_mk _
  let fields := fun x => ((⟨N.matrix x, N.positive x⟩ : {A : SpinMatrix // A.PosSemidef}), φ.grad x)
  have hfields : Continuous fields := hfield.prodMk hφ.continuous_grad
  let gas := fun z : {A : SpinMatrix // A.PosSemidef} × Position => sswEnergy energy η z.1.val z.2
  have hgas : Continuous gas := continuous_coulomb_gas L H S
  have hloc : Continuous f := by
    change Continuous (fun x => σ * (gas ∘ fields) x)
    exact (continuous_const (y := σ)).mul (hgas.comp hfields)
  obtain ⟨z,hz,hm⟩ := (isCompact_closedBall c R).exists_isMaxOn ⟨c,Metric.mem_closedBall_self hR.le⟩ hloc.abs.continuousOn
  have bound (x : Position) (hx : P.cutoff (c-x) ≠ 0) : |f x| ≤ |f z| :=
    isMaxOn_iff.mp hm x (support x hx)
  have hi := (bounded_cutoff_integral (f := f) P c hloc.aestronglyMeasurable (abs_nonneg (f z))
    (ae_of_all _ bound)).1
  exact hi.congr (eq.mono fun x hx => congrArg (fun A => (σ*F.ssw A (φ.grad x))*P.cutoff (c-x)) hx)

end TSGA.ManyBody
