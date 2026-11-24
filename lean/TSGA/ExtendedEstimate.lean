import TSGA.MainTheorem
import TSGA.ErrorDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Theorem 3.3 with extended phase-error integrals

Only the phase kinetic energy is required to be finite in the hypotheses.
The Hessian and active-set errors are nonnegative Lebesgue integrals. If
either is infinite, the right-hand side of the estimate is `⊤`. In both
cases the local SSW energy is integrable.
-/

noncomputable section

namespace TSGA

open Filter MeasureTheory TSGA.Localization

/-- The weaker phase class for the extended estimate, with local Sobolev control of
the matrix root only where the gradient of the phase is nonzero. -/
structure ManuscriptPhase (D : Density) (p : ℝ) (φ : Phase) (G : MatrixGradient) : Prop where
  regular : φ.Regular p
  root_regular : RootRegularOn φ.active D p G
  kinetic : Integrable fun x => D.charge x * ‖φ.grad x‖ ^ 2

/-- Finiteness of the two potentially divergent phase remainders, measured
by their extended nonnegative integrals over the stated domains. -/
def PhaseRemaindersFinite (D : Density) (p : ℝ) (φ : Phase) (G : MatrixGradient) : Prop :=
  (∫⁻ x, ENNReal.ofReal (D.charge x * φ.hessianNorm x ^ p)) < ⊤ ∧
  (∫⁻ x in φ.active, ENNReal.ofReal (‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p)) < ⊤

/-- All error coefficients are strictly positive in the quantified theorem.
Thus the extended total equals its real formula precisely in the finite case. -/
def withPhaseRemainders (D : Density) (p : ℝ) (φ : Phase) (G : MatrixGradient)
    (finiteError : ℝ) : WithTop ℝ := by
  classical
  exact if PhaseRemaindersFinite D p φ G then ↑finiteError else ⊤

/-- At zero phase the extended convention gives the ordinary LSDA right-hand
side for every matrix gradient witness. -/
@[simp] theorem withPhaseRemainders_zero (D : Density) {p : ℝ} (hp : 0 < p)
    (G : MatrixGradient) (rhs : ℝ) : withPhaseRemainders D p Phase.zero G rhs = ↑rhs := by
  have hfin : PhaseRemaindersFinite D p Phase.zero G := by
    simp [PhaseRemaindersFinite, Phase.zero, Phase.hessianNorm, Real.zero_rpow hp.ne']
  simp [withPhaseRemainders, hfin]

private theorem curvature_measurable {D : Density} {p θ : ℝ} {φ : Phase} {S T : MatrixGradient}
    (hp : 0 < p) (hD : DensityRegular D p θ S T) (hr : φ.Regular p) :
    AEStronglyMeasurable (fun x => D.charge x * φ.hessianNorm x ^ p) volume := by
  have hh (i j : Fin 3) : AEMeasurable (fun x => φ.hessian x i j) volume :=
    (locallyIntegrableOn_univ.mp (hr.weak_hessian i j).2.1).aestronglyMeasurable.aemeasurable
  have hs : AEMeasurable (fun x => ∑ i, ∑ j, φ.hessian x i j ^ 2) volume :=
    Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => (hh i j).pow_const 2
  have hn : AEMeasurable φ.hessianNorm volume :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hs
  exact (hD.charge_L1.aestronglyMeasurable.aemeasurable.mul
    ((Real.continuous_rpow_const hp.le).measurable.comp_aemeasurable hn)).aestronglyMeasurable

private theorem root_weight_measurable {D : Density} {p : ℝ} {φ : Phase} {G : MatrixGradient}
    (hp : 0 < p) (hφ : ManuscriptPhase D p φ G) :
    AEStronglyMeasurable (fun x => ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p)
      (volume.restrict φ.active) := by
  have hloc : LocallyIntegrableOn (fun x => matrixGradNorm G x ^ p) φ.active := by
    intro x hx
    obtain ⟨r, hr, _, _, _, hLp⟩ := hφ.root_regular x hx
    refine ⟨Metric.ball x r, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr), ?_⟩
    change Integrable (fun y => matrixGradNorm G y ^ p) (volume.restrict (Metric.ball x r))
    have hn (y : Position) : ‖matrixGradNorm G y‖ = matrixGradNorm G y :=
      Real.norm_of_nonneg (Real.sqrt_nonneg _)
    simpa only [hn, ENNReal.toReal_ofReal hp.le] using
      hLp.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  exact ((hφ.regular.continuous_grad.norm.pow 2).aestronglyMeasurable).mul hloc.aestronglyMeasurable

/-- Finiteness of the extended phase integrals recovers the hypotheses used
by the finite-volume localization proof. -/
theorem ManuscriptPhase.admissible_iff {D : Density} {p θ : ℝ} {φ : Phase}
    {S T G : MatrixGradient} (hφ : ManuscriptPhase D p φ G) (hp : 0 < p)
    (hD : DensityRegular D p θ S T) :
    PhaseAdmissible D p φ G ↔ PhaseRemaindersFinite D p φ G := by
  have hc : ∀ x, 0 ≤ D.charge x * φ.hessianNorm x ^ p := fun x =>
    mul_nonneg (D.charge_nonneg x) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hw : ∀ x, 0 ≤ ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p := fun x =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hci := hasFiniteIntegral_iff_ofReal (f := fun x => D.charge x * φ.hessianNorm x ^ p)
    (μ := volume) (ae_of_all _ hc)
  have hwi := hasFiniteIntegral_iff_ofReal (f := fun x => ‖φ.grad x‖ ^ 2 * matrixGradNorm G x ^ p)
    (μ := volume.restrict φ.active) (ae_of_all _ hw)
  constructor
  · intro h
    exact ⟨hci.mp h.curvature.2, hwi.mp h.root_weighted.2⟩
  · rintro ⟨c, w⟩
    exact ⟨hφ.regular, hφ.root_regular, hφ.kinetic,
      ⟨curvature_measurable hp hD hφ.regular, hci.mpr c⟩,
      ⟨root_weight_measurable hp hφ, hwi.mpr w⟩⟩

private theorem extended_bound {D : Density} {p θ : ℝ} {φ : Phase} {S T G : MatrixGradient}
    {err rhs : ℝ} (hp : 0 < p) (hD : DensityRegular D p θ S T) (hφ : ManuscriptPhase D p φ G)
    (h : PhaseAdmissible D p φ G → err ≤ rhs) :
    (err : WithTop ℝ) ≤ withPhaseRemainders D p φ G rhs := by
  classical
  by_cases hfin : PhaseRemaindersFinite D p φ G
  · simpa [withPhaseRemainders, hfin] using h ((hφ.admissible_iff hp hD).mpr hfin)
  · simp [withPhaseRemainders, hfin]

/-- The standard bound, allowing infinite phase remainders. -/
def ExtendedTSGAEstimate (F : GasEnergies) (classOf : Density → Prop) (p θ b C : ℝ) : Prop :=
  ∀ (D : Density) (S T : MatrixGradient), classOf D → DensityRegular D p θ S T →
    ∀ (φ : Phase) (G : MatrixGradient), ManuscriptPhase D p φ G → ∀ ε : ℝ, 0 < ε →
      Integrable (localEnergy F D φ) ∧
      (↑|rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| : WithTop ℝ) ≤
        withPhaseRemainders D p φ G (tsgaError D φ S T G p b C ε)

/-- The global-root alternative with the same convention for the two phase
remainders. Its extra unweighted root integral is finite by the global Lᵖ hypothesis. -/
def ExtendedSharpTSGAEstimate (F : GasEnergies) (p θ C : ℝ) : Prop :=
  ∀ (D : Density) (S T G : MatrixGradient), DensityRegular D p θ S T →
    IsMatrixGradientOn Set.univ (D.power (1 / p)) G → MemLp (matrixGradNorm G) (ENNReal.ofReal p) →
    ∀ (φ : Phase), ManuscriptPhase D p φ G → ∀ ε : ℝ, 0 < ε →
      Integrable (localEnergy F D φ) ∧
      (↑|rotatedEnergy F D φ - ∫ x, localEnergy F D φ x| : WithTop ℝ) ≤
        withPhaseRemainders D p φ G (tsgaError D φ S T G p (2 * p - 1) C ε +
          C / ε ^ (2 * p - 1) * (∫ x, matrixGradNorm G x ^ p))

theorem TSGAEstimate.extended {F : GasEnergies} {A p θ b C : ℝ} {classOf : Density → Prop}
    (h : TSGAEstimate F classOf p θ b C) (H : APriori F A) (hp : 3 < p) (hθ : 0 < θ) :
    ExtendedTSGAEstimate F classOf p θ b C := by
  intro D S T hclass hD φ G hφ ε hε
  refine ⟨H.integrable_local hp hθ hD hφ.regular hφ.kinetic, extended_bound (by linarith) hD hφ ?_⟩
  exact fun hadm => (h D S T hclass hD φ G hadm ε hε).2

theorem SharpTSGAEstimate.extended {F : GasEnergies} {A p θ C : ℝ}
    (h : SharpTSGAEstimate F p θ C) (H : APriori F A) (hp : 3 < p) (hθ : 0 < θ) :
    ExtendedSharpTSGAEstimate F p θ C := by
  intro D S T G hD hG hLp φ hφ ε hε
  refine ⟨H.integrable_local hp hθ hD hφ.regular hφ.kinetic, extended_bound (by linarith) hD hφ ?_⟩
  exact fun hadm => (h D S T G hD hG hLp φ hadm ε hε).2

/-- The two estimates of Theorem 3.3 and the positive-minority strengthening,
allowing an infinite phase remainder. -/
structure MainExtendedTSGAEstimate (F : GasEnergies) : Prop where
  general : ∀ p θ : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p * θ →
    ∃ C > 0, ExtendedTSGAEstimate F (fun _ => True) p θ (bulkExponent p θ) C
  minority : ∀ p θ ν : ℝ, 3 < p → 0 < θ → θ < 1 → 2 ≤ p * θ →
    0 < ν → ν ≤ 1 / 2 → ∃ C > 0,
      ExtendedTSGAEstimate F (MinorityBound ν) p θ (polarizedBulkExponent p θ) C
  sharp : ∀ p : ℝ, 3 < p → ∃ C > 0, ∀ θ : ℝ, 0 < θ → θ < 1 → 2 ≤ p * θ →
    ExtendedSharpTSGAEstimate F p θ C

theorem extended_of_mainTSGA {F : GasEnergies} {A : ℝ} (h : MainTSGAEstimate F) (H : APriori F A) :
    MainExtendedTSGAEstimate F where
  general p θ hp hθ hθ' hθp := by
    obtain ⟨C, hC, hbound⟩ := h.general p θ hp hθ hθ' hθp
    exact ⟨C, hC, hbound.extended H hp hθ⟩
  minority p θ ν hp hθ hθ' hθp hν hν' := by
    obtain ⟨C, hC, hbound⟩ := h.minority p θ ν hp hθ hθ' hθp hν hν'
    exact ⟨C, hC, hbound.extended H hp hθ⟩
  sharp p hp := by
    obtain ⟨C, hC, hbound⟩ := h.sharp p hp
    exact ⟨C, hC, fun θ hθ hθ' hθp => (hbound θ hθ hθ' hθp).extended H hp hθ⟩

/-- Restrict the extended estimates to finite phase remainders, preserving
each constant. This lets the physical theorem feed the LSDA and its rescaling. -/
theorem MainExtendedTSGAEstimate.toFinite {F : GasEnergies} (H : MainExtendedTSGAEstimate F) :
    MainTSGAEstimate F := by
  have finiteBound {classOf : Density → Prop} {p θ b C : ℝ} (hp : 0 < p)
      (h : ExtendedTSGAEstimate F classOf p θ b C) : TSGAEstimate F classOf p θ b C := by
    intro D S T hc hD φ G hφ ε hε
    let phase : ManuscriptPhase D p φ G := ⟨hφ.regular, hφ.root_regular, hφ.kinetic⟩
    obtain ⟨hi, hb⟩ := h D S T hc hD φ G phase ε hε
    exact ⟨hi, by simpa [withPhaseRemainders, (phase.admissible_iff hp hD).mp hφ,
      rotatedEnergy, localEnergy] using hb⟩
  constructor
  · intro p θ hp hθ hθ' hpθ
    obtain ⟨C, hC, h⟩ := H.general p θ hp hθ hθ' hpθ
    exact ⟨C, hC, finiteBound (by linarith) h⟩
  · intro p θ ν hp hθ hθ' hpθ hν hν'
    obtain ⟨C, hC, h⟩ := H.minority p θ ν hp hθ hθ' hpθ hν hν'
    exact ⟨C, hC, finiteBound (by linarith) h⟩
  · intro p hp
    obtain ⟨C, hC, h⟩ := H.sharp p hp
    refine ⟨C, hC, ?_⟩
    intro θ hθ hθ' hpθ D S T G hD hw hG φ hφ ε hε
    let phase : ManuscriptPhase D p φ G := ⟨hφ.regular, hφ.root_regular, hφ.kinetic⟩
    obtain ⟨hi, hb⟩ := h θ hθ hθ' hpθ D S T G hD hw hG φ phase ε hε
    have hfin := (phase.admissible_iff (by linarith) hD).mp hφ
    simp only [withPhaseRemainders, hfin, ↓reduceIte, WithTop.coe_le_coe, rotatedEnergy, localEnergy] at hb
    exact ⟨hi, hb⟩

end TSGA
