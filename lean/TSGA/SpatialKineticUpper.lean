import TSGA.SpatialDensity
import TSGA.LayerGradient

/-! # The kinetic upper bound in arbitrary positive spatial dimension

The scalar smoothing profiles are independent of the density. The trace identity for
localized Fermi projectors supplies a fermionic trial with the prescribed diagonal.
The Hilbert–Schmidt layer estimate and the passage to the kinetic infimum are derived below.
-/

noncomputable section
namespace TSGA.ManyBody.Spatial

open MeasureTheory Set TSGA.Localization
open scoped ComplexOrder

variable {d : ℕ}

/-- The volume form of the semiclassical constant, using the unit momentum ball. -/
def thomasFermi (d : ℕ) : ℝ :=
  4 * Real.pi^2 * d / (d + 2 : ℝ) *
    ((volume.real (Metric.ball (0 : Point d) 1))⁻¹) ^ (2 / (d : ℝ))

theorem thomasFermi_nonneg (d : ℕ) : 0 ≤ thomasFermi d := by
  unfold thomasFermi
  positivity

def traceMoment (D : Density d) (a : ℝ) : ℝ := ∫ x, (D.power a x).trace.re

theorem tracePower_eq_sum (D : Density d) (x : Point d) (a : ℝ) :
    (D.power a x).trace.re = ∑ i, (D.positive x).isHermitian.eigenvalues i ^ a := by
  rw [Density.power, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal, Fin.sum_univ_two]

theorem traceMoment_nonneg (D : Density d) (a : ℝ) : 0 ≤ traceMoment D a := by
  apply integral_nonneg
  intro x
  change 0 ≤ (D.power a x).trace.re
  rw [tracePower_eq_sum]
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg ((D.positive x).eigenvalues_nonneg i) _

/-- Both spin-degeneracy factors in the comparison with the scalar density. -/
theorem trace_power_comparison (D : Density d) (x : Point d) {a : ℝ} (ha : 1 ≤ a) :
    2 ^ (1-a) * D.charge x ^ a ≤ (D.power a x).trace.re ∧
    (D.power a x).trace.re ≤ D.charge x ^ a := by
  rw [tracePower_eq_sum, Fin.sum_univ_two, Density.charge, (D.positive x).1.trace_eq_sum_eigenvalues,
    Fin.sum_univ_two, Complex.add_re]
  let e := (D.positive x).1.eigenvalues
  have h₀ := (D.positive x).eigenvalues_nonneg (0 : Fin 2)
  have h₁ := (D.positive x).eigenvalues_nonneg (1 : Fin 2)
  change 2 ^ (1-a) * (e 0 + e 1) ^ a ≤ (e 0)^a + (e 1)^a ∧ _
  refine ⟨?_, Real.add_rpow_le_rpow_add h₀ h₁ ha⟩
  have h : (e 0 + e 1)^a ≤ (2:ℝ)^(a-1)*((e 0)^a + (e 1)^a) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ⟨e 0, h₀⟩ ⟨e 1, h₁⟩ ha
  rw [show 1-a = -(a-1) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    inv_mul_eq_div]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)).2 (by linarith)

def trialMoment (d : ℕ) (η : ℝ → ℝ) : ℝ := ∫ t in Ioi (0:ℝ), η t * t ^ (2/(d:ℝ))

def layerAmplitude (η : ℝ → ℝ) (D : Density d) (t : ℝ) (x : Point d) : SpinMatrix :=
  (D.positive x).isHermitian.cfc (fun r => profileAt η r t)

def layerCost (V : ℝ → Gradient d) (x : Point d) : ℝ := ∫ t, kineticDensity (V t) x ∂profileMeasure

/-- This two-point inequality uses only the pair of matrix values and their positivity.
Evaluating the existing spectral lemma on a two-valued field reuses its full proof. -/
theorem layer_distance {η : ℝ → ℝ} (der : DilationDerivative η) (D : Density d) (x y : Point d) :
    Integrable (fun t => hilbertSchmidt (layerAmplitude η D t x - layerAmplitude η D t y)^2) profileMeasure ∧
    (∫ t, hilbertSchmidt (layerAmplitude η D t x - layerAmplitude η D t y)^2 ∂profileMeasure) ≤
      trialStiffness η * hilbertSchmidt (D.power (1/2) x - D.power (1/2) y)^2 := by
  classical
  obtain ⟨z, hz⟩ := exists_ne (0:Position)
  let select (v : Position) := if v = 0 then x else y
  let pair : TSGA.Density := ⟨fun v => D.matrix (select v), fun v => D.positive (select v)⟩
  have pull (v w : Position) : Integrable (fun t => hilbertSchmidt
      (layerAmplitude η D t (select v) - layerAmplitude η D t (select w))^2) profileMeasure ∧
      (∫ t, hilbertSchmidt (layerAmplitude η D t (select v) - layerAmplitude η D t (select w))^2 ∂profileMeasure) ≤
        trialStiffness η * hilbertSchmidt (D.power (1/2) (select v) - D.power (1/2) (select w))^2 :=
    layer_matrix_distance der pair v w
  have h := pull 0 z
  simpa only [show select 0 = x by simp [select], show select z = y by simp [select, hz]] using h

structure FamilyMeasurable (F : ℝ → Point d → SpinMatrix) (V : ℝ → Gradient d) : Prop where
  value : ∀ j k, AEStronglyMeasurable (fun z : Point d × ℝ => F z.2 z.1 j k) (volume.prod profileMeasure)
  gradient : ∀ i j k, AEStronglyMeasurable (fun z : Point d × ℝ => V z.2 z.1 i j k) (volume.prod profileMeasure)

/-- The Hilbert-valued Sobolev composition theorem, for arbitrary fields. -/
def FamilySobolevComposition (d : ℕ) : Prop :=
  ∀ (u : Point d → SpinMatrix) (F : ℝ → Point d → SpinMatrix) (S : Gradient d)
    (V : ℝ → Gradient d) (L : ℝ), 0 ≤ L → IsMatrixGradient u S →
    (∀ t > 0, IsMatrixGradient (F t) (V t)) → FamilyMeasurable F V →
    (∀ x y, Integrable (fun t => hilbertSchmidt (F t x-F t y)^2) profileMeasure ∧
      (∫ t, hilbertSchmidt (F t x-F t y)^2 ∂profileMeasure) ≤ L * hilbertSchmidt (u x-u y)^2) →
    ∀ᵐ x, layerCost V x ≤ L * kineticDensity S x

/-- Compactly supported scalar profiles from the projector construction. -/
structure LayerProfile (η : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ η t
  compact : HasCompactSupport η
  positive_support : tsupport η ⊆ Ioi 0
  lipschitz : ∃ L, LipschitzWith L (fun t => √(η t))
  mass : (∫ t in Ioi (0:ℝ), η t) = 1
  pauli : (∫ t in Ioi (0:ℝ), η t/t) ≤ 1

/-- The diagonal obtained by integrating the squared spectral amplitudes. -/
def layerDiagonal (η : ℝ → ℝ) (D : Density d) (x : Point d) : SpinMatrix :=
  (D.positive x).1.cfc (fun r => ∫ t, (profileAt η r t)^2 ∂profileMeasure)

theorem layerDiagonal_eq {η : ℝ → ℝ} (hη : LayerProfile η) (D : Density d) (x : Point d) :
    layerDiagonal η D x = D.matrix x := by
  have scalar (r : ℝ) (hr : 0 ≤ r) : (∫ t, (profileAt η r t)^2 ∂profileMeasure) = r := by
    rcases hr.eq_or_lt with h | h
    · simp [← h, profileAt]
    · simp only [profileAt, h.ne', ↓reduceIte, Real.sq_sqrt (hη.nonneg _)]
      change (∫ t in Ioi (0:ℝ), η (t/r)) = r
      simp only [div_eq_mul_inv, mul_comm _ r⁻¹]
      rw [integral_comp_mul_left_Ioi η 0 (inv_pos.mpr h)]
      simp [hη.mass]
  let A := (D.positive x).1
  refine Eq.trans ?_ A.spectral_theorem.symm
  apply congrArg (Unitary.conjStarAlgAut ℂ SpinMatrix A.eigenvectorUnitary)
  apply congrArg Matrix.diagonal
  funext i
  exact congrArg Complex.ofReal (scalar _ ((D.positive x).eigenvalues_nonneg i))

/-- Scalar profile estimates from the smoothing construction of Lewin–Lieb–Seiringer. -/
def SmoothingProfiles (d : ℕ) (κ₁ κ₂ : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ η : ℝ → ℝ,
  LayerProfile η ∧
  Nonempty (DilationDerivative η) ∧ Integrable (fun t => η t * t^(2/(d:ℝ))) profileMeasure ∧
  trialMoment d η ≤ 1 + κ₁ * ε ∧
  trialStiffness η ≤ κ₂ * (1 + √ε)^2 / ε

/-- The diagonal and kinetic trace identities of the localized Fermi projector trial.
The spatial profile-gradient integral is left unevaluated. -/
def ProjectorTraceIdentity (d : ℕ) : Prop := ∀ (D : Density d) (S : Gradient d), SqrtRegular D S →
  ∀ η : ℝ → ℝ, LayerProfile η →
  DilationDerivative η → Integrable (fun t => η t * t^(2/(d:ℝ))) profileMeasure →
  ∃ (γ : OneBody d) (V : ℝ → Gradient d), γ.matrixDensity =ᵐ[volume] layerDiagonal η D ∧
    (∀ t > 0, IsMatrixGradient (layerAmplitude η D t) (V t)) ∧ FamilyMeasurable (layerAmplitude η D) V ∧
    Integrable (layerCost V) ∧ γ.kinetic = (∫ x, layerCost V x) +
      thomasFermi d * traceMoment D (1 + 2/(d:ℝ)) * trialMoment d η

/-- The upper kinetic bound, with constants chosen before the density and the scale.
The same construction supplies a finite-energy representative at the prescribed density. -/
theorem kinetic_upper (hd : 0 < d) (sob : FamilySobolevComposition d)
    (projectors : ProjectorTraceIdentity d)
    (profiles : ∀ d : ℕ, 0 < d → ∃ κ₁ > 0, ∃ κ₂ > 0, SmoothingProfiles d κ₁ κ₂) :
    ∃ κ₁ > 0, ∃ κ₂ > 0, ∀ (D : Density d) (S : Gradient d), SqrtRegular D S →
      ∀ ε : ℝ, 0 < ε → (∃ γ : OneBody d, γ.matrixDensity =ᵐ[volume] D.matrix) ∧
        bestKinetic D.matrix ≤ thomasFermi d * (1+κ₁*ε) * traceMoment D (1+2/(d:ℝ)) +
          κ₂ * (1+√ε)^2 / ε * sqrtKinetic S := by
  obtain ⟨κ₁, h₁, κ₂, h₂, P⟩ := profiles d hd
  refine ⟨κ₁, h₁, κ₂, h₂, ?_⟩
  intro D S hD ε hε
  obtain ⟨η, hη, ⟨der⟩, intη, moment, stiff⟩ := P ε hε
  obtain ⟨γ, V, diag, weak, meas, intV, trace⟩ := projectors D S hD η hη der intη
  have density := diag.trans (Filter.Eventually.of_forall (layerDiagonal_eq hη D))
  refine ⟨⟨γ, density⟩, (bestKinetic_le density).trans ?_⟩
  have gradient := sob (D.power (1/2)) (layerAmplitude η D) S V (trialStiffness η)
    (trialStiffness_nonneg η) hD.weak weak meas (layer_distance der D)
  have intS : Integrable (kineticDensity S) := by
    simpa only [Real.sq_sqrt (kineticDensity_nonneg S _)] using hD.grad.integrable_sq
  have bound := integral_mono_ae intV (intS.const_mul _) gradient
  rw [integral_const_mul] at bound
  change _ ≤ trialStiffness η * sqrtKinetic S at bound
  have hs : 0 ≤ sqrtKinetic S := integral_nonneg (kineticDensity_nonneg S)
  have cost := mul_le_mul_of_nonneg_right stiff hs
  have phaseSpace := mul_le_mul_of_nonneg_left moment
    (mul_nonneg (thomasFermi_nonneg d) (traceMoment_nonneg D (1+2/(d:ℝ))))
  rw [trace]
  linarith only [bound, cost, phaseSpace]

end TSGA.ManyBody.Spatial
