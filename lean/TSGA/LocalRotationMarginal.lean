import TSGA.GaugeEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Nonnegative one-particle multiplication observables on Coulomb sectors -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

def Wave.localMassDensity {n : ℕ} (ψ : Wave n) (w : Position → ℝ) (x : Space n) : ℝ :=
  ∑ i, w (x i) * ∑ s, ‖ψ.value s x‖^2

def PureState.localMass (p : PureState) (w : Position → ℝ) : ℝ := match p with
  | .vacuum => 0
  | .occupied ψ => ∫ x, ψ.localMassDensity w x

def PureState.localMassFinite (p : PureState) (w : Position → ℝ) : Prop := match p with
  | .vacuum => True
  | .occupied ψ => Integrable (ψ.localMassDensity w)

theorem Wave.localMassDensity_nonneg {n : ℕ} (ψ : Wave n) {w : Position → ℝ} (h : ∀ x, 0 ≤ w x)
    (x : Space n) : 0 ≤ ψ.localMassDensity w x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (h (x i)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem PureState.localMass_nonneg (p : PureState) {w : Position → ℝ} (h : ∀ x, 0 ≤ w x) :
    0 ≤ p.localMass w := by
  cases p with
  | vacuum => exact le_rfl
  | occupied ψ => exact integral_nonneg (ψ.localMassDensity_nonneg h)

/-- The spatial marginal identity against a nonnegative scalar test. Finite
expectation implies integrability in every sector with positive weight.
This is Fubini–Tonelli and permutation symmetry of the spatial spin sum. -/
def LocalScalarMarginal : Prop := ∀ (Γ : MixedState) (D : Density), feasible D.matrix Γ →
  ∀ (w : Position → ℝ), AEMeasurable w volume → (∀ x, 0 ≤ w x) → Integrable (fun x => D.charge x*w x) →
    (∀ k, 0 < Γ.weight k → (Γ.component k).localMassFinite w) ∧
      HasSum (fun k => Γ.weight k*(Γ.component k).localMass w) (∫ x, D.charge x*w x)

/-- Ordinary open neighborhoods and the zero extension of an H¹ function
supported in a closed ball give the two local Sobolev domains used here. -/
def LocalRotationDomain (D : Density) (O : Set Position) : Prop :=
  (IsOpen O ∧ tsupport D.charge ⊆ O) ∨
    ∃ c r, 0 < r ∧ O = Metric.closedBall c r ∧ ∀ x ∉ O, D.charge x = 0

theorem LocalRotationDomain.measurableSet {D : Density} {O} (h : LocalRotationDomain D O) : MeasurableSet O := by
  rcases h with ⟨ho,_⟩ | ⟨_,_,_,rfl,_⟩
  · exact ho.measurableSet
  · exact Metric.isClosed_closedBall.measurableSet

def PureState.localizedOn (p : PureState) (K : Set Position) : Prop := match p with
  | .vacuum => True
  | .occupied ψ => ∀ᵐ x, ∀ i, x i ∉ K → ∀ s, ψ.value s x = 0

theorem LocalScalarMarginal.localized {Γ : MixedState} {D : Density} (m : LocalScalarMarginal)
    (hΓ : feasible D.matrix Γ) (k : ℕ) (hk : 0 < Γ.weight k) :
    (Γ.component k).localizedOn (tsupport D.charge) := by
  classical
  let K := tsupport D.charge
  let f : Position → ℝ := Kᶜ.indicator (fun _ => 1)
  have hf (x) : 0 ≤ f x := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hz (x) : D.charge x*f x = 0 := by
    by_cases h : x ∈ K
    · simp [f,h]
    · rw [image_eq_zero_of_notMem_tsupport h,zero_mul]
  have hm : MeasurableSet K := (isClosed_tsupport D.charge).measurableSet
  obtain ⟨finite,hs⟩ := m Γ D hΓ f (measurable_const.indicator hm.compl).aemeasurable hf (by simp only [hz]; simp)
  have sumzero : (∑' l, Γ.weight l*(Γ.component l).localMass f) = 0 := by simpa only [hz,integral_zero] using hs.tsum_eq
  have hn l := mul_nonneg (Γ.weight_nonneg l) ((Γ.component l).localMass_nonneg hf)
  have hle := hs.summable.le_tsum k (fun l _ => hn l)
  rw [sumzero] at hle
  have hzero := (mul_eq_zero.mp (le_antisymm hle (hn k))).resolve_left hk.ne'
  have hi := finite k hk
  generalize hp : Γ.component k = p at hi hzero ⊢
  cases p with
  | vacuum => trivial
  | occupied ψ =>
    have hvanish := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (ψ.localMassDensity_nonneg hf)) hi).mp hzero
    filter_upwards [hvanish] with x hx
    intro i hxi s
    have hslot := Finset.single_le_sum (f := fun l => f (x l)*∑ a, ‖ψ.value a x‖^2)
      (fun l _ => mul_nonneg (hf _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
    have hentry := Finset.single_le_sum (f := fun a => ‖ψ.value a x‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ s)
    change ψ.localMassDensity f x = 0 at hx
    change _ ≤ ψ.localMassDensity f x at hslot
    rw [hx, show f (x i) = 1 from Set.indicator_of_mem hxi _,one_mul] at hslot
    exact norm_eq_zero.mp (by nlinarith only [hentry,hslot,norm_nonneg (ψ.value s x)])

end TSGA.ManyBody
