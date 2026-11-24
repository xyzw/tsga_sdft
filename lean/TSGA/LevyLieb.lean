import TSGA.Sobolev
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! # The grand-canonical Levy–Lieb functional in three dimensions

A mixed state has a countable spectral decomposition into normalized pure
states in particle-number sectors. Spatial integrals are Lebesgue integrals
and the two spin coordinates carry counting measure. The density constraint
in the search is imposed up to almost-everywhere equality.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory
open scoped ContDiff ComplexConjugate

abbrev Space (n : ℕ) := Fin n → Position
abbrev Spins (n : ℕ) := Fin n → Fin 2

/-- Integrate over the positions and sum over all spin configurations. -/
def sectorIntegral {n : ℕ} (f : Spins n → Space n → ℝ) : ℝ := ∑ s, ∫ x, f s x

def coulomb {n : ℕ} (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Iio i, (‖x i - x j‖)⁻¹

theorem coulomb_nonneg {n : ℕ} (x : Space n) : 0 ≤ coulomb x := by
  unfold coulomb
  positivity

/-- A coordinate vector for the jth component of particle i. -/
def particleDirection {n : ℕ} (i : Fin n) (j : Fin 3) : Space n :=
  Pi.single i (PiLp.single 2 j 1)

/-- Normalized fermionic wavefunction with its distributional first derivatives.
Finite Coulomb and kinetic expectations make it an admissible pure trial state. -/
structure Wave (n : ℕ) where
  value : Spins n → Space n → ℂ
  gradient : Spins n → Space n → Fin n → Fin 3 → ℂ
  antisymmetric : ∀ (π : Equiv.Perm (Fin n)) s, ∀ᵐ x ∂(volume : Measure (Space n)),
    value (s ∘ π) (x ∘ π) = ((Equiv.Perm.sign π : ℤˣ) : ℤ) * value s x
  square_integrable : ∀ s, MemLp (value s) 2 volume
  normalized : sectorIntegral (fun s x => ‖value s x‖ ^ 2) = 1
  gradient_L2 : ∀ s i j, MemLp (fun x => gradient s x i j) 2 volume
  weak_gradient : ∀ s i j (ψ : Space n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ x, (fderiv ℝ ψ x (particleDirection i j)) • value s x) =
      -(∫ x, ψ x • gradient s x i j)
  interaction_integrable : ∀ s, Integrable (fun x => coulomb x * ‖value s x‖ ^ 2)

def Wave.kinetic {n : ℕ} (ψ : Wave n) : ℝ :=
  sectorIntegral fun s x => ∑ i, ∑ j, ‖ψ.gradient s x i j‖ ^ 2

def Wave.interaction {n : ℕ} (ψ : Wave n) : ℝ :=
  sectorIntegral fun s x => coulomb x * ‖ψ.value s x‖ ^ 2

/-- The first-coordinate marginal of a normalized antisymmetric wavefunction
in the (n+1)-particle sector, with the usual particle-number factor. -/
def Wave.matrixDensity {n : ℕ} (ψ : Wave (n+1)) (x : Position) : SpinMatrix := fun i j =>
  (n+1 : ℕ) * ∑ s : Spins n, ∫ y : Space n,
    ψ.value (Fin.cons i s) (Fin.cons x y) * conj (ψ.value (Fin.cons j s) (Fin.cons x y))

inductive PureState where
  | vacuum
  | occupied {n : ℕ} (ψ : Wave (n+1))

def PureState.matrixDensity : PureState → Position → SpinMatrix
  | .vacuum => 0
  | .occupied ψ => ψ.matrixDensity

def PureState.kinetic : PureState → ℝ
  | .vacuum => 0
  | .occupied ψ => ψ.kinetic

def PureState.interaction : PureState → ℝ
  | .vacuum => 0
  | .occupied ψ => ψ.interaction

def PureState.particles : PureState → ℕ
  | .vacuum => 0
  | .occupied (n := n) _ => n + 1

theorem PureState.kinetic_nonneg (s : PureState) : 0 ≤ s.kinetic := by
  cases s with
  | vacuum => exact le_rfl
  | occupied ψ =>
    exact Finset.sum_nonneg fun _ _ => integral_nonneg fun x =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem PureState.interaction_nonneg (s : PureState) : 0 ≤ s.interaction := by
  cases s with
  | vacuum => exact le_rfl
  | occupied ψ =>
    exact Finset.sum_nonneg fun _ _ => integral_nonneg fun x => mul_nonneg (coulomb_nonneg x) (sq_nonneg _)

/-- Countable mixtures include the sectorwise spectral decompositions of
positive trace-class density operators. All expectations used in the search
are finite. -/
structure MixedState where
  component : ℕ → PureState
  weight : ℕ → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  normalized : HasSum weight 1
  particles_summable : Summable (fun k => weight k * (component k).particles)
  kinetic_summable : Summable (fun k => weight k * (component k).kinetic)
  interaction_summable : Summable (fun k => weight k * (component k).interaction)
  density_summable : ∀ᵐ x ∂(volume : Measure Position), ∀ i j,
    Summable (fun k => (weight k : ℂ) * (component k).matrixDensity x i j)

def MixedState.matrixDensity (Γ : MixedState) (x : Position) : SpinMatrix := fun i j =>
  ∑' k, (Γ.weight k : ℂ) * (Γ.component k).matrixDensity x i j

def MixedState.kinetic (Γ : MixedState) : ℝ := ∑' k, Γ.weight k * (Γ.component k).kinetic

def MixedState.interaction (Γ : MixedState) : ℝ := ∑' k, Γ.weight k * (Γ.component k).interaction

theorem MixedState.kinetic_nonneg (Γ : MixedState) : 0 ≤ Γ.kinetic :=
  tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) (Γ.component k).kinetic_nonneg

theorem MixedState.interaction_nonneg (Γ : MixedState) : 0 ≤ Γ.interaction :=
  tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) (Γ.component k).interaction_nonneg

def MixedState.vacuum : MixedState where
  component _ := .vacuum
  weight k := if k = 0 then 1 else 0
  weight_nonneg k := by split <;> norm_num
  normalized := by simpa using (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  particles_summable := by simp [PureState.particles]
  kinetic_summable := by simp [PureState.kinetic]
  interaction_summable := by simp [PureState.interaction]
  density_summable := by simp [PureState.matrixDensity]

/-- The Coulomb direct energy of the charge density. -/
def hartree (ρ : Position → ℝ) : ℝ :=
  (∫ x, ∫ y, ρ x * ρ y / ‖x - y‖) / 2

theorem hartree_congr {ρ σ : Position → ℝ} (h : ρ =ᵐ[volume] σ) : hartree ρ = hartree σ := by
  unfold hartree
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with x hx
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hx, hy]

def feasible (M : Position → SpinMatrix) (Γ : MixedState) : Prop := Γ.matrixDensity =ᵐ[volume] M

def levyLieb (M : Position → SpinMatrix) : ℝ :=
  sInf {e | ∃ Γ : MixedState, feasible M Γ ∧ e = Γ.kinetic + Γ.interaction}

def energy (M : Position → SpinMatrix) : ℝ := levyLieb M - hartree (fun x => (M x).trace.re)

/-- The extended functional assigns infinite energy to an empty feasible
set. The real functional used in the TSGA is its restriction to densities
which have finite-energy representatives. -/
def extendedEnergy (M : Position → SpinMatrix) : WithTop ℝ := by
  classical
  exact if ∃ Γ, feasible M Γ then ↑(energy M) else ⊤

theorem extendedEnergy_of_feasible {M : Position → SpinMatrix} (h : ∃ Γ, feasible M Γ) :
    extendedEnergy M = ↑(energy M) := by
  classical
  simp [extendedEnergy, h]

theorem energy_congr {M N : Position → SpinMatrix} (heq : M =ᵐ[volume] N) : energy M = energy N := by
  have hs : levyLieb M = levyLieb N := by
    apply congrArg sInf
    ext e
    exact ⟨fun ⟨Γ, hΓ, h⟩ => ⟨Γ, hΓ.trans heq, h⟩, fun ⟨Γ, hΓ, h⟩ => ⟨Γ, hΓ.trans heq.symm, h⟩⟩
  unfold energy
  rw [hs]
  congr 1
  exact hartree_congr (heq.mono fun x hx => congrArg (fun A : SpinMatrix => A.trace.re) hx)

theorem levyLieb_le {M : Position → SpinMatrix} {Γ : MixedState} (h : feasible M Γ) :
    levyLieb M ≤ Γ.kinetic + Γ.interaction := by
  unfold levyLieb
  apply csInf_le
  · exact ⟨0, fun e ⟨s, _, he⟩ => he ▸ add_nonneg s.kinetic_nonneg s.interaction_nonneg⟩
  · exact ⟨Γ, h, rfl⟩

theorem le_levyLieb {M : Position → SpinMatrix} {a : ℝ} (h : ∃ Γ, feasible M Γ)
    (hle : ∀ Γ, feasible M Γ → a ≤ Γ.kinetic + Γ.interaction) : a ≤ levyLieb M := by
  obtain ⟨Γ, hΓ⟩ := h
  exact le_csInf ⟨_, Γ, hΓ, rfl⟩ fun e ⟨s, hs, he⟩ => he ▸ hle s hs

theorem energy_vacuum : energy 0 = 0 := by
  have hv : feasible 0 MixedState.vacuum := by
    apply Filter.Eventually.of_forall
    intro x
    ext i j
    simp [MixedState.matrixDensity, MixedState.vacuum, PureState.matrixDensity]
  have hE : levyLieb 0 = 0 := by
    apply le_antisymm
    · simpa [MixedState.kinetic, MixedState.interaction, MixedState.vacuum,
        PureState.kinetic, PureState.interaction] using levyLieb_le hv
    · exact le_levyLieb ⟨_, hv⟩ fun Γ _ => add_nonneg Γ.kinetic_nonneg Γ.interaction_nonneg
  simp [energy, hE, hartree]

end TSGA.ManyBody
