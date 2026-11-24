import TSGA.SpatialKineticUpper
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-! # Grand-canonical Coulomb upper bound in finite spatial dimension

States are mixtures of antisymmetric wavefunctions on the particle sectors of `ℝᵈ`.
The direct and exchange terms are ordinary integrals for the kernel `1 / |x-y|`.
The quasi-free trace identity applies on the domain of finite direct energy.
-/

noncomputable section
namespace TSGA.ManyBody.Spatial

open MeasureTheory
open scoped ContDiff ComplexConjugate

abbrev Config (d n : ℕ) := Fin n → Point d
variable {d : ℕ}

/-- Integrate over the positions and sum over all spin configurations. -/
def sectorIntegral {n : ℕ} (f : Spins n → Config d n → ℝ) : ℝ := ∑ s, ∫ x, f s x

def coulomb {n : ℕ} (x : Config d n) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Iio i, (‖x i - x j‖)⁻¹

theorem coulomb_nonneg {n : ℕ} (x : Config d n) : 0 ≤ coulomb x := by
  unfold coulomb
  positivity

/-- A coordinate vector for the jth component of particle i. -/
def particleDirection {n : ℕ} (i : Fin n) (j : Fin d) : Config d n :=
  Pi.single i (PiLp.single 2 j 1)

/-- Normalized fermionic wavefunction with its distributional first derivatives.
Finite Coulomb and kinetic expectations make it an admissible pure trial state. -/
structure Wave (d n : ℕ) where
  value : Spins n → Config d n → ℂ
  gradient : Spins n → Config d n → Fin n → Fin d → ℂ
  antisymmetric : ∀ (π : Equiv.Perm (Fin n)) s, ∀ᵐ x ∂(volume : Measure (Config d n)),
    value (s ∘ π) (x ∘ π) = ((Equiv.Perm.sign π : ℤˣ) : ℤ) * value s x
  square_integrable : ∀ s, MemLp (value s) 2 volume
  normalized : sectorIntegral (fun s x => ‖value s x‖ ^ 2) = 1
  gradient_L2 : ∀ s i j, MemLp (fun x => gradient s x i j) 2 volume
  weak_gradient : ∀ s i j (ψ : Config d n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ x, (fderiv ℝ ψ x (particleDirection i j)) • value s x) =
      -(∫ x, ψ x • gradient s x i j)
  interaction_integrable : ∀ s, Integrable (fun x => coulomb x * ‖value s x‖ ^ 2)

def Wave.kinetic {n : ℕ} (ψ : Wave d n) : ℝ :=
  sectorIntegral fun s x => ∑ i, ∑ j, ‖ψ.gradient s x i j‖ ^ 2

def Wave.interaction {n : ℕ} (ψ : Wave d n) : ℝ :=
  sectorIntegral fun s x => coulomb x * ‖ψ.value s x‖ ^ 2

/-- The first-coordinate marginal of a normalized antisymmetric wavefunction
in the (n+1)-particle sector, with the usual particle-number factor. -/
def Wave.matrixDensity {n : ℕ} (ψ : Wave d (n+1)) (x : Point d) : SpinMatrix := fun i j =>
  (n+1 : ℕ) * ∑ s : Spins n, ∫ y : Config d n,
    ψ.value (Fin.cons i s) (Fin.cons x y) * conj (ψ.value (Fin.cons j s) (Fin.cons x y))

inductive PureState (d : ℕ) where
  | vacuum
  | occupied {n : ℕ} (ψ : Wave d (n+1))

def PureState.matrixDensity : PureState d → Point d → SpinMatrix
  | .vacuum => 0
  | .occupied ψ => ψ.matrixDensity

def PureState.kinetic : PureState d → ℝ
  | .vacuum => 0
  | .occupied ψ => ψ.kinetic

def PureState.interaction : PureState d → ℝ
  | .vacuum => 0
  | .occupied ψ => ψ.interaction

def PureState.particles : PureState d → ℕ
  | .vacuum => 0
  | .occupied (n := n) _ => n + 1

theorem PureState.kinetic_nonneg (s : PureState d) : 0 ≤ s.kinetic := by
  cases s with
  | vacuum => exact le_rfl
  | occupied ψ =>
    exact Finset.sum_nonneg fun _ _ => integral_nonneg fun x =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem PureState.interaction_nonneg (s : PureState d) : 0 ≤ s.interaction := by
  cases s with
  | vacuum => exact le_rfl
  | occupied ψ =>
    exact Finset.sum_nonneg fun _ _ => integral_nonneg fun x => mul_nonneg (coulomb_nonneg x) (sq_nonneg _)

/-- Countable mixtures include the sectorwise spectral decompositions of
positive trace-class density operators. All expectations used in the search
are finite. -/
structure MixedState (d : ℕ) where
  component : ℕ → PureState d
  weight : ℕ → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  normalized : HasSum weight 1
  particles_summable : Summable (fun k => weight k * (component k).particles)
  kinetic_summable : Summable (fun k => weight k * (component k).kinetic)
  interaction_summable : Summable (fun k => weight k * (component k).interaction)
  density_summable : ∀ᵐ x ∂(volume : Measure (Point d)), ∀ i j,
    Summable (fun k => (weight k : ℂ) * (component k).matrixDensity x i j)

def MixedState.matrixDensity (Γ : MixedState d) (x : Point d) : SpinMatrix := fun i j =>
  ∑' k, (Γ.weight k : ℂ) * (Γ.component k).matrixDensity x i j

def MixedState.kinetic (Γ : MixedState d) : ℝ := ∑' k, Γ.weight k * (Γ.component k).kinetic

def MixedState.interaction (Γ : MixedState d) : ℝ := ∑' k, Γ.weight k * (Γ.component k).interaction

theorem MixedState.kinetic_nonneg (Γ : MixedState d) : 0 ≤ Γ.kinetic :=
  tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) (Γ.component k).kinetic_nonneg

theorem MixedState.interaction_nonneg (Γ : MixedState d) : 0 ≤ Γ.interaction :=
  tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) (Γ.component k).interaction_nonneg

def directIntegrand (D : Density d) (z : Point d × Point d) : ℝ :=
  D.charge z.1 * D.charge z.2 / ‖z.1-z.2‖

def hartree (D : Density d) : ℝ := (∫ z, directIntegrand D z) / 2

def exchangeIntegrand (γ : OneBody d) (z : Point d × Point d) : ℝ :=
  (∑ i, ∑ j, ‖γ.kernel z.1 z.2 i j‖^2) / ‖z.1-z.2‖

def OneBody.exchange (γ : OneBody d) : ℝ := (∫ z, exchangeIntegrand γ z) / 2

theorem OneBody.exchange_nonneg (γ : OneBody d) : 0 ≤ γ.exchange := by
  apply div_nonneg _ (by norm_num)
  exact integral_nonneg fun z => div_nonneg
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (norm_nonneg _)

def levyLieb (D : Density d) : ℝ :=
  sInf {e | ∃ Γ : MixedState d, Γ.matrixDensity =ᵐ[volume] D.matrix ∧ e = Γ.kinetic + Γ.interaction}

def energy (D : Density d) : ℝ := levyLieb D - hartree D

/-- Finite direct energy permits evaluating the Coulomb quasi-free trace as direct minus exchange. -/
def QuasiFreeRealization (d : ℕ) : Prop := ∀ (D : Density d) (γ : OneBody d),
  γ.matrixDensity =ᵐ[volume] D.matrix → Integrable (directIntegrand D) →
  Integrable (exchangeIntegrand γ) ∧ ∃ Γ : MixedState d, Γ.matrixDensity =ᵐ[volume] D.matrix ∧
    Γ.kinetic = γ.kinetic ∧ Γ.interaction = hartree D - γ.exchange

theorem energy_le_bestKinetic (qf : QuasiFreeRealization d) {D : Density d}
    (finiteDirect : Integrable (directIntegrand D))
    (rep : ∃ γ : OneBody d, γ.matrixDensity =ᵐ[volume] D.matrix) :
    energy D ≤ bestKinetic D.matrix := by
  obtain ⟨g, hg⟩ := rep
  refine le_csInf (s := {t | ∃ γ : OneBody d, γ.matrixDensity =ᵐ[volume] D.matrix ∧ t = γ.kinetic})
    ⟨g.kinetic, g, hg, rfl⟩ ?_
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨_, Γ, hΓ, hk, hi⟩ := qf D γ hγ finiteDirect
  have bound : levyLieb D ≤ Γ.kinetic + Γ.interaction := csInf_le
    ⟨0, fun _ ⟨Γ', _, he⟩ => he ▸ add_nonneg Γ'.kinetic_nonneg Γ'.interaction_nonneg⟩ ⟨Γ, hΓ, rfl⟩
  rw [hk, hi] at bound
  unfold energy
  linarith [γ.exchange_nonneg]

/-- The Coulomb upper bound with the same constants as the kinetic constrained search. -/
theorem kinetic_and_energy_upper (hd : 0 < d) (sob : FamilySobolevComposition d)
    (projectors : ProjectorTraceIdentity d) (qf : QuasiFreeRealization d)
    (profiles : ∀ d : ℕ, 0 < d → ∃ κ₁ > 0, ∃ κ₂ > 0, SmoothingProfiles d κ₁ κ₂) :
    ∃ κ₁ > 0, ∃ κ₂ > 0, ∀ (D : Density d) (S : Gradient d), SqrtRegular D S →
      Integrable (directIntegrand D) → ∀ ε : ℝ, 0 < ε →
      energy D ≤ bestKinetic D.matrix ∧
        bestKinetic D.matrix ≤ thomasFermi d * (1+κ₁*ε) * traceMoment D (1+2/(d:ℝ)) +
          κ₂ * (1+√ε)^2 / ε * sqrtKinetic S := by
  obtain ⟨κ₁, h₁, κ₂, h₂, H⟩ := kinetic_upper hd sob projectors profiles
  refine ⟨κ₁, h₁, κ₂, h₂, ?_⟩
  intro D S hD hj ε hε
  obtain ⟨rep, bound⟩ := H D S hD ε hε
  exact ⟨energy_le_bestKinetic qf hj rep, bound⟩

/-- Sobolev interpolation for the charge of a regular square-root density, at the
Hardy–Littlewood–Sobolev exponent for the Coulomb kernel. -/
def ChargeSobolevEmbedding (d : ℕ) : Prop := ∀ (D : Density d) (S : Gradient d),
  SqrtRegular D S → MemLp D.charge (ENNReal.ofReal (2*(d:ℝ)/(2*(d:ℝ)-1)))

/-- The Coulomb case of the Hardy–Littlewood–Sobolev inequality, in its integrability form. -/
def CoulombHLS (d : ℕ) : Prop := ∀ f : Point d → ℝ,
  MemLp f (ENNReal.ofReal (2*(d:ℝ)/(2*(d:ℝ)-1))) →
    Integrable (fun z : Point d × Point d => f z.1 * f z.2 / ‖z.1-z.2‖)

/-- For `d ≥ 2` the Coulomb kernel is locally integrable, and Sobolev and HLS
supply finite direct energy for every admissible density. -/
theorem energy_upper (hd : 2 ≤ d) (sob : FamilySobolevComposition d)
    (embed : ChargeSobolevEmbedding d) (hls : CoulombHLS d)
    (projectors : ProjectorTraceIdentity d) (qf : QuasiFreeRealization d)
    (profiles : ∀ d : ℕ, 0 < d → ∃ κ₁ > 0, ∃ κ₂ > 0, SmoothingProfiles d κ₁ κ₂) :
    ∃ κ₁ > 0, ∃ κ₂ > 0, ∀ (D : Density d) (S : Gradient d), SqrtRegular D S →
      ∀ ε : ℝ, 0 < ε → energy D ≤ thomasFermi d * (1+κ₁*ε) * traceMoment D (1+2/(d:ℝ)) +
        κ₂ * (1+√ε)^2 / ε * sqrtKinetic S := by
  obtain ⟨κ₁, h₁, κ₂, h₂, H⟩ := kinetic_and_energy_upper (by omega : 0 < d) sob projectors qf profiles
  refine ⟨κ₁, h₁, κ₂, h₂, ?_⟩
  intro D S hD ε hε
  obtain ⟨leT, leR⟩ := H D S hD (hls D.charge (embed D S hD)) ε hε
  exact leT.trans leR

/-- A nonzero plateau already forces infinite direct Coulomb energy on the real line. -/
theorem line_coulomb_not_integrable_of_plateau (ρ : ℝ → ℝ)
    (hρ : ∀ x ∈ Set.Icc (0:ℝ) 1, ρ x = 1) :
    ¬Integrable (fun z : ℝ × ℝ => ρ z.1 * ρ z.2 / |z.1-z.2|) := by
  intro H
  have hp : (volume : Measure ℝ) (Set.Ioo 0 1) ≠ 0 := by simp
  obtain ⟨x, hx, hi⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae H.prod_right_ae)
  have hi' : IntegrableOn (fun y : ℝ => (y-x)⁻¹) (Set.Icc x 1) := by
    refine (integrableOn_congr_fun (f := fun y : ℝ => ρ x * ρ y / |x-y|) ?_ measurableSet_Icc).mp hi.integrableOn
    intro y hy
    simp [hρ x ⟨hx.1.le, hx.2.le⟩, hρ y ⟨hx.1.le.trans hy.1, hy.2⟩, abs_of_nonpos (sub_nonpos.mpr hy.1), neg_sub]
  have inter := (intervalIntegrable_iff_integrableOn_Icc_of_le hx.2.le).2 hi'
  rw [intervalIntegrable_sub_inv_iff] at inter
  exact inter.elim hx.2.ne (fun h => h (Set.left_mem_uIcc ..))

end TSGA.ManyBody.Spatial
