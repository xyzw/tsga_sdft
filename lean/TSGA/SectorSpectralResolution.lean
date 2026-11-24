import TSGA.MarginalPositivity
import TSGA.ParticleNumber
import TSGA.SpectralLipschitz
import TSGA.WaveCurrent
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Realizing a sector spectral decomposition as a concrete mixed state

A positive normal Fock state of finite number, kinetic and interaction
expectations has a countable sector spectral decomposition. Its occupied
eigenvectors belong to the kinetic and Coulomb form domains. The weights
and normalized form-domain vectors suffice to construct the mixed state
of the constrained search, since finite expected number implies absolute
pointwise summability of every spin density entry almost everywhere.
-/

noncomputable section
namespace TSGA.ManyBody

open MeasureTheory Filter
open scoped ComplexOrder ComplexConjugate ENNReal MatrixOrder

/-- Spin density entries are dominated by the total charge, including
off-diagonal entries in a noncollinear frame. -/
theorem norm_spin_entry_le_trace {A : SpinMatrix} (hA : A.PosSemidef) (i j : Fin 2) :
    ‖A i j‖ ≤ A.trace.re := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB]
  have h (a : Fin 2) (k : Fin 2) : ‖B k a‖^2 ≤ ∑ l, ‖B k l‖^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg ‖B k l‖) (Finset.mem_univ a)
  calc
    ‖(star B * B) i j‖ ≤ ∑ k, ‖B k i‖*‖B k j‖ := by
      simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose] using
        (norm_sum_le Finset.univ (fun k => conj (B k i)*B k j))
    _ ≤ ∑ k, ∑ l, ‖B k l‖^2 := Finset.sum_le_sum fun k _ => by
      nlinarith only [h i k,h j k,sq_nonneg (‖B k i‖-‖B k j‖)]
    _ = _ := (Localization.hs_trace B).trans (congrArg Complex.re (Matrix.trace_mul_comm B (star B)))

/-- The data delivered by the sectorwise spectral theorem with finite
expectations of the three positive Fock quadratic forms. -/
structure SectorSpectralResolution where
  component : ℕ → PureState
  weight : ℕ → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  normalized : HasSum weight 1
  particles_summable : Summable (fun k => weight k * (component k).particles)
  kinetic_summable : Summable (fun k => weight k * (component k).kinetic)
  interaction_summable : Summable (fun k => weight k * (component k).interaction)

/-- Finite expected particle number controls the pointwise series of spin
density matrices. No summability of a second particle moment is needed. -/
theorem SectorSpectralResolution.density_summable (d : SectorSpectralResolution) :
    ∀ᵐ x : Position, ∀ i j, Summable (fun k => (d.weight k : ℂ) * (d.component k).matrixDensity x i j) := by
  let f (k : ℕ) (x : Position) := d.weight k * ((d.component k).matrixDensity x).trace.re
  have mass (s : PureState) : Integrable (fun x => (s.matrixDensity x).trace.re) ∧
      (∫ x, (s.matrixDensity x).trace.re) = s.particles := by
    cases s with
    | vacuum => simp [PureState.matrixDensity, PureState.particles]
    | occupied ψ => simpa [PureState.particles,PureState.matrixDensity] using ψ.particleNumber
  have hp (k) : 0 ≤ᵐ[volume] f k := (d.component k).matrixDensity_posSemidef.mono fun x hx =>
    mul_nonneg (d.weight_nonneg k) (RCLike.nonneg_iff.mp hx.trace_nonneg).1
  have hi (k) : Integrable (f k) := (mass (d.component k)).1.const_mul _
  have hm (k) : eLpNorm (f k) 1 volume = ENNReal.ofReal (d.weight k*(d.component k).particles) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      _ = ∫⁻ x, ENNReal.ofReal (f k x) := by
        apply lintegral_congr_ae
        filter_upwards [hp k] with x hx
        rw [← ofReal_norm, Real.norm_of_nonneg hx]
      _ = ENNReal.ofReal (∫ x, f k x) := (ofReal_integral_eq_lintegral_ofReal (hi k) (hp k)).symm
      _ = _ := by simp [f,integral_const_mul,(mass (d.component k)).2]
  have hn : ∀ᵐ x : Position, Summable (fun k => ‖f k x‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl (fun k => (hi k).1)
    simpa only [hm] using d.particles_summable.tsum_ofReal_ne_top
  have hpos : ∀ᵐ x : Position, ∀ k, ((d.component k).matrixDensity x).PosSemidef :=
    ae_all_iff.mpr fun k => (d.component k).matrixDensity_posSemidef
  filter_upwards [hn,hpos] with x hx hpx
  intro i j
  apply hx.of_norm_bounded
  intro k
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (d.weight_nonneg k),Real.norm_of_nonneg (mul_nonneg (d.weight_nonneg k) (RCLike.nonneg_iff.mp (hpx k).trace_nonneg).1 : 0 ≤ f k x)]
  exact mul_le_mul_of_nonneg_left (norm_spin_entry_le_trace (hpx k) i j) (d.weight_nonneg k)

def SectorSpectralResolution.toMixedState (d : SectorSpectralResolution) : MixedState where
  component := d.component
  weight := d.weight
  weight_nonneg := d.weight_nonneg
  normalized := d.normalized
  particles_summable := d.particles_summable
  kinetic_summable := d.kinetic_summable
  interaction_summable := d.interaction_summable
  density_summable := d.density_summable

def SectorSpectralResolution.ofMixedState (Γ : MixedState) : SectorSpectralResolution where
  component := Γ.component
  weight := Γ.weight
  weight_nonneg := Γ.weight_nonneg
  normalized := Γ.normalized
  particles_summable := Γ.particles_summable
  kinetic_summable := Γ.kinetic_summable
  interaction_summable := Γ.interaction_summable

@[simp] theorem SectorSpectralResolution.toMixedState_ofMixedState (Γ : MixedState) :
    (SectorSpectralResolution.ofMixedState Γ).toMixedState = Γ := rfl

/-- The diagonal expansion of a quadratic observable in this ensemble. -/
def SectorSpectralResolution.expect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : SectorSpectralResolution) (F : PureState → E) : E := ∑' k, d.weight k • F (d.component k)

theorem SectorSpectralResolution.realize_expect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : SectorSpectralResolution) (F : PureState → E) :
    (∑' k, d.toMixedState.weight k • F (d.toMixedState.component k)) = d.expect F := rfl

def MixedState.particleMean (Γ : MixedState) : ℝ := ∑' k, Γ.weight k * (Γ.component k).particles

private theorem summable_weighted_blocks (Γ : MixedState) (states : ℕ → MixedState)
    (F : PureState → ℝ) (hp : ∀ s, 0 ≤ F s)
    (hrow : ∀ k, Summable (fun j => (states k).weight j * F ((states k).component j)))
    (htotal : Summable (fun k => Γ.weight k * ∑' j, (states k).weight j * F ((states k).component j))) :
    Summable (fun p : ℕ × ℕ => (Γ.weight p.1*(states p.1).weight p.2)*F ((states p.1).component p.2)) := by
  apply (summable_prod_of_nonneg (fun (p : ℕ × ℕ) =>
    mul_nonneg (mul_nonneg (Γ.weight_nonneg p.1) ((states p.1).weight_nonneg p.2)) (hp _))).2
  simp only [mul_assoc]
  refine ⟨fun k => (hrow k).mul_left _,?_⟩
  simpa only [tsum_mul_left] using htotal

/-- A countable mixture of countable sector decompositions, indexed on ℕ
by the canonical bijection ℕ × ℕ ≃ ℕ. The moment hypotheses are exactly
the weighted totals of the corresponding component states. -/
def MixedState.flatten (Γ : MixedState) (states : ℕ → MixedState)
    (hN : Summable (fun k => Γ.weight k * (states k).particleMean))
    (hT : Summable (fun k => Γ.weight k * (states k).kinetic))
    (hV : Summable (fun k => Γ.weight k * (states k).interaction)) : MixedState := by
  let e := Nat.pairEquiv.symm
  let c : ℕ → PureState := fun l => (states (e l).1).component (e l).2
  let w : ℕ → ℝ := fun l => Γ.weight (e l).1 * (states (e l).1).weight (e l).2
  have sum (F : PureState → ℝ) (hp : ∀ s, 0 ≤ F s)
      (hr : ∀ k, Summable (fun j => (states k).weight j * F ((states k).component j)))
      (ht : Summable (fun k => Γ.weight k * ∑' j, (states k).weight j * F ((states k).component j))) :
      Summable (fun l => w l * F (c l)) :=
    (e.summable_iff (f := fun p : ℕ × ℕ => (Γ.weight p.1 * (states p.1).weight p.2) * F ((states p.1).component p.2))).mpr (summable_weighted_blocks Γ states F hp hr ht)
  have wpos (l) : 0 ≤ w l := mul_nonneg (Γ.weight_nonneg _) ((states _).weight_nonneg _)
  have row (k : ℕ) : HasSum (fun j => Γ.weight k * (states k).weight j) (Γ.weight k) := by
    simpa only [mul_one] using ((states k).normalized.mul_left (Γ.weight k))
  have hs : Summable (fun p : ℕ × ℕ => Γ.weight p.1 * (states p.1).weight p.2) := by
    apply (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => Γ.weight p.1 * (states p.1).weight p.2)
      (fun p => mul_nonneg (Γ.weight_nonneg p.1) ((states p.1).weight_nonneg p.2))).2
    exact ⟨fun k => (row k).summable, by simpa only [fun k => (row k).tsum_eq] using Γ.normalized.summable⟩
  have ht : (∑' l, w l) = 1 := by
    calc
      _ = ∑' p : ℕ × ℕ, Γ.weight p.1 * (states p.1).weight p.2 := e.tsum_eq (fun p : ℕ × ℕ => Γ.weight p.1 * (states p.1).weight p.2)
      _ = 1 := by simpa only [fun k => (row k).tsum_eq,Γ.normalized.tsum_eq] using hs.tsum_prod
  have hs' : Summable w := (e.summable_iff (f := fun p : ℕ × ℕ => Γ.weight p.1 * (states p.1).weight p.2)).mpr hs
  exact SectorSpectralResolution.toMixedState ⟨c,w,wpos,ht ▸ hs'.hasSum,
    sum _ (fun s => Nat.cast_nonneg s.particles) (fun k => (states k).particles_summable) hN,
    sum _ PureState.kinetic_nonneg (fun k => (states k).kinetic_summable) hT,
    sum _ PureState.interaction_nonneg (fun k => (states k).interaction_summable) hV⟩

/-- Expectations in the flattened ensemble are the iterated expectations.
The absolute summability assumption is on the joint row and eigenvector
index, so the identity applies to signed and complex observables as well. -/
theorem MixedState.flatten_expect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Γ : MixedState) (states : ℕ → MixedState) (hN hT hV) (F : PureState → E)
    (h : Summable (fun p : ℕ × ℕ =>
      (Γ.weight p.1 * (states p.1).weight p.2) • F ((states p.1).component p.2))) :
    let Λ := Γ.flatten states hN hT hV
    (∑' k, Λ.weight k • F (Λ.component k)) = ∑' k, Γ.weight k • ∑' j, (states k).weight j • F ((states k).component j) := by
  intro Λ
  calc
    _ = ∑' p : ℕ × ℕ, (Γ.weight p.1 * (states p.1).weight p.2) • F ((states p.1).component p.2) :=
      Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => (Γ.weight p.1 * (states p.1).weight p.2) • F ((states p.1).component p.2))
    _ = _ := by simpa only [mul_smul,tsum_const_smul''] using h.tsum_prod

/-- Any observable bounded by the particle, kinetic and interaction forms
is absolutely summable for the flattened ensemble. -/
theorem MixedState.flatten_summable_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Γ : MixedState) (states : ℕ → MixedState)
    (hN : Summable (fun k => Γ.weight k * (states k).particleMean))
    (hT : Summable (fun k => Γ.weight k * (states k).kinetic))
    (hV : Summable (fun k => Γ.weight k * (states k).interaction))
    (F : PureState → E) (C : ℝ) (hb : ∀ s : PureState, ‖F s‖ ≤ C * (s.particles + s.kinetic + s.interaction)) :
    Summable (fun p : ℕ × ℕ => (Γ.weight p.1 * (states p.1).weight p.2) • F ((states p.1).component p.2)) := by
  have hn := summable_weighted_blocks Γ states (fun s => (s.particles : ℝ))
    (fun s => Nat.cast_nonneg _) (fun k => (states k).particles_summable) hN
  have ht := summable_weighted_blocks Γ states PureState.kinetic PureState.kinetic_nonneg
    (fun k => (states k).kinetic_summable) hT
  have hw := summable_weighted_blocks Γ states PureState.interaction PureState.interaction_nonneg
    (fun k => (states k).interaction_summable) hV
  apply (((hn.add ht).add hw).mul_left C).of_norm_bounded
  intro p
  let a := Γ.weight p.1 * (states p.1).weight p.2
  have ha : 0 ≤ a := mul_nonneg (Γ.weight_nonneg _) ((states p.1).weight_nonneg _)
  change ‖a • F _‖ ≤ C * ((a*_+a*_)+a*_)
  rw [norm_smul, Real.norm_of_nonneg ha]
  calc
    _ ≤ a * (C * _) := mul_le_mul_of_nonneg_left (hb _) ha
    _ = _ := by ring

theorem MixedState.flatten_moments (Γ : MixedState) (states : ℕ → MixedState) (hN hT hV) :
    let Λ := Γ.flatten states hN hT hV
    Λ.particleMean = ∑' k, Γ.weight k * (states k).particleMean ∧
    Λ.kinetic = ∑' k, Γ.weight k * (states k).kinetic ∧
    Λ.interaction = ∑' k, Γ.weight k * (states k).interaction := by
  intro Λ
  refine ⟨?_,?_,?_⟩
  · exact Γ.flatten_expect states hN hT hV (fun s => (s.particles : ℝ))
      (summable_weighted_blocks Γ states _ (fun s => Nat.cast_nonneg _) (fun k => (states k).particles_summable) hN)
  · exact Γ.flatten_expect states hN hT hV PureState.kinetic
      (summable_weighted_blocks Γ states _ PureState.kinetic_nonneg (fun k => (states k).kinetic_summable) hT)
  · exact Γ.flatten_expect states hN hT hV PureState.interaction
      (summable_weighted_blocks Γ states _ PureState.interaction_nonneg (fun k => (states k).interaction_summable) hV)

/-- Pointwise density of a mixture of sector spectral decompositions. -/
theorem MixedState.flatten_density (Γ : MixedState) (states : ℕ → MixedState) (hN hT hV) :
    let Λ := Γ.flatten states hN hT hV
    ∀ᵐ x : Position, ∀ i j, Λ.matrixDensity x i j =
      ∑' k, (Γ.weight k : ℂ) * (states k).matrixDensity x i j := by
  intro Λ
  filter_upwards [Λ.density_summable] with x hx
  intro i j
  let f (p : ℕ × ℕ) := (((Γ.weight p.1 * (states p.1).weight p.2 : ℝ) : ℂ) *
    ((states p.1).component p.2).matrixDensity x i j)
  have hs : Summable f := (Nat.pairEquiv.symm.summable_iff (f := f)).mp (hx i j)
  calc
    _ = ∑' p, f p := Nat.pairEquiv.symm.tsum_eq f
    _ = _ := by
      rw [hs.tsum_prod]
      simp only [f,Complex.ofReal_mul,mul_assoc,tsum_mul_left,MixedState.matrixDensity]

/-- A constant spin sandwich commutes with the countable density mixture. -/
theorem MixedState.flatten_density_sandwich (Γ : MixedState) (states : ℕ → MixedState) (hN hT hV)
    (S : SpinMatrix) (hd : ∀ k, ∀ᵐ x : Position, (states k).matrixDensity x =
      S * (Γ.component k).matrixDensity x * star S) :
    ∀ᵐ x : Position, (Γ.flatten states hN hT hV).matrixDensity x = S * Γ.matrixDensity x * star S := by
  filter_upwards [Γ.flatten_density states hN hT hV, ae_all_iff.mpr hd, Γ.density_summable] with x hx he hs
  have hh : HasSum (fun k => (Γ.weight k : ℂ) • (Γ.component k).matrixDensity x) (Γ.matrixDensity x) :=
    Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => (hs i j).hasSum
  have hS := (hh.mul_left S).mul_right (star S)
  ext i j
  rw [hx]
  have ht := (Pi.hasSum.mp (Pi.hasSum.mp hS i) j).tsum_eq
  simpa only [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,smul_eq_mul] using ht

/-- Particle-resolved momenta of the mixture, with convergence obtained
from finite expected particle number and kinetic energy. -/
theorem MixedState.flatten_spinMomentum (Γ : MixedState) (states : ℕ → MixedState) (hN hT hV)
    (a : Fin 2) (j : Fin 3) :
    (Γ.flatten states hN hT hV).spinMomentum a j = ∑' k, Γ.weight k * (states k).spinMomentum a j := by
  apply Γ.flatten_expect states hN hT hV (fun s => s.spinMomentum a j)
  apply Γ.flatten_summable_of_bound states hN hT hV (fun s => s.spinMomentum a j) 1
  intro s
  rw [Real.norm_eq_abs,one_mul]
  exact (s.spinMomentum_bound a j).trans (le_add_of_nonneg_right s.interaction_nonneg)

theorem MixedState.particleMean_nonneg (Γ : MixedState) : 0 ≤ Γ.particleMean :=
  tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) (Nat.cast_nonneg _)

/-- Finiteness of the averaged moments follows from their sector bounds
under removal. -/
theorem MixedState.summable_localized_moments (Γ : MixedState) (states : ℕ → MixedState)
    (hN : ∀ k, (states k).particleMean ≤ (Γ.component k).particles)
    (hT : ∀ k, (states k).kinetic ≤ (Γ.component k).kinetic)
    (hV : ∀ k, (states k).interaction ≤ (Γ.component k).interaction) :
    Summable (fun k => Γ.weight k * (states k).particleMean) ∧
    Summable (fun k => Γ.weight k * (states k).kinetic) ∧
    Summable (fun k => Γ.weight k * (states k).interaction) :=
  ⟨Γ.particles_summable.of_nonneg_of_le (fun k => mul_nonneg (Γ.weight_nonneg k) (states k).particleMean_nonneg)
      (fun k => mul_le_mul_of_nonneg_left (hN k) (Γ.weight_nonneg k)),
   Γ.kinetic_summable.of_nonneg_of_le (fun k => mul_nonneg (Γ.weight_nonneg k) (states k).kinetic_nonneg)
      (fun k => mul_le_mul_of_nonneg_left (hT k) (Γ.weight_nonneg k)),
   Γ.interaction_summable.of_nonneg_of_le (fun k => mul_nonneg (Γ.weight_nonneg k) (states k).interaction_nonneg)
      (fun k => mul_le_mul_of_nonneg_left (hV k) (Γ.weight_nonneg k))⟩

end TSGA.ManyBody
