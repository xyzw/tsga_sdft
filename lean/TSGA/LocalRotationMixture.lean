import TSGA.LocalRotationQuadratic
import TSGA.StateMixing

/-! # Countable mixtures of spatially rotated sector states -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory

/-- Sector rotation data before summing over the spectrum of a mixed state.
Weights enter the density identity so zero-weight components may stay fixed. -/
structure LocalComponentChange (p : PureState) (w : ℝ) (U : Position → unitary SpinMatrix) where
  rotated : PureState
  particles : rotated.particles = p.particles
  interaction : rotated.interaction = p.interaction
  density : ∀ᵐ x, w • rotated.matrixDensity x = (U x : SpinMatrix) * (w • p.matrixDensity x) * star (U x : SpinMatrix)
  extra : ℝ
  cross : ℝ
  extra_nonneg : 0 ≤ extra
  polar : ∀ t : ℝ, 0 ≤ p.kinetic + 2*t*cross + t^2*extra
  kinetic : rotated.kinetic = p.kinetic + 2*cross + extra

/-- Rotating each occupied spectral component gives an admissible grand
canonical state. The two cross terms combine by positivity of the full
quadratic form, including when either kinetic norm vanishes. -/
theorem MixedState.localRotation_of_components (Γ : MixedState) {U : Position → unitary SpinMatrix}
    (R : ∀ k, LocalComponentChange (Γ.component k) (Γ.weight k) U)
    {W : ℝ} (hs : Summable (fun k => Γ.weight k*(R k).extra))
    (hW : (∑' k, Γ.weight k*(R k).extra) ≤ W) :
    ∃ Δ : MixedState, Δ.matrixDensity =ᵐ[volume] (fun x => (U x : SpinMatrix)*Γ.matrixDensity x*star (U x : SpinMatrix)) ∧
      Δ.interaction = Γ.interaction ∧ ∃ g j : ℝ, 0 ≤ g ∧ g ≤ W ∧ j^2 ≤ Γ.kinetic*g ∧
        Δ.kinetic = Γ.kinetic+2*j+g := by
  let v := fun k => Γ.weight k*(R k).cross
  have hv : Summable v := by
    apply Summable.of_norm
    apply (Γ.kinetic_summable.add hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    have h₁ := (R k).polar 1
    have h₂ := (R k).polar (-1)
    have hb : |(R k).cross| ≤ (Γ.component k).kinetic+(R k).extra := by
      apply abs_le.mpr
      constructor <;> nlinarith [(Γ.component k).kinetic_nonneg,(R k).extra_nonneg]
    simpa only [v, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Γ.weight_nonneg k), mul_add,Pi.add_apply] using
      mul_le_mul_of_nonneg_left hb (Γ.weight_nonneg k)
  let g := ∑' k, Γ.weight k*(R k).extra
  let j := ∑' k, v k
  have hpoly (t : ℝ) : HasSum (fun k => Γ.weight k*((Γ.component k).kinetic+2*t*(R k).cross+t^2*(R k).extra))
      (Γ.kinetic+2*t*j+t^2*g) := by
    convert (Γ.kinetic_summable.hasSum.add (hv.hasSum.mul_left (2*t))).add (hs.hasSum.mul_left (t^2)) using 1
    · ext k
      simp only [v]
      ring
    · rfl
  have hk : HasSum (fun k => Γ.weight k*(R k).rotated.kinetic) (Γ.kinetic+2*j+g) := by
    simpa only [(R _).kinetic, mul_one,one_pow,one_mul] using hpoly 1
  have hd : ∀ᵐ x, HasSum (fun k => Γ.weight k • (R k).rotated.matrixDensity x)
      ((U x : SpinMatrix)*Γ.matrixDensity x*star (U x : SpinMatrix)) := by
    filter_upwards [Γ.density_summable, ae_all_iff.mpr (fun k => (R k).density)] with x hx he
    have hm : HasSum (fun k => Γ.weight k • (Γ.component k).matrixDensity x) (Γ.matrixDensity x) :=
      Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun l => (hx i l).hasSum
    simpa only [he] using (hm.mul_left (U x : SpinMatrix)).mul_right (star (U x : SpinMatrix))
  let Δ : MixedState := {
    component := fun k => (R k).rotated
    weight := Γ.weight
    weight_nonneg := Γ.weight_nonneg
    normalized := Γ.normalized
    particles_summable := by simpa only [(R _).particles] using Γ.particles_summable
    kinetic_summable := hk.summable
    interaction_summable := by simpa only [(R _).interaction] using Γ.interaction_summable
    density_summable := hd.mono fun x h i l => (Pi.hasSum.mp (Pi.hasSum.mp h i) l).summable }
  have hg : 0 ≤ g := tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) (R k).extra_nonneg
  refine ⟨Δ,hd.mono (fun x h => ?_),?_,g,j,hg,hW,localForm_schwarz Γ.kinetic_nonneg hg (fun t => ?_),hk.tsum_eq⟩
  · exact Matrix.ext fun i l => (Pi.hasSum.mp (Pi.hasSum.mp h i) l).tsum_eq
  · simp only [Δ,MixedState.interaction,(R _).interaction]
  · rw [← (hpoly t).tsum_eq]
    exact tsum_nonneg fun k => mul_nonneg (Γ.weight_nonneg k) ((R k).polar t)

end TSGA.ManyBody
