import TSGA.SpiralEnergy
import Mathlib.Tactic.FieldSimp

/-!
# Thermodynamic SSW energy

We fix the constant spin density matrix and write `density` for its trace.
The normalized cutoff has integral equal to the volume, so its particle
number is `density * volume n`. The pointwise limit in this auxiliary lemma is
supplied by `FiniteLocalization.tendsto` in the proof of Theorem 3.1.
-/

namespace TSGA.Thermodynamic

open Filter FiniteSpiral
open scoped Topology

/-- Part (ii) of `prop:SSW_properties`. The finite-volume variational
formula gives concavity of the energy density after the quadratic subtraction. -/
theorem correctedEnergyDensity_concave {State : ℕ → Type*} {density : ℝ}
    {volume : ℕ → ℝ} {stateEnergy : (n : ℕ) → State n → ℝ}
    {spinCurrent : (n : ℕ) → State n → Wavevector}
    {finiteEnergy : ℕ → Wavevector → ℝ} {energyDensity : Wavevector → ℝ}
    (hvol : ∀ n, 0 < volume n)
    (hvar : ∀ n, VariationalFormula (stateEnergy n) (spinCurrent n)
      (density * volume n) (finiteEnergy n))
    (hlim : ∀ q, Tendsto (fun n => finiteEnergy n q / volume n) atTop (𝓝 (energyDensity q))) :
    ConcaveOn ℝ Set.univ (fun q => energyDensity q - ‖q‖ ^ 2 / 4 * density) := by
  let corrected (n : ℕ) (q : Wavevector) := finiteEnergy n q / volume n - ‖q‖ ^ 2 / 4 * density
  have hconc (n : ℕ) : ConcaveOn ℝ Set.univ (corrected n) := by
    have heq : corrected n = fun q => (volume n)⁻¹ •
        (finiteEnergy n q - ‖q‖ ^ 2 / 4 * (density * volume n)) := by
      funext q
      dsimp only [corrected, smul_eq_mul]
      field_simp [(hvol n).ne']
    rw [heq]
    exact (correctedEnergy_concave (hvar n)).smul (inv_nonneg.mpr (hvol n).le)
  have hcorrected (q : Wavevector) :
      Tendsto (fun n => corrected n q) atTop (𝓝 (energyDensity q - ‖q‖ ^ 2 / 4 * density)) :=
    (hlim q).sub tendsto_const_nhds
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  exact le_of_tendsto_of_tendsto' (((hcorrected x).const_smul a).add ((hcorrected y).const_smul b))
    (hcorrected _) (fun n => (hconc n).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab)

/-- The radial monotonicity used in part (iii) of `prop:Lipschitz_SSW`.
On each ray the corrected isotropic energy is non-increasing. -/
theorem correctedEnergyDensity_antitoneOn_ray {density : ℝ} {energyDensity : Wavevector → ℝ}
    (hconc : ConcaveOn ℝ Set.univ (fun q => energyDensity q - ‖q‖ ^ 2 / 4 * density))
    (hiso : ∀ q k, ‖q‖ = ‖k‖ → energyDensity q = energyDensity k) (e : Wavevector) :
    AntitoneOn (fun r : ℝ => energyDensity (r • e) - ‖r • e‖ ^ 2 / 4 * density) (Set.Ici 0) := by
  let f (q : Wavevector) := energyDensity q - ‖q‖ ^ 2 / 4 * density
  have heven (q : Wavevector) : f (-q) = f q := by simp [f, hiso (-q) q (norm_neg q)]
  intro r hr s hs hrs
  change 0 ≤ r at hr
  change 0 ≤ s at hs
  rcases hs.eq_or_lt with hzero | hpos
  · have hrs' : r = s := by linarith
    rw [hrs']
  let a := (s + r) / (2 * s)
  let b := (s - r) / (2 * s)
  have ha : 0 ≤ a := div_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  have hrs' : a * s + b * (-s) = r := by
    dsimp [a, b]
    field_simp
    ring
  have hpoint : a • (s • e) + b • (-(s • e)) = r • e := by
    rw [← neg_smul, smul_smul, smul_smul, ← add_smul, hrs']
  have h := hconc.2 (Set.mem_univ (s • e)) (Set.mem_univ (-(s • e))) ha hb hab
  change a * f (s • e) + b * f (-(s • e)) ≤ f _ at h
  rwa [heven, ← add_mul, hab, one_mul, hpoint] at h

end TSGA.Thermodynamic
