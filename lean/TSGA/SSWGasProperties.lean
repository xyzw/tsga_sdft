import TSGA.CoulombModelInputs
import TSGA.ConditionalUEG

/-! # Thermodynamic limit and properties of the spin-spiral wave gas

Theorem 3.1 and Proposition 3.2 of `tsga.tex` for the Coulomb energy.
The polarization curve uses the signed magnetization fraction in Section 3.1.
-/

noncomputable section
namespace TSGA

open SSW MeasureTheory Filter
open scoped Topology ComplexOrder

namespace SSW

/-- At a zero of the transverse magnetization, including vacuum, every
wavevector yields the uniform gas energy independently of the phase extension. -/
theorem sswEnergy_of_transverseMagnetization_eq_zero (E : EnergyFunctional)
    (η : Mollifier) {M : SpinMatrix} (hM : M.IsHermitian)
    (hz : transverseMagnetization M = 0) (q : Position) :
    sswEnergy E η M q = uniformEnergy E η M := by
  have h10 : M 1 0 = 0 := (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have h01 : M 0 1 = 0 := by simpa [h10] using (hM.apply 0 1).symm
  have fixed (α : ℝ) : rotate α M = M := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact rotate_diag _ _ _
    · simp [Localization.rotate_by_entry, h01]
    · simp [Localization.rotate_by_entry, h10]
    · exact rotate_diag _ _ _
  have field (f : Position → ℝ) (k : Position) :
      cutoffSpiral f M k = fun y => (f y : ℂ) • M :=
    funext fun y => by simp only [cutoffSpiral, fixed]
  have tile (ℓ δ : ℝ) : tileEnergy E η M ℓ δ = fun _ =>
      E (fun y => (smoothedIndicator (tetrahedron ℓ) η δ y : ℂ) • M) /
        regionVolume (tetrahedron ℓ) := by
    funext k
    simp only [tileEnergy, field]
  apply tileLimit_congr
  exact Filter.Eventually.of_forall fun _ => by
    simp only [averagedTile, tile, directionAverage_const]

/-- The three parts of `prop:SSW_properties` for one nonzero spin matrix. -/
structure SSWGasProperties (F : GasEnergies) (M : SpinMatrix) : Prop where
  isotropic : ∀ (R : Position ≃ₗᵢ[ℝ] Position) (q : Position), F.ssw M (R q) = F.ssw M q
  concave : ConcaveOn ℝ Set.univ (fun q => F.ssw M q - ‖q‖ ^ 2 / 4 * M.trace.re)
  bounds : ∀ {ζ θ : ℝ}, SpinParameters M ζ θ → ∀ q : Position,
    let up := (1 + ζ * Real.cos θ) / 2 * M.trace.re
    let down := (1 - ζ * Real.cos θ) / 2 * M.trace.re
    let cost := M.trace.re * ‖q‖ ^ 2 / 4 * (1 - ζ ^ 2 * (Real.cos θ) ^ 2)
    F.ueg (populations up down) ≤ F.ssw M q ∧ F.ssw M q ≤ F.ueg M + cost ∧
      (ζ = 1 → F.ssw M q = F.ueg M + cost)

private theorem trace_pos_of_nonzero {M : SpinMatrix} (hM : M.PosSemidef) (hne : M ≠ 0) :
    0 < M.trace.re := by
  have ht := RCLike.nonneg_iff.mp hM.trace_nonneg
  exact lt_of_le_of_ne ht.1 fun h => hne (hM.trace_eq_zero_iff.mp (Complex.ext h.symm ht.2))

/-- Concavity applies at every nonzero positive semidefinite matrix.
The polar angle and polarization enter only the two bounds and their equality case. -/
theorem SSWGasTheorem.properties {F : GasEnergies} (gas : SSWGasTheorem F)
    {M : SpinMatrix} (hM : M.PosSemidef) (hne : M ≠ 0) : SSWGasProperties F M := by
  obtain ⟨ζ, θ, h⟩ := exists_spinParameters hM (trace_pos_of_nonzero hM hne)
  refine ⟨gas.isotropic M, gas.concave h, ?_⟩
  intro z angle hz q up down cost
  have hp : (populations up down).PosSemidef := hz.diagonal_eq_populations ▸ hz.diagonal_positive
  have b := gas.bounds hz
  rw [← F.zero_mode M hM, ← F.zero_mode _ hp]
  exact ⟨b.lower q, b.upper q, fun full => b.full full q⟩

/-- Two constructions with different reference mollifiers agree, by evaluating
their limits along the same sequence of balls. -/
theorem SSWGasTheorem.reference_independent {E : EnergyFunctional} {η χ : Mollifier}
    (gas : SSWGasTheorem (referenceEnergies E η)) (gas' : SSWGasTheorem (referenceEnergies E χ))
    {M : SpinMatrix} (hM : M.PosSemidef) (hne : M ≠ 0) (q : Position) :
    sswEnergy E η M q = sswEnergy E χ M q :=
  let D := DomainSequence.balls η
  let hr := trace_pos_of_nonzero hM hne
  tendsto_nhds_unique (gas.limit M hM hr q D) (gas'.limit M hM hr q D)

end SSW

namespace ManyBody

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Measure Z} [SFinite ι] {η : Mollifier}

/-- Theorem 3.1. All choices of domains, smoothing widths and outer mollifier
give the same energy. The spiral of wavevector zero gives the uniform gas. -/
theorem CoulombModelInputs.ssw_limit (P : CoulombModelInputs μ ι η)
    {M : SpinMatrix} (hM : M.PosSemidef) (hne : M ≠ 0) (q : Position) :
    (∀ D : DomainSequence, Tendsto (fun n => D.energyDensity energy M n q)
      atTop (𝓝 (sswEnergy energy η M q))) ∧
    sswEnergy energy η M 0 = uniformEnergy energy η M :=
  ⟨P.gas.1.limit M hM (SSW.trace_pos_of_nonzero hM hne) q, sswEnergy_zero_wavevector ..⟩

/-- Proposition 3.2 for the same reference energies as Theorem 3.1. -/
theorem CoulombModelInputs.ssw_properties (P : CoulombModelInputs μ ι η)
    {M : SpinMatrix} (hM : M.PosSemidef) (hne : M ≠ 0) :
    SSWGasProperties (referenceEnergies energy η) M :=
  P.gas.1.properties hM hne

/-- At fixed positive charge the uniform gas energy is convex and even on
the signed polarization interval. Its minimum is attained at zero and its
maximum at full polarization. -/
theorem CoulombGasInputs.uniform_polarization {K r : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) (hr : 0 < r) :
    let g := fun z : ℝ => uniformEnergy energy η
      (populations ((1 + z) / 2 * r) ((1 - z) / 2 * r))
    ConvexOn ℝ (Set.Icc (-1) 1) g ∧ MonotoneOn g (Set.Icc 0 1) ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, g (-z) = g z ∧ g 0 ≤ g z ∧ g z ≤ g 1 := by
  intro g
  let f := fun t : ℝ => uniformEnergy energy η (populations (r - t*r) (t*r))
  obtain ⟨conv, symm, _⟩ := L.population_curve H sob hr
  let t : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap (1/2 : ℝ) 0
  have coord (z : ℝ) : t z = (1-z)/2 := by
    simp [t, AffineMap.lineMap_apply_module]
    ring
  have mem {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) : t z ∈ Set.Icc (0 : ℝ) 1 := by
    rw [coord]
    constructor <;> linarith [hz.1, hz.2]
  have hg (z : ℝ) : g z = f (t z) := by
    dsimp only [g, f]
    rw [coord, show r - (1-z)/2*r = (1+z)/2*r by ring]
  have cg : ConvexOn ℝ (Set.Icc (-1) 1) g := by
    rw [show g = f ∘ t from funext hg]
    exact (conv.comp_affineMap t).subset (fun _ hz => mem hz) (convex_Icc ..)
  have even {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) : g (-z) = g z := by
    rw [hg, hg, show t (-z) = 1 - t z by rw [coord, coord]; ring]
    exact symm _ (mem hz)
  have between {z x : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hx : x ∈ Set.Icc (-z) z) :
      g x ≤ g z := by
    have hn : -z ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
    exact ((convex_iff_ordConnected.mp (cg.convex_le (g z))).out
      (x := -z) ⟨hn, (even hz).le⟩ (y := z) ⟨hz, le_rfl⟩ hx).2
  refine ⟨cg, ?_, ?_⟩
  · intro x hx z hz hxz
    exact between ⟨by linarith [hz.1], hz.2⟩ ⟨by linarith [hz.1, hx.1], hxz⟩
  intro z hz
  refine ⟨even hz, ?_, between (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1) hz⟩
  rcases le_total 0 z with h | h
  · exact between hz ⟨neg_nonpos.mpr h, h⟩
  · rw [← even hz]
    exact between ⟨by linarith [hz.2], by linarith [hz.1]⟩ ⟨by linarith, by linarith⟩

/-- The final bound in Appendix E. Transferring charge to the empty spin
channel lowers the uniform gas energy by at most a cube root of its fraction. -/
theorem CoulombGasInputs.uniform_spin_flip {K : ℝ} (L : CoulombGasInputs η K)
    (H : FiniteEnergyInputs) (sob : SobolevDifferenceQuotients) :
    ∃ C > 0, ∀ {r x : ℝ}, 0 < r → x ∈ Set.Icc 0 (r/2) →
      let loss := uniformEnergy energy η (populations r 0) -
        uniformEnergy energy η (populations (r-x) x)
      0 ≤ loss ∧ loss ≤ C * (r^(4/3 : ℝ) + r^(5/3 : ℝ)) * (x/r)^(1/3 : ℝ) := by
  obtain ⟨J, hJ, holder⟩ := coulomb_ssw_holder L.localization (L.kinematics H sob)
    L.rate (L.removal H sob) H.lo_nonneg H.indirect_lower
  refine ⟨J * (2 : ℝ)^(1/3 : ℝ), by positivity, ?_⟩
  intro r x hr hx loss
  let A := populations r 0
  let B := populations (r-x) x
  have hA : A.PosSemidef := population_pos hr.le le_rfl
  have hB : B.PosSemidef := population_pos (by linarith [hx.2]) hx.1
  have tr : max A.trace.re B.trace.re = r := by simp [A, B, populations]
  have h := holder hA hB 0 (by rwa [tr])
  simp only [sswEnergy_zero_wavevector, tr, holderGrowth, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] at h
  have dist : Localization.hilbertSchmidt (A-B) ≤ 2*x := by
    have diff : A-B = populations x (-x) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A, B, populations]
    rw [diff]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith [hx.1], ?_⟩
    simp [populations, Fin.sum_univ_two]
    nlinarith [sq_nonneg x]
  have rel : (Localization.hilbertSchmidt (A-B)/r)^(1/3 : ℝ) ≤
      (2 : ℝ)^(1/3 : ℝ) * (x/r)^(1/3 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hx.1 hr.le)]
    apply Real.rpow_le_rpow (div_nonneg (show 0 ≤ Localization.hilbertSchmidt (A-B)
      from Real.sqrt_nonneg _) hr.le) _ (by norm_num)
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right dist hr.le
  constructor
  · let z := 1 - 2*x/r
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [z]
      constructor <;> field_simp <;> linarith [hx.1, hx.2]
    have cap := ((L.uniform_polarization H sob hr).2.2 z hz).2.2
    have up : (1+z)/2*r = r-x := by dsimp [z]; field_simp; ring
    have down : (1-z)/2*r = x := by dsimp [z]; field_simp; ring
    simpa [loss, up, down, sub_nonneg] using cap
  · calc
      loss ≤ |uniformEnergy energy η A - uniformEnergy energy η B| := le_abs_self _
      _ ≤ _ := h
      _ ≤ J*(r^(4/3:ℝ)+r^(5/3:ℝ)) * ((2:ℝ)^(1/3:ℝ)*(x/r)^(1/3:ℝ)) :=
        mul_le_mul_of_nonneg_left rel (by positivity)
      _ = _ := by ring

end ManyBody
end TSGA
