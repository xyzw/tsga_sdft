import TSGA.FixedTraceRoot
import TSGA.CoulombMinorityFraction
import TSGA.AngularGas

/-! # Fixed-charge root regularity of the physical Coulomb SSW gas -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory SSW TSGA.Localization
open scoped ComplexOrder MatrixOrder

/-- Proposition E.2(vi) at equal positive traces. The constants for the
population and rotation estimates are uniform in the density and wavevector. -/
theorem coulomb_ssw_equal_trace_root {η : Mollifier} {J K cLO : ℝ}
    (loc : ∀ M : SpinMatrix, M.PosSemidef → 0 < M.trace.re → ∀ q : Position, FiniteLocalization energy η M q)
    (states : ∀ (M : SpinMatrix) (ζ θ : ℝ), SpinParameters M ζ θ →
      ∀ n, SpiralKinematics (DomainSequence.balls unitBallMollifier) M n ζ θ)
    (rate : FiniteRateTiling energy η K) (removal : SpiralRemovalTrials η J) (hc : 0 ≤ cLO)
    (lo : ∀ D : Density, ∀ Γ, feasible D.matrix Γ →
      -cLO * (∫ x, D.charge x^(4/3 : ℝ)) ≤ indirectAt D.matrix Γ)
    {p : ℝ} (hp : 3 ≤ p) :
    ∃ L > 0, ∀ q : Position, ∀ {P Q : SpinMatrix} (hP : P.PosSemidef) (hQ : Q.PosSemidef),
      0 < P.trace.re → P.trace.re = Q.trace.re →
      |sswEnergy energy η P q - sswEnergy energy η Q q| ≤
        L*(holderGrowth P.trace.re q/P.trace.re^(1/p:ℝ))*
          hilbertSchmidt (hP.1.cfc (fun t => t^(1/p:ℝ))-hQ.1.cfc (fun t => t^(1/p:ℝ))) := by
  obtain ⟨F, hF, frac⟩ := coulomb_ssw_minority_fraction loc states rate removal hc lo
  obtain ⟨G, hG, ang⟩ := coulomb_ssw_spin_rotation_hs loc rate (removal.withLiebOxford lo)
  have hK := zero_lt_one.trans_le rate.one_le
  have hp0 : 0 < p := by linarith
  have hgap := rootGap_pos hp0
  refine ⟨8*K*p+F*(p/3)+4*G/rootGap p, by positivity, ?_⟩
  intro q P Q hP hQ hr htr
  let r := P.trace.re
  let H := holderGrowth r q
  have hH : 0 ≤ H := by dsimp [H, r, holderGrowth]; positivity
  have h := fixedTrace_root_lipschitz (e := fun X => sswEnergy energy η X q) (p := p) (by linarith) hr
    (L := 8*K*H) (F := F*H*(p/3)) (G := G*H) (by positivity) (by positivity) (by positivity)
  have hp' : P ∈ fixedCharge r := ⟨hP,rfl⟩
  have hq' : Q ∈ fixedCharge r := ⟨hQ,htr.symm⟩
  have hbulk (X : SpinMatrix) (hx : X ∈ fixedCharge r) (Y : SpinMatrix) (hy : Y ∈ fixedCharge r)
      (mx : (r/4) • (1 : SpinMatrix) ≤ X) (my : (r/4) • (1 : SpinMatrix) ≤ Y) :
      |sswEnergy energy η X q-sswEnergy energy η Y q| ≤ 8*K*H*(hilbertSchmidt (X-Y)/r) := by
    have hfloor {Z : SpinMatrix} (hz : (r/4) • (1 : SpinMatrix) ≤ Z) :
        (Z - (((1/4:ℝ)*r : ℝ) : ℂ) • (1 : SpinMatrix)).PosSemidef := by
      have he : (((1/4:ℝ)*r : ℝ) : ℂ) • (1 : SpinMatrix) = (r/4) • (1 : SpinMatrix) := by
        ext i j
        simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
        congr 1
        norm_cast
        ring
      rw [he]
      exact Matrix.le_iff.mp hz
    apply (minority_fixed_charge_lipschitz rate hr (by norm_num : (0:ℝ) < 1/4) q
      (coulomb_ssw_convex_fixed_charge η loc states hr q) hx hy (hfloor mx) (hfloor my)).trans_eq
    dsimp only [H]
    rw [holderGrowth_eq hr]
    unfold rateGrowth
    dsimp only [r]
    field_simp [hr.ne']
    ring
  have hfrac (X : SpinMatrix) (hx : X ∈ fixedCharge r) (Y : SpinMatrix) (hy : Y ∈ fixedCharge r)
      (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) (1/2)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (1/2)) :=
    (frac hr hx hy q hs ht).2 p hp
  have hang (X : SpinMatrix) (hx : X ∈ fixedCharge r) (S : unitary SpinMatrix) :
      |sswEnergy energy η (Unitary.conjStarAlgAut ℂ SpinMatrix S X) q-sswEnergy energy η X q| ≤
        G*H*hilbertSchmidt ((S : SpinMatrix)-1) := by
    change |sswEnergy energy η ((S : SpinMatrix)*X*star (S : SpinMatrix)) q-sswEnergy energy η X q| ≤
      G*holderGrowth r q*hilbertSchmidt ((S : SpinMatrix)-1)
    simpa only [hx.2] using ang X hx.1 (hx.2.symm ▸ hr) S S.property q
  exact (h hbulk hfrac hang hp' hq').trans_eq (by dsimp only [H, r]; ring)

end TSGA.ManyBody
