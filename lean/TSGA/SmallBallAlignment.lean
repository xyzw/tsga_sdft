import TSGA.SmallBallMatrices
import TSGA.BallTruncatedGradient
import TSGA.CoulombRotationReplacement
import TSGA.ShiftedComparison

/-! # Choosing the frozen matrices and spin axes jointly on a small ball -/

noncomputable section
namespace TSGA.ManyBody
open MeasureTheory TSGA.Localization Metric Set Matrix
open scoped ComplexOrder MatrixOrder

/-- Both comparisons use one spin frame. In the shifted case the density
already has a spectral floor. In the gapped case the extremal eigenvalues
are expressed in the common frame at the center. -/
inductive SmallAxisBranch {N : Density} {R : ℝ} {c : Position} (s : SmallBallScale N R c) :
    Density → SpinMatrix → SpinMatrix → Prop where
  | shifted (floor : ∀ x ∈ closedBall c R, (s.r/8) • (1 : SpinMatrix) ≤ N.matrix x) :
      SmallAxisBranch s N (N.matrix c - s.omega 1 • 1) (N.matrix c + s.omega 1 • 1)
  | gapped (hr : 0 < s.r)
      (minor : ∃ y ∈ closedBall c R, ∃ i : Fin 2, (N.positive y).1.eigenvalues i ≤ s.r/8)
      (E : SpectralExtrema N (closedBall c R)) :
      SmallAxisBranch s (referenceDensity N c) (E.lowerMatrix c) (E.upperMatrix c)

structure SmallBallMatrices {N : Density} {R : ℝ} {c : Position} (s : SmallBallScale N R c) where
  aligned : Density
  low : SpinMatrix
  high : SpinMatrix
  construction : SmallAxisBranch s aligned low high
  low_pos : low.PosSemidef
  high_pos : high.PosSemidef
  ordered : ∀ x ∈ closedBall c R, low ≤ aligned.matrix x ∧ aligned.matrix x ≤ high ∧
    hilbertSchmidt (aligned.matrix x-low) ≤ 3*s.omega 1 ∧ hilbertSchmidt (high-aligned.matrix x) ≤ 3*s.omega 1
  power : ∀ {B : SpinMatrix} (hB : B.PosSemidef), B = low ∨ B = high →
    ∀ {a : ℝ}, 0 < a → a ≤ 1 → ∀ x ∈ closedBall c R,
      hilbertSchmidt (hB.1.cfc (fun z => z^a)-N.power a x) ≤ 48*s.omega a
  matrix_dist : ∀ {B : SpinMatrix}, B = low ∨ B = high → ∀ x ∈ closedBall c R,
    hilbertSchmidt (B-N.matrix x) ≤ 3*s.omega 1
  traces : ∀ x ∈ closedBall c R, low.trace.re ≤ N.charge x ∧ N.charge x ≤ high.trace.re
  minority : ∀ {ν : ℝ}, 0 ≤ ν → ν ≤ 1/2 → MinorityBound ν N →
    (ν*s.r/8) • (1 : SpinMatrix) ≤ low ∧ (ν*s.r/8) • (1 : SpinMatrix) ≤ high

private theorem smul_one_mono {a b : ℝ} (h : a ≤ b) :
    a • (1 : SpinMatrix) ≤ b • (1 : SpinMatrix) := by
  simpa only [inSpinFrame_const] using (inSpinFrame_mono (1 : unitary SpinMatrix)
    (a := fun _ => a) (b := fun _ => b) fun _ => h)

theorem continuous_minority_floor {N : Density} (hc : Continuous N.matrix) {ν : ℝ} (h : MinorityBound ν N) :
    ∀ x, (ν*N.charge x) • (1 : SpinMatrix) ≤ N.matrix x := by
  let v := fun x => N.matrix x - ((ν*N.charge x : ℝ) : ℂ) • (1 : SpinMatrix)
  have cn : Continuous N.charge := by unfold Density.charge; fun_prop
  have cv : Continuous v := by dsimp [v]; fun_prop
  have hdense := Measure.dense_of_ae (μ := volume) h
  intro x
  have hx := hdense x
  change x ∈ closure (v ⁻¹' {A : SpinMatrix | A.PosSemidef}) at hx
  rw [(Matrix.posSemidef_is_closed.preimage cv).closure_eq] at hx
  exact Matrix.le_iff.mpr hx

private theorem trace_mono {A B : SpinMatrix} (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
  have t := (RCLike.nonneg_iff.mp (Matrix.le_iff.mp h).trace_nonneg).1
  change 0 ≤ (B-A).trace.re at t
  simpa only [Matrix.trace_sub,Complex.sub_re,sub_nonneg] using t

open scoped Matrix.Norms.Frobenius in
private theorem shift_dist {N : Density} {R : ℝ} {c : Position} (s : SmallBallScale N R c)
    (hc : c ∈ closedBall c R) {x : Position} (hx : x ∈ closedBall c R) {t : ℝ} (ht : |t| ≤ s.omega 1) :
    hilbertSchmidt (N.matrix c+t • (1 : SpinMatrix)-N.matrix x) ≤ 3*s.omega 1 := by
  have hI : ‖(1 : SpinMatrix)‖ ≤ 2 := by
    rw [← SSW.hs_eq_norm]
    simpa using SSW.hilbertSchmidt_le_trace (PosSemidef.one : (1 : SpinMatrix).PosSemidef)
  have o := s.matrix_osc hc hx
  rw [SSW.hs_eq_norm] at o ⊢
  rw [show N.matrix c+t • (1:SpinMatrix)-N.matrix x = t • (1:SpinMatrix) + (N.matrix c-N.matrix x) by abel]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs]
  linarith only [o,mul_le_mul ht hI (norm_nonneg _) ((abs_nonneg t).trans ht)]

private theorem shift_power_constant {u r : ℝ} (hr : 0 < r) (hu : 0 < u) (_hle : u ≤ 1) :
    (u*(r/16)^(u-1))*(3*(1/u*r^(1-u))) ≤ 48 := by
  have hcancel : r^(u-1)*r^(1-u)=1 := by rw [← Real.rpow_add hr]; simp
  have hnum : (16 : ℝ)^(1-u) ≤ 16 := by
    calc
      _ ≤ (16 : ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := Real.rpow_one _
  have e : (r/16)^(u-1) = r^(u-1) * (16:ℝ)^(1-u) := by
    rw [Real.div_rpow hr.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num : 0 ≤ (16:ℝ))]
    congr 2
    ring
  rw [e]
  calc
    _ = 3*(16:ℝ)^(1-u)*(r^(u-1)*r^(1-u)) := by field_simp
    _ ≤ _ := by rw [hcancel,mul_one]; linarith only [hnum]

private theorem shift_power {N : Density} {R : ℝ} {c : Position} (s : SmallBallScale N R c)
    (hc : c ∈ closedBall c R) {x : Position} (hx : x ∈ closedBall c R) {t : ℝ} (ht : |t| ≤ s.omega 1)
    (floor : ∀ y ∈ closedBall c R, (s.r/8) • (1 : SpinMatrix) ≤ N.matrix y)
    (hB : (N.matrix c+t • (1 : SpinMatrix)).PosSemidef) {a : ℝ} (ha : 0 < a) (hle : a ≤ 1) :
    hilbertSchmidt (hB.1.cfc (fun z => z^a)-N.power a x) ≤ 48*s.omega a := by
  rcases s.r_nonneg.eq_or_lt with hz | hr
  · have hzero : s.omega 1 = 0 := le_antisymm (by linarith only [s.small,hz]) (s.omega_nonneg _ zero_lt_one)
    have ht0 : t = 0 := abs_nonpos_iff.mp (hzero ▸ ht)
    subst t
    have e : N.matrix c + (0:ℝ) • (1:SpinMatrix) = N.matrix c := by simp
    have cong {A B : SpinMatrix} (hh : A=B) (hA : A.PosSemidef) (hB' : B.PosSemidef) :
        hA.1.cfc (fun z => z^a) = hB'.1.cfc (fun z => z^a) := by subst B; rfl
    rw [cong e hB (N.positive c)]
    exact (s.osc a ha c hc x hx).trans (by linarith only [s.omega_nonneg _ ha])
  · have h := shifted_power_comparison N hc hx hr s.small ht (fun _ h _ k => s.matrix_osc h k) floor
    obtain ⟨_,est⟩ := h
    apply (est ha hle).trans
    have scalar := s.omega_one_le a ha hle
    have coeff : 0 ≤ a*(s.r/16)^(a-1) := mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _)
    calc
      _ ≤ (a*(s.r/16)^(a-1))*(3*((1/a*s.r^(1-a))*s.omega a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left scalar (by norm_num)) coeff
      _ = ((a*(s.r/16)^(a-1))*(3*(1/a*s.r^(1-a))))*s.omega a := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (shift_power_constant hr ha hle) (s.omega_nonneg _ ha)

set_option maxHeartbeats 600000 in
theorem smallBallMatrices_nonempty {N : Density} {R : ℝ} {c : Position} (s : SmallBallScale N R c)
    (hR : 0 < R) (cont : Continuous N.matrix) : Nonempty (SmallBallMatrices s) := by
  classical
  let K := closedBall c R
  have hc : c ∈ K := mem_closedBall_self hR.le
  let δ := s.omega 1
  have hd : 0 ≤ δ := s.omega_nonneg _ zero_lt_one
  have floorOrGap : (∀ y ∈ K, (s.r/8) • (1:SpinMatrix) ≤ N.matrix y) ∨
      ∃ y ∈ K, ∃ i : Fin 2, (N.positive y).1.eigenvalues i ≤ s.r/8 := by
    by_contra! h
    obtain ⟨y,hy,fail⟩ := h.1
    apply fail
    have e : inSpinFrame (N.positive y).1.eigenvectorUnitary (N.positive y).1.eigenvalues = N.matrix y :=
      (N.positive y).1.spectral_theorem.symm
    rw [← e]
    exact (inSpinFrame_floor_iff ..).2 fun i => (h.2 y hy i).le
  by_cases floor : ∀ y ∈ K, (s.r/8) • (1:SpinMatrix) ≤ N.matrix y
  · let low := N.matrix c-δ • (1:SpinMatrix)
    let high := N.matrix c+δ • (1:SpinMatrix)
    have comp (x) (hx : x ∈ K) := shifted_comparison N hc hx s.r_nonneg s.small
      (fun _ h _ k => s.matrix_osc h k) floor
    have nonneg : 0 ≤ (s.r/16) • (1:SpinMatrix) :=
      (PosSemidef.one.smul (div_nonneg s.r_nonneg (by norm_num))).nonneg
    have lowpos := Matrix.nonneg_iff_posSemidef.mp (nonneg.trans (comp c hc).1)
    have highpos := Matrix.nonneg_iff_posSemidef.mp (nonneg.trans (comp c hc).2.2.2)
    have loweq : low = N.matrix c+(-δ) • (1:SpinMatrix) := by simp [low,sub_eq_add_neg]
    have lowdiff (x) (hx : x ∈ K) : hilbertSchmidt (low-N.matrix x) ≤ 3*δ := by
      rw [loweq]
      exact shift_dist s hc hx (by rw [abs_neg,abs_of_nonneg hd])
    have highdiff (x) (hx : x ∈ K) : hilbertSchmidt (high-N.matrix x) ≤ 3*δ :=
      shift_dist s hc hx (by rw [abs_of_nonneg hd])
    refine ⟨⟨N,low,high,.shifted floor,lowpos,highpos,?_,?_,?_,?_,?_⟩⟩
    · intro x hx
      exact ⟨(comp x hx).2.1,(comp x hx).2.2.1, (SSW.hs_sub_comm (N.matrix x) low).le.trans (lowdiff x hx), highdiff x hx⟩
    · intro B hb sel a ha ha' x hx
      rcases sel with rfl | rfl
      · have eq (M : SpinMatrix) (hm : M.PosSemidef) (he : M = N.matrix c+(-δ) • (1:SpinMatrix)) :
            hilbertSchmidt (hm.1.cfc (fun z => z^a)-N.power a x) ≤ 48*s.omega a := by
          subst M
          exact shift_power s hc hx (by rw [abs_neg,abs_of_nonneg hd]) floor hm ha ha'
        exact eq low hb loweq
      · exact shift_power s hc hx (by rw [abs_of_nonneg hd]) floor hb ha ha'
    · intro B sel x hx
      rcases sel with rfl | rfl
      exacts [lowdiff x hx,highdiff x hx]
    · intro x hx
      exact ⟨trace_mono (comp x hx).2.1, trace_mono (comp x hx).2.2.1⟩
    · intro ν hn hν _
      have hscale := mul_le_mul_of_nonneg_right hν s.r_nonneg
      have hh := smul_one_mono (show ν*s.r/8 ≤ s.r/16 by linarith only [hscale])
      exact ⟨hh.trans (comp c hc).1,hh.trans (comp c hc).2.2.2⟩
  · have minor := floorOrGap.resolve_left floor
    have hr : 0 < s.r := by
      apply lt_of_le_of_ne s.r_nonneg
      intro h
      have hf (y) (_ : y ∈ K) : (s.r/8) • (1:SpinMatrix) ≤ N.matrix y := by simpa [← h] using (N.positive y).nonneg
      exact floor hf
    let E := SpectralExtrema.onCompact N (isCompact_closedBall c R) ⟨c,hc⟩ cont.continuousOn
    have orders := spectral_ordered_pairs E c hd (fun x hx y hy i => by
      have hi := eigenvalue_power_distance (N.positive x) (N.positive y) (zero_le_one : (0:ℝ) ≤ 1) i
      simpa only [Real.rpow_one] using hi.trans (s.osc 1 zero_lt_one x hx y hy))
    refine ⟨⟨referenceDensity N c,E.lowerMatrix c,E.upperMatrix c,.gapped hr minor E,E.lower_pos c,E.upper_pos c,?_,?_,?_,?_,?_⟩⟩
    · intro x hx
      have h := orders x hx
      exact ⟨h.1,h.2.1,by linarith only [h.2.2.1,hd],by linarith only [h.2.2.2,hd]⟩
    · intro B hb sel a ha _ x hx
      have h := E.power_comparison c hc ha (s.omega_nonneg a ha) (s.osc _ ha) hx
      rcases sel with rfl | rfl
      · exact h.1.trans (by linarith only [s.omega_nonneg a ha])
      · exact h.2.trans (by linarith only [s.omega_nonneg a ha])
    · intro B sel x hx
      have h := E.power_comparison c hc zero_lt_one hd (s.osc 1 zero_lt_one) hx
      have one {A : SpinMatrix} (hA : A.PosSemidef) : hA.1.cfc (fun z => z^(1:ℝ)) = A :=
        density_power_one (constantSpinDensity A hA) c
      have transfer (B : SpinMatrix) (hB : B.PosSemidef)
          (hb : hilbertSchmidt (hB.1.cfc (fun t => t^(1:ℝ)) - N.power 1 x) ≤ 3*δ) :
          hilbertSchmidt (B-N.matrix x) ≤ 3*δ := by
        rw [one hB, density_power_one N x] at hb
        exact hb
      rcases sel with rfl | rfl
      · exact transfer _ (E.lower_pos c) h.1
      · exact transfer _ (E.upper_pos c) h.2
    · exact fun x hx => ⟨(E.trace_bounds c hx s.cap).1,(E.trace_bounds c hx s.cap).2.1⟩
    · intro ν hn _ hν
      have hh := E.minority_at_peak c hn (show δ ≤ s.r/4 by linarith only [s.small,s.r_nonneg])
        s.peak (fun _ h _ k => s.matrix_osc h k) (fun y _ => continuous_minority_floor cont hν y)
      have hscale := smul_one_mono (show ν*s.r/8 ≤ ν*s.r/2 by linarith only [mul_nonneg hn s.r_nonneg])
      exact ⟨hscale.trans hh.1,hscale.trans hh.2⟩

namespace SmallBallMatrices
variable {N : Density} {R : ℝ} {c : Position} {s : SmallBallScale N R c} (m : SmallBallMatrices s)

theorem trace_range {B : SpinMatrix} (sel : B = m.low ∨ B = m.high) :
    s.r/2 ≤ B.trace.re ∧ B.trace.re ≤ 2*s.r := by
  obtain ⟨z,hz,he⟩ := s.peak
  have hd := (SSW.abs_trace_re_le_hilbertSchmidt (B-N.matrix z)).trans
    (mul_le_mul_of_nonneg_left (m.matrix_dist sel z hz) (by norm_num : (0:ℝ) ≤ 2))
  rw [Matrix.trace_sub,Complex.sub_re] at hd
  change |B.trace.re - N.charge z| ≤ _ at hd
  rw [he] at hd
  constructor <;> linarith only [(abs_le.mp hd).1,(abs_le.mp hd).2,s.small,s.r_nonneg]

theorem minority_domain {ν : ℝ} (hn : 0 ≤ ν) (hν : ν ≤ 1/2) (hm : MinorityBound ν N)
    {B : SpinMatrix} (_hB : B.PosSemidef) (sel : B = m.low ∨ B = m.high) :
    (B - (((ν/16)*B.trace.re : ℝ) : ℂ) • (1:SpinMatrix)).PosSemidef := by
  have hf := m.minority hn hν hm
  have t := mul_le_mul_of_nonneg_left (m.trace_range sel).2 hn
  have hscale := smul_one_mono (show ν/16*B.trace.re ≤ ν*s.r/8 by linarith only [t])
  apply Matrix.le_iff.mp
  rcases sel with rfl | rfl
  exacts [hscale.trans hf.1, hscale.trans hf.2]

/-- The same choice of spin frame works for every orientation and dilation
on the ball. Its dependence on the taper enters only through its kinetic cost. -/
def axisCost (t : SpiralTaper (closedBall c R)) (S : MatrixGradient) (p : ℝ) : ℝ := by
  classical
  exact if m.aligned = N then 0 else
    alignmentCost t S s.r ((96/(1/p))*(s.omega (1/p)/s.r^(1/p)))

theorem axes (t : SpiralTaper (closedBall c R)) (shape : Integrable t.shape)
    {p θ : ℝ} {S T : MatrixGradient} (reg : DensityRegular N p θ S T) (hp : 1 ≤ p)
    (hR : 0 < R) (sob : SobolevCompositionOn (closedBall c R)) :
    TileAxisChoice t N m.aligned (m.axisCost t S p) := by
  classical
  let d := (96/(1/p))*(s.omega (1/p)/s.r^(1/p))
  have all {A lo hi} (br : SmallAxisBranch s A lo hi) :
      TileAxisChoice t N A (if A = N then 0 else alignmentCost t S s.r d) := by
    by_cases eq : A = N
    · rw [ite_eq_left eq,eq]
      exact .unchanged
    rw [ite_eq_right eq]
    cases br with
    | shifted => exact (eq rfl).elim
    | gapped hr minor E =>
      have hp₀ : 0 < p := by linarith
      have hk := kineticDensity_integrable reg
      exact .polarized hR hr sob s.cap s.peak minor
        (fun x hx y hy => (s.matrix_osc hx hy).trans s.small) (one_div_pos.mpr hp₀)
        ((div_le_one hp₀).2 hp) (fun x hx => s.osc _ (one_div_pos.mpr hp₀) _ hx _ (mem_closedBall_self hR.le))
        (fun i j k => PhaseLocalization.weakPartialOn_restrict MeasurableSet.univ (subset_univ _) (reg.sqrt_gradient i j k))
        reg.charge_L1.aestronglyMeasurable.aemeasurable shape hk.aestronglyMeasurable.aemeasurable
        (hk.bdd_mul shape.aestronglyMeasurable (c := 1)
          (ae_of_all _ fun x => (Real.norm_of_nonneg (t.range x).1).le.trans (t.range x).2))
  exact all m.construction

theorem axisCost_le (t : SpiralTaper (closedBall c R)) (S : MatrixGradient) (p : ℝ) :
    m.axisCost t S p ≤ alignmentCost t S s.r ((96/(1/p))*(s.omega (1/p)/s.r^(1/p))) := by
  classical
  unfold axisCost
  split_ifs
  · unfold alignmentCost
    have kin : 0 ≤ ∫ x, t.shape x*kineticDensity S x :=
      integral_nonneg fun x => mul_nonneg (t.range x).1 (sq_nonneg _)
    have sh : 0 ≤ ∫ x, t.shape x := integral_nonneg fun x => (t.range x).1
    positivity [s.r_nonneg]
  · exact le_rfl

end SmallBallMatrices

/-- Joint choice of the continuous density and both comparison matrices from
the essential small-oscillation test, including vacuum balls. -/
theorem smallBallMatrices_of_regular {D : Density} {S T : MatrixGradient} {p θ κ C R : ℝ}
    (morrey : MatrixSobolevMorrey p C) (hp : 3 < p) (hθ : 0 < θ) (hle : θ ≤ 1)
    (reg : DensityRegular D p θ S T) (hR : 0 < R) (hk : κ ≤ θ/64) (c : Position)
    (small : SmallPowerOscillation D θ κ R c) :
    ∃ N : Density, N.matrix =ᵐ[volume] D.matrix ∧ Continuous N.matrix ∧
      (∀ a : ℝ, 0 < a → Continuous (N.power a)) ∧
      ∃ s : SmallBallScale N R c, s.omega θ ≤ κ*s.r^θ ∧ Nonempty (SmallBallMatrices s) := by
  obtain ⟨N,e,cn,cp⟩ := morrey.density_representative hp hθ reg
  obtain ⟨s,h⟩ := smallBallScale_of_regular e cn cp hR hθ hle hk small
  exact ⟨N,e,cn,cp,s,h,smallBallMatrices_nonempty s hR cn⟩

end TSGA.ManyBody
