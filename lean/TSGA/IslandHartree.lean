import TSGA.LevyLieb
import Mathlib.MeasureTheory.Integral.Prod

/-! # Coulomb cost of randomizing a trial state

Averaging disjoint outside and inside states requires subtracting the
Hartree energy of the averaged charge. Fubini identifies the discrepancy
with the Hartree energy of the centered charge field in Appendix C.
-/

noncomputable section

namespace TSGA.ManyBody

open MeasureTheory MeasureTheory.Measure Filter

abbrev PairSpace := Position × Position
abbrev pairVolume : Measure PairSpace := (volume : Measure Position).prod volume

def directKernel (f g : Position → ℝ) (z : PairSpace) := f z.1 * g z.2 / ‖z.1 - z.2‖

theorem hartree_eq_pair (f : Position → ℝ) (hi : Integrable (directKernel f f) pairVolume) :
    hartree f = (∫ z, directKernel f f z ∂pairVolume)/2 := by
  rw [integral_prod _ hi]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def JointDirectIntegrable (μ : Measure Ω) (R : Ω → Position → ℝ) : Prop :=
  Integrable (fun p : Ω × PairSpace => directKernel (R p.1) (R p.1) p.2) (μ.prod pairVolume)

theorem expect_hartree_as_pair {R : Ω → Position → ℝ} (h : JointDirectIntegrable μ R) :
    (∫ ω, hartree (R ω) ∂μ) = (∫ z : PairSpace, ∫ ω, directKernel (R ω) (R ω) z ∂μ ∂pairVolume)/2 := by
  calc
    _ = ∫ ω, (∫ z : PairSpace, directKernel (R ω) (R ω) z ∂pairVolume)/2 ∂μ :=
      integral_congr_ae (h.prod_right_ae.mono fun ω hi => hartree_eq_pair _ hi)
    _ = _ := by
      rw [integral_div, integral_integral_swap (f := fun ω z => directKernel (R ω) (R ω) z) h]

theorem integrable_hartree_of_joint {R : Ω → Position → ℝ} (h : JointDirectIntegrable μ R) :
    Integrable (fun ω => hartree (R ω)) μ :=
  (h.integral_prod_left.div_const 2).congr (h.prod_right_ae.mono fun ω hi => (hartree_eq_pair (R ω) hi).symm)

/-- Polarization of the random two-point kernel. The charge can have either
sign and the formula includes the diagonal under Lean's division convention. -/
private theorem centered_scalar {X Y : Ω → ℝ} {a b d : ℝ}
    (hx : Integrable X μ) (hy : Integrable Y μ) (ha : (∫ ω, X ω ∂μ) = a)
    (hb : (∫ ω, Y ω ∂μ) = b) (hxy : Integrable (fun ω => X ω * Y ω / d) μ) :
    (∫ ω, (X ω-a)*(Y ω-b)/d ∂μ) = (∫ ω, X ω*Y ω/d ∂μ) - a*b/d := by
  have he (ω) : (X ω-a)*(Y ω-b)/d = ((X ω*Y ω/d-X ω*(b/d))-Y ω*(a/d))+a*b/d := by ring
  simp_rw [he]
  erw [integral_add ((hxy.sub (hx.mul_const (b/d))).sub (hy.mul_const (a/d))) (integrable_const (a*b/d)),
    integral_sub (hxy.sub (hx.mul_const (b/d))) (hy.mul_const (a/d)), integral_sub hxy (hx.mul_const (b/d)),
    integral_mul_const (b/d) X, integral_mul_const (a/d) Y, ha, hb, integral_const]
  simp
  ring

/-- Expected electrostatic energy equals electrostatic energy at the mean
plus the expected fluctuation energy. -/
theorem expect_hartree_centered {R : Ω → Position → ℝ} {m : Position → ℝ}
    (mean : ∀ᵐ x, Integrable (fun ω => R ω x) μ ∧ (∫ ω, R ω x ∂μ) = m x)
    (hr : JointDirectIntegrable μ R) (hm : Integrable (directKernel m m) pairVolume)
    (hc : JointDirectIntegrable μ (fun ω x => R ω x-m x)) :
    (∫ ω, hartree (R ω) ∂μ) = hartree m + ∫ ω, hartree (fun x => R ω x-m x) ∂μ := by
  rw [expect_hartree_as_pair hr, expect_hartree_as_pair hc, hartree_eq_pair m hm]
  have he : ∀ᵐ z : PairSpace ∂pairVolume, (∫ ω, directKernel (fun x => R ω x-m x) (fun x => R ω x-m x) z ∂μ)
      = (∫ ω, directKernel (R ω) (R ω) z ∂μ) - directKernel m m z := by
    filter_upwards [hr.prod_left_ae, (quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae mean,
      (quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae mean] with z hxy hx hy
    exact centered_scalar hx.1 hy.1 hx.2 hy.2 hxy
  rw [integral_congr_ae he, integral_sub hr.integral_prod_right hm]
  ring

/-- Coulomb term between two independent clusters with the two specified
charges. Each unordered pair joining the two clusters is counted once. -/
def crossDirect (f g : Position → ℝ) : ℝ := ∫ z : PairSpace, directKernel f g z ∂pairVolume

theorem hartree_sum {f g : Position → ℝ} (hf : Integrable (directKernel f f) pairVolume)
    (hg : Integrable (directKernel g g) pairVolume) (hfg : Integrable (directKernel f g) pairVolume) :
    hartree (f+g) = hartree f + hartree g + crossDirect f g := by
  have hswap (z : PairSpace) : directKernel g f z = directKernel f g z.swap := by
    simp [directKernel, norm_sub_rev z.2 z.1, mul_comm]
  have hgf : Integrable (directKernel g f) pairVolume := by
    exact hfg.swap.congr (ae_of_all _ fun z => (hswap z).symm)
  have he : directKernel (f+g) (f+g) =
      directKernel f f + directKernel g g + directKernel f g + directKernel g f := by
    funext z
    simp only [directKernel, Pi.add_apply]
    ring
  have hsum : Integrable (directKernel (f+g) (f+g)) pairVolume := he ▸ (((hf.add hg).add hfg).add hgf)
  rw [hartree_eq_pair _ hsum, hartree_eq_pair _ hf, hartree_eq_pair _ hg, he]
  simp only [Pi.add_apply]
  erw [integral_add ((hf.add hg).add hfg) hgf, integral_add (hf.add hg) hfg, integral_add hf hg]
  have hi : (∫ z : PairSpace, directKernel g f z ∂pairVolume) = crossDirect f g := by
    simp_rw [hswap]
    exact integral_prod_swap _
  rw [hi]
  unfold crossDirect
  ring

/-- Absolute integrability for the polarization identity of three signed
charge fields. -/
structure TripleDirectIntegrable (f g h : Position → ℝ) : Prop where
  first : Integrable (directKernel f f) pairVolume
  second : Integrable (directKernel g g) pairVolume
  third : Integrable (directKernel h h) pairVolume
  total : Integrable (directKernel (f+g+h) (f+g+h)) pairVolume
  fg : Integrable (directKernel (f-g) (f-g)) pairVolume
  fh : Integrable (directKernel (f-h) (f-h)) pairVolume
  gh : Integrable (directKernel (g-h) (g-h)) pairVolume

/-- Positivity of the Coulomb form on signed charges is the analytic
input. Polarization then bounds the three-field fluctuation. -/
theorem hartree_three_le {f g h : Position → ℝ} (dom : TripleDirectIntegrable f g h)
    (positive : ∀ u, Integrable (directKernel u u) pairVolume → 0 ≤ hartree u) :
    hartree (f+g+h) ≤ 3*(hartree f+hartree g+hartree h) := by
  let Q := fun u : Position → ℝ => directKernel u u
  have identity (z : PairSpace) : Q (f+g+h) z + Q (f-g) z + Q (f-h) z + Q (g-h) z =
      3*(Q f z + Q g z + Q h z) := by
    simp only [Q, directKernel, Pi.add_apply, Pi.sub_apply]
    ring
  have hsum : (∫ z, Q (f+g+h) z + Q (f-g) z + Q (f-h) z + Q (g-h) z ∂pairVolume) =
      ∫ z, 3*(Q f z+Q g z+Q h z) ∂pairVolume := integral_congr_ae (ae_of_all _ identity)
  dsimp only [Q] at hsum
  erw [integral_add ((dom.total.add dom.fg).add dom.fh) dom.gh, integral_add (dom.total.add dom.fg) dom.fh,
    integral_add dom.total dom.fg, integral_const_mul, integral_add (dom.first.add dom.second) dom.third,
    integral_add dom.first dom.second] at hsum
  have hfg := positive _ dom.fg
  have hfh := positive _ dom.fh
  have hgh := positive _ dom.gh
  rw [hartree_eq_pair _ dom.fg] at hfg
  rw [hartree_eq_pair _ dom.fh] at hfh
  rw [hartree_eq_pair _ dom.gh] at hgh
  rw [hartree_eq_pair _ dom.total, hartree_eq_pair _ dom.first, hartree_eq_pair _ dom.second, hartree_eq_pair _ dom.third]
  linarith only [hsum,hfg,hfh,hgh]

omit [IsProbabilityMeasure μ] in
/-- Entrywise averaging of scalar partition weights yields the full
spin-density constraint of the barycenter, including off-diagonal spin
coherences. -/
theorem feasible_of_island_weights (bar : MixedState) (B D : Position → SpinMatrix)
    (a b : Ω → Position → ℝ)
    (weights : ∀ᵐ x, Integrable (fun ω => a ω x) μ ∧ Integrable (fun ω => b ω x) μ ∧
      (∫ ω, a ω x ∂μ) = 1 ∧ (∫ ω, b ω x ∂μ) = 1)
    (average : ∀ᵐ x, ∀ i j, bar.matrixDensity x i j =
      ∫ ω, a ω x • (B x i j) + b ω x • (D x i j) ∂μ) : feasible (B+D) bar := by
  filter_upwards [weights, average] with x hw hbar
  ext i j
  rw [hbar i j, integral_add (hw.1.smul_const _) (hw.2.1.smul_const _),
    integral_smul_const, integral_smul_const, hw.2.2.1, hw.2.2.2, one_smul, one_smul]
  rfl

/-- Data of one geometric localization and the independent-cluster product.
The two-body trace identity records the cross interaction explicitly. -/
structure IslandTrial (μ : Measure Ω) (M : Position → SpinMatrix) where
  bar : MixedState
  feasible_bar : feasible M bar
  outside : Ω → MixedState
  inside : Ω → MixedState
  f : Ω → Position → ℝ
  g : Ω → Position → ℝ
  f_density : ∀ᵐ ω ∂μ, f ω =ᵐ[volume] fun x => ((outside ω).matrixDensity x).trace.re
  g_density : ∀ᵐ ω ∂μ, g ω =ᵐ[volume] fun x => ((inside ω).matrixDensity x).trace.re
  mean : ∀ᵐ x, Integrable (fun ω => f ω x+g ω x) μ ∧
    (∫ ω, f ω x+g ω x ∂μ) = (M x).trace.re
  hf : JointDirectIntegrable μ f
  hg : JointDirectIntegrable μ g
  hfg : ∀ᵐ ω ∂μ, Integrable (directKernel (f ω) (g ω)) pairVolume
  hr : JointDirectIntegrable μ (fun ω => f ω+g ω)
  hm : Integrable (directKernel (fun x => (M x).trace.re) (fun x => (M x).trace.re)) pairVolume
  hc : JointDirectIntegrable μ (fun ω x => (f ω+g ω) x - (M x).trace.re)
  hout : Integrable (fun ω => (outside ω).kinetic + (outside ω).interaction) μ
  hin : Integrable (fun ω => (inside ω).kinetic + (inside ω).interaction) μ
  average : bar.kinetic + bar.interaction = ∫ ω,
    (outside ω).kinetic + (outside ω).interaction +
      ((inside ω).kinetic + (inside ω).interaction) + crossDirect (f ω) (g ω) ∂μ

variable {M : Position → SpinMatrix}

def IslandTrial.outsideEnergy (h : IslandTrial μ M) : ℝ :=
  ∫ ω, (h.outside ω).kinetic + (h.outside ω).interaction - hartree (h.f ω) ∂μ

def IslandTrial.insideEnergy (h : IslandTrial μ M) : ℝ :=
  ∫ ω, (h.inside ω).kinetic + (h.inside ω).interaction - hartree (h.g ω) ∂μ

def IslandTrial.fluctuation (h : IslandTrial μ M) : ℝ :=
  ∫ ω, hartree (fun x => h.f ω x + h.g ω x - (M x).trace.re) ∂μ

/-- Appendix C, equation `eq:three_terms`. The trial ensemble is the
barycenter of independent-cluster products. Its kinetic and interaction
formulas are the ordinary one- and two-body trace identities. -/
theorem IslandTrial.energy_le (trial : IslandTrial μ M) :
    energy M ≤ trial.outsideEnergy + trial.insideEnergy + trial.fluctuation := by
  rcases trial with ⟨bar, hbar, outside, inside, f, g, _, _, mean, hf, hg, hfg, hr, hm, hc, hout, hin, average⟩
  let o := fun ω => (outside ω).kinetic + (outside ω).interaction - hartree (f ω)
  let i := fun ω => (inside ω).kinetic + (inside ω).interaction - hartree (g ω)
  have ho : Integrable o μ := hout.sub (integrable_hartree_of_joint hf)
  have hi : Integrable i μ := hin.sub (integrable_hartree_of_joint hg)
  have hadd : bar.kinetic + bar.interaction = ∫ ω, o ω+i ω+hartree (f ω+g ω) ∂μ := by
    rw [average]
    apply integral_congr_ae
    filter_upwards [hf.prod_right_ae, hg.prod_right_ae, hfg] with ω h₁ h₂ h₁₂
    rw [hartree_sum h₁ h₂ h₁₂]
    dsimp [o,i]
    ring
  erw [integral_add (ho.add hi) (integrable_hartree_of_joint hr), integral_add ho hi,
    expect_hartree_centered mean hr hm hc] at hadd
  change levyLieb M - hartree (fun x => (M x).trace.re) ≤ (∫ ω, o ω ∂μ) + (∫ ω, i ω ∂μ) + ∫ ω, hartree (fun x => (f ω+g ω) x - (M x).trace.re) ∂μ
  simp only [Pi.add_apply]
  linarith only [levyLieb_le hbar, hadd]

end TSGA.ManyBody
