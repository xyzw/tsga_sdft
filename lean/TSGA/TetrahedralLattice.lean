import TSGA.TetrahedronVolume
import Mathlib.Order.WellFounded
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The 24 tetrahedra of a translated cube

Order the absolute coordinates and choose the signs of the two largest.
The sign of the smallest coordinate is free inside the reference tetrahedron.
-/

noncomputable section
namespace TSGA.SSW

open Set MeasureTheory

/-- The cube contains six coordinate orders and four choices of signs. -/
abbrev CubeOrientation := Equiv.Perm (Fin 3) × Bool × Bool
abbrev LatticeTile := (Fin 3 → ℤ) × CubeOrientation

theorem card_cubeOrientation : Fintype.card CubeOrientation = 24 := by
  simp [CubeOrientation, Fintype.card_perm, Nat.factorial]

private def signedCoord (b : Bool) (a : ℝ) := if b then a else -a

private theorem abs_signed (b : Bool) (a : ℝ) : |signedCoord b a| = |a| := by
  cases b <;> simp [signedCoord]

private def signAt (o : CubeOrientation) : Fin 3 → Bool := ![o.2.1,o.2.2,true]

/-- The spatial chart sends the cell to the centered reference tetrahedron. -/
def latticeChart (ℓ : ℝ) (p : LatticeTile) (x : Position) : Position :=
  let z := fun i => x i - ℓ*(p.1 i : ℝ)
  WithLp.toLp 2 ![signedCoord p.2.2.1 (z (p.2.1 0)) - 3*ℓ/8,
    signedCoord p.2.2.2 (z (p.2.1 1)) - ℓ/4, z (p.2.1 2)]

private theorem chart_mem_iff (ℓ : ℝ) (p : LatticeTile) (x : Position) :
    latticeChart ℓ p x ∈ tetrahedron ℓ ↔
      let z := fun i => x i - ℓ*(p.1 i : ℝ)
      |z (p.2.1 2)| < signedCoord p.2.2.2 (z (p.2.1 1)) ∧
      signedCoord p.2.2.2 (z (p.2.1 1)) < signedCoord p.2.2.1 (z (p.2.1 0)) ∧
      signedCoord p.2.2.1 (z (p.2.1 0)) < ℓ/2 := by
  simp [latticeChart, tetrahedron]

private theorem chart_sub (ℓ : ℝ) (p : LatticeTile) (x y : Position) (i : Fin 3) :
    (latticeChart ℓ p x - latticeChart ℓ p y) i =
      signedCoord (signAt p.2 i) ((x-y) (p.2.1 i)) := by
  fin_cases i <;> simp [latticeChart, signAt, signedCoord] <;> split <;> ring

theorem latticeChart_isometry (ℓ : ℝ) (p : LatticeTile) : Isometry (latticeChart ℓ p) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, chart_sub]
  have sq_signed (b : Bool) (v : ℝ) : signedCoord b v ^ 2 = v^2 := by cases b <;> simp [signedCoord]
  simp only [sq_signed]
  exact Equiv.sum_comp p.2.1 (fun i => ((x-y) i)^2)

private theorem latticeChart_surjective (ℓ : ℝ) (p : LatticeTile) : Function.Surjective (latticeChart ℓ p) := by
  intro y
  let z : Fin 3 → ℝ := ![signedCoord p.2.2.1 (y 0 + 3*ℓ/8),signedCoord p.2.2.2 (y 1 + ℓ/4),y 2]
  refine ⟨WithLp.toLp 2 (fun i => z (p.2.1.symm i) + ℓ*(p.1 i : ℝ)), ?_⟩
  ext i
  fin_cases i <;> simp [latticeChart, z, signedCoord] <;> split <;> ring

/-- The chart carries volume on a lattice cell to volume on the reference shape. -/
def latticeChartEquiv (ℓ : ℝ) (p : LatticeTile) : Position ≃ᵢ Position where
  toEquiv := Equiv.ofBijective (latticeChart ℓ p) ⟨(latticeChart_isometry ℓ p).injective,
    latticeChart_surjective ℓ p⟩
  isometry_toFun := latticeChart_isometry ℓ p

theorem latticeChart_preserving (ℓ : ℝ) (p : LatticeTile) :
    MeasurePreserving (latticeChart ℓ p) volume volume := by
  let e := latticeChartEquiv ℓ p
  have hr : MeasurePreserving e.toRealLinearIsometryEquiv (volume : Measure Position) volume :=
    e.toRealLinearIsometryEquiv.measurePreserving
  have he : (fun x => e.toRealLinearIsometryEquiv x + e 0) = latticeChart ℓ p := by
    funext x
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply, sub_add_cancel]
    rfl
  rw [← he]
  exact (measurePreserving_add_right volume (e 0)).comp hr

private theorem cell_order {ℓ : ℝ} {p : LatticeTile} {x : Position}
    (h : latticeChart ℓ p x ∈ tetrahedron ℓ) :
    let z := fun i => x i - ℓ*(p.1 i : ℝ)
    StrictAnti (fun j => |z (p.2.1 j)|) ∧ (∀ i, |z i| < ℓ/2) ∧
      0 < signedCoord p.2.2.1 (z (p.2.1 0)) ∧ 0 < signedCoord p.2.2.2 (z (p.2.1 1)) := by
  let z := fun i => x i - ℓ*(p.1 i : ℝ)
  obtain ⟨h₂,h₁,h₀⟩ := (chart_mem_iff ℓ p x).mp h
  have hp₁ := (abs_nonneg _).trans_lt h₂
  have hp₀ := hp₁.trans h₁
  have a₀ := (abs_signed p.2.2.1 (z (p.2.1 0))).symm.trans (abs_of_pos hp₀)
  have a₁ := (abs_signed p.2.2.2 (z (p.2.1 1))).symm.trans (abs_of_pos hp₁)
  have h10 : |z (p.2.1 1)| < |z (p.2.1 0)| := a₁.trans_lt (h₁.trans_eq a₀.symm)
  have h21 : |z (p.2.1 2)| < |z (p.2.1 1)| := h₂.trans_eq a₁.symm
  have hmax : |z (p.2.1 0)| < ℓ/2 := a₀.trans_lt h₀
  refine ⟨?_,?_,hp₀,hp₁⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact h10 | exact h21 | exact h21.trans h10 | exact False.elim ((by decide : ¬ _) hij)
  · intro i
    obtain ⟨j,rfl⟩ := p.2.1.surjective i
    fin_cases j <;> first | exact hmax | exact h10.trans hmax | exact h21.trans (h10.trans hmax)

private theorem lattice_index_unique {ℓ x : ℝ} {m n : ℤ} (hℓ : 0 < ℓ)
    (hm : |x-ℓ*(m:ℝ)| < ℓ/2) (hn : |x-ℓ*(n:ℝ)| < ℓ/2) : m = n := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm (le_of_not_ge hmn)).symm
  by_contra h
  have hsucc : m+1 ≤ n := by omega
  have hreal : (m:ℝ)+1 ≤ n := by exact_mod_cast hsucc
  have gap := mul_le_mul_of_nonneg_left hreal hℓ.le
  obtain ⟨hm₀,hm₁⟩ := abs_lt.mp hm
  obtain ⟨hn₀,hn₁⟩ := abs_lt.mp hn
  linarith

/-- The actual open cells are disjoint throughout the translated lattice. -/
theorem latticeChart_disjoint {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Pairwise fun i j : LatticeTile => Disjoint (latticeChart ℓ i ⁻¹' tetrahedron ℓ)
      (latticeChart ℓ j ⁻¹' tetrahedron ℓ) := by
  rintro ⟨m,σ,b,c⟩ ⟨n,τ,d,e⟩ hne
  apply disjoint_left.mpr
  intro x hx hy
  apply hne
  obtain ⟨hs,hcube,hb,hc⟩ := cell_order hx
  obtain ⟨ht,hcube',hd,he⟩ := cell_order hy
  have hmn : m=n := funext fun i => lattice_index_unique hℓ (hcube i) (hcube' i)
  subst n
  let f := fun i : Fin 3 => |x i-ℓ*(m i:ℝ)|
  change StrictAnti (fun i => f (σ i)) at hs
  change StrictAnti (fun i => f (τ i)) at ht
  have heq : (fun i => f (σ i)) = (fun i => f (τ i)) :=
    (hs.range_inj ht).mp (by simp only [Set.range_comp', Equiv.range_eq_univ])
  have hinj : Function.Injective f := by
    intro u v h
    obtain ⟨i,rfl⟩ := σ.surjective u
    obtain ⟨j,rfl⟩ := σ.surjective v
    exact congrArg σ (hs.injective h)
  have hp : σ=τ := Equiv.ext fun i => hinj (congrFun heq i)
  subst τ
  have signs {u v : Bool} {a : ℝ} (h : 0 < signedCoord u a) (h' : 0 < signedCoord v a) : u=v := by
    cases u <;> cases v <;> simp_all [signedCoord] <;> linarith
  obtain rfl : b=d := signs hb hd
  obtain rfl : c=e := signs hc he
  rfl

private theorem ae_linear_ne (L : Position →ₗ[ℝ] ℝ) (a : ℝ) (hw : ∃ v, L v = 1) :
    ∀ᵐ x : Position, L x ≠ a := by
  let S := AffineSubspace.comap L.toAffineMap (AffineSubspace.mk' a (⊥ : Submodule ℝ ℝ))
  have hmem (x : Position) : x ∈ S ↔ L x = a := by
    simp [S, AffineSubspace.mem_comap, AffineSubspace.mem_mk', vsub_eq_sub, sub_eq_zero]
  have hn : S ≠ ⊤ := by
    obtain ⟨u,hu⟩ := hw
    rintro h
    have hall (x : Position) : L x = a := (hmem x).1 (by rw [h]; trivial)
    have h0 := hall 0
    rw [map_zero] at h0
    linarith [hall u]
  filter_upwards [compl_mem_ae_iff.mpr (Measure.addHaar_affineSubspace volume S hn)] with x hx he
  exact hx ((hmem x).2 he)

private theorem generic_cube_coordinates (ℓ : ℝ) :
    ∀ᵐ x : Position, ∀ m : Fin 3 → ℤ,
      (∀ i, x i ≠ ℓ*(m i:ℝ) - ℓ/2) ∧ Function.Injective (fun i => |x i-ℓ*(m i:ℝ)|) := by
  rw [ae_all_iff]
  intro m
  let L (i : Fin 3) := EuclideanSpace.projₗ (𝕜 := ℝ) i
  have single (i : Fin 3) : ∃ v, L i v = 1 := ⟨EuclideanSpace.single i 1, by simp [L]⟩
  have side := ae_all_iff.mpr fun i => ae_linear_ne (L i) (ℓ*(m i:ℝ)-ℓ/2) (single i)
  have pair (i j : Fin 3) : ∀ᵐ x : Position, i ≠ j →
      |x i-ℓ*(m i:ℝ)| ≠ |x j-ℓ*(m j:ℝ)| := by
    by_cases h : i=j
    · simp [h]
    have hs : ∃ v, (L i - L j) v = 1 := ⟨EuclideanSpace.single i 1, by simp [L,Ne.symm h]⟩
    have ha : ∃ v, (L i + L j) v = 1 := ⟨EuclideanSpace.single i 1, by simp [L,Ne.symm h]⟩
    filter_upwards [ae_linear_ne _ (ℓ*(m i:ℝ)-ℓ*(m j:ℝ)) hs,
      ae_linear_ne _ (ℓ*(m i:ℝ)+ℓ*(m j:ℝ)) ha] with x hd hp _ habs
    change x i-x j ≠ _ at hd
    change x i+x j ≠ _ at hp
    rcases abs_eq_abs.mp habs with h' | h'
    · exact hd (by linarith)
    · exact hp (by linarith)
  filter_upwards [side, ae_all_iff.mpr (fun i => ae_all_iff.mpr (pair i))] with x hs hp
  exact ⟨hs, fun {i j} hij => by_contra fun h => hp i j h hij⟩

/-- The open cells cover almost every point, with a unique lattice and
orientation label. Ties in the absolute coordinate ordering and cube faces
belong to a countable union of affine planes. -/
theorem latticeChart_ae_unique {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ x : Position, ∃! p : LatticeTile, latticeChart ℓ p x ∈ tetrahedron ℓ := by
  filter_upwards [generic_cube_coordinates ℓ] with x hx
  let m (i : Fin 3) : ℤ := ⌊x i/ℓ+1/2⌋
  let z (i : Fin 3) := x i-ℓ*(m i:ℝ)
  obtain ⟨hw,hinj⟩ := hx m
  have box (i : Fin 3) : |z i| < ℓ/2 := by
    have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x i / ℓ + 1/2)) hℓ.le
    have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x i / ℓ + 1/2)) hℓ
    change (m i:ℝ)*ℓ ≤ (x i/ℓ+1/2)*ℓ at hlo
    change (x i/ℓ+1/2)*ℓ < ((m i:ℝ)+1)*ℓ at hhi
    simp only [add_mul, div_mul_cancel₀ _ hℓ.ne', one_mul] at hlo hhi
    dsimp [z]
    apply abs_lt.mpr
    exact ⟨lt_of_le_of_ne (by linarith) (by intro h; exact hw i (by linarith)), by linarith⟩
  let f : Fin 3 → ℝ := fun i => -|z i|
  let σ := Tuple.sort f
  have hj : Function.Injective f := fun i j h => hinj (neg_inj.mp h)
  have ord := (Tuple.monotone_sort f).strictMono_of_injective (hj.comp σ.injective)
  let b (i : Fin 3) : Bool := decide (0 ≤ z (σ i))
  have hb (i : Fin 3) : signedCoord (b i) (z (σ i)) = |z (σ i)| := by
    by_cases h : 0 ≤ z (σ i)
    · simp [b,signedCoord,h,abs_of_nonneg h]
    · simp [b,signedCoord,h,abs_of_neg (lt_of_not_ge h)]
  let p : LatticeTile := (m,σ,b 0,b 1)
  have inside : latticeChart ℓ p x ∈ tetrahedron ℓ := by
    rw [chart_mem_iff]
    change |z (σ 2)| < signedCoord (b 1) (z (σ 1)) ∧
      signedCoord (b 1) (z (σ 1)) < signedCoord (b 0) (z (σ 0)) ∧
      signedCoord (b 0) (z (σ 0)) < ℓ/2
    simp only [hb]
    have h₁ : -|z (σ 1)| < -|z (σ 2)| := ord (by decide : (1:Fin 3) < 2)
    have h₀ : -|z (σ 0)| < -|z (σ 1)| := ord (by decide : (0:Fin 3) < 1)
    exact ⟨by linarith,by linarith,box _⟩
  exact ⟨p,inside,fun j hj => by_contra fun h =>
    disjoint_left.mp (latticeChart_disjoint hℓ h) hj inside⟩

/-- The fundamental cube in physical space, translated by a lattice vector. -/
def latticeCube (ℓ : ℝ) (m : Fin 3 → ℤ) : Set Position :=
  {x | ∀ i, |x i - ℓ*(m i:ℝ)| < ℓ/2}

theorem latticeChart_cell_subset_cube {ℓ : ℝ} (p : LatticeTile) :
    latticeChart ℓ p ⁻¹' tetrahedron ℓ ⊆ latticeCube ℓ p.1 := fun _ hx => (cell_order hx).2.1

def latticeShift (ℓ : ℝ) : (Fin 3 → ℤ) →+ Position where
  toFun m := WithLp.toLp 2 (fun i => ℓ*(m i:ℝ))
  map_zero' := by ext; simp
  map_add' m n := by ext; simp [mul_add]

theorem latticeCube_measurable (ℓ : ℝ) (m : Fin 3 → ℤ) : MeasurableSet (latticeCube ℓ m) := by
  rw [latticeCube, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i : Fin 3 => (isOpen_lt
    ((EuclideanSpace.proj i).continuous.sub continuous_const).abs continuous_const).measurableSet)

theorem latticeCube_fundamental {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsAddFundamentalDomain (latticeShift ℓ).range (latticeCube ℓ 0) volume := by
  refine ⟨(latticeCube_measurable _ _).nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [latticeChart_ae_unique hℓ] with x hx
    obtain ⟨⟨m,o⟩,h,_⟩ := hx
    refine ⟨⟨latticeShift ℓ (-m),⟨-m,rfl⟩⟩,?_⟩
    intro i
    have hm : |x i - ℓ*(m i : ℝ)| < ℓ/2 := latticeChart_cell_subset_cube _ h i
    change |(latticeShift ℓ (-m) + x) i - ℓ*((0 : Fin 3 → ℤ) i:ℝ)| < _
    simpa [latticeShift,sub_eq_add_neg,add_comm] using hm
  · rintro ⟨u,m,rfl⟩ ⟨v,n,rfl⟩ hne
    apply Disjoint.aedisjoint
    apply disjoint_left.mpr
    intro x hx hy
    rw [mem_vadd_set_iff_neg_vadd_mem] at hx hy
    have coord (k : Fin 3 → ℤ) (h : - (⟨latticeShift ℓ k,⟨k,rfl⟩⟩ : (latticeShift ℓ).range) +ᵥ x ∈
        latticeCube ℓ 0) (i : Fin 3) : |x i-ℓ*(k i:ℝ)| < ℓ/2 := by
      have ha := h i
      change |(-latticeShift ℓ k + x) i-ℓ*((0 : Fin 3 → ℤ) i:ℝ)| < ℓ/2 at ha
      simpa [sub_eq_add_neg,add_comm,latticeShift] using ha
    exact hne (Subtype.ext (congrArg (latticeShift ℓ)
      (funext fun i => lattice_index_unique hℓ (coord m hx i) (coord n hy i))))

theorem latticeCube_eq_cells_ae {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin 3 → ℤ) :
    latticeCube ℓ m =ᵐ[volume] ⋃ o : CubeOrientation, latticeChart ℓ (m,o) ⁻¹' tetrahedron ℓ := by
  filter_upwards [latticeChart_ae_unique hℓ] with x hx
  constructor
  · intro h
    obtain ⟨⟨n,o⟩,hn,_⟩ := hx
    have hc := (cell_order hn).2.1
    have hnm : n=m := funext fun i => lattice_index_unique hℓ (hc i) (h i)
    subst n
    exact mem_iUnion.mpr ⟨o,hn⟩
  · intro h
    obtain ⟨o,ho⟩ := mem_iUnion.mp h
    exact (cell_order ho).2.1

theorem latticeCube_volume {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin 3 → ℤ) :
    regionVolume (latticeCube ℓ m) = ℓ^3 := by
  let S (o : CubeOrientation) := latticeChart ℓ (m,o) ⁻¹' tetrahedron ℓ
  have hm (o) : MeasurableSet (S o) := (tetrahedron_open ℓ).measurableSet.preimage
    (latticeChart_isometry ℓ (m,o)).continuous.measurable
  have measure_cell (o) : volume (S o) = volume (tetrahedron ℓ) :=
    (latticeChart_preserving ℓ (m,o)).measure_preimage (tetrahedron_open ℓ).measurableSet.nullMeasurableSet
  have hfin := (ENNReal.toReal_pos_iff.mp (tetrahedron_volume_pos hℓ)).2.ne
  have cs (o) : (∫ _ in S o, (1:ℝ)) = regionVolume (tetrahedron ℓ) := by
    simp [regionVolume,measureReal_def,measure_cell]
  have he : regionVolume (latticeCube ℓ m) = ∫ _ in latticeCube ℓ m, (1:ℝ) := by simp [regionVolume]
  rw [he,setIntegral_congr_set (latticeCube_eq_cells_ae hℓ m)]
  change (∫ _ in ⋃ o, S o, (1:ℝ)) = _
  rw [integral_iUnion_fintype hm
    (fun i j h => latticeChart_disjoint hℓ (show ((m,i) : LatticeTile) ≠ (m,j) from fun e => h (congrArg Prod.snd e)))
    (fun o => integrableOn_const ((measure_cell o).trans_ne hfin))]
  change (∑ o : CubeOrientation, ∫ _ in S o, (1:ℝ)) = ℓ^3
  simp_rw [cs]
  simp only [Finset.sum_const, Finset.card_univ, card_cubeOrientation, nsmul_eq_mul, tetrahedron_volume hℓ]
  norm_num
  ring

theorem latticeChart_dilate (t ℓ : ℝ) (p : LatticeTile) (x : Position) :
    latticeChart (t*ℓ) p (t • x) = t • latticeChart ℓ p x := by
  obtain ⟨m,σ,b,c⟩ := p
  cases b <;> cases c <;> ext i <;> fin_cases i <;> simp [latticeChart,signedCoord] <;> ring

end TSGA.SSW
