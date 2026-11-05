module

public import PaperP1.Diophantine.GeometricProjectiveFibres
public import PaperP1.Diophantine.BidegreeOneCurveCount
public import PaperP1.Algebra.SmallIntegerKernel

/-! # A coarse geometric biform count and the complete second-degree-one case -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricBiformCoarseCount

open Polynomial Finset PaperP1.GeometricProjectiveFibres PaperP1.BidegreeOneFibreCount
  PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.GeometricFactorSwap
  PaperP1.IntegerFactorProjectiveCurve

theorem finite_count (G : ℤ[X][X]) (hG : G ≠ 0) (hY : 0 < degreeY G) (hgeom : Geometric G)
    (S : Finset Point)
    (hprim : ∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
      (s.2 0).natAbs.Coprime (s.2 1).natAbs)
    (hzero : ∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) :
    S.card ≤ (S.image Prod.fst).card * (2 * (degreeY G + 1)) := by
  classical
  have hf (x : Fin 2 → ℤ) (hx : x ∈ S.image Prod.fst) :
      (S.filter (fun s ↦ s.1 = x)).card ≤ 2 * (degreeY G + 1) := by
    obtain ⟨s₀, hs₀, he₀⟩ := mem_image.mp hx
    let T := S.filter (fun s ↦ s.1 = x)
    have hi : Set.InjOn Prod.snd (T : Set Point) := by
      intro s hs t ht he
      exact Prod.ext ((mem_filter.mp hs).2.trans (mem_filter.mp ht).2.symm) he
    have hxp : (x 0).natAbs.Coprime (x 1).natAbs := by rw [← he₀]; exact (hprim s₀ hs₀).1
    rw [← Finset.card_image_of_injOn hi]
    apply primitive_fibre_card G hG hY hgeom x hxp (T.image Prod.snd)
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hy
      exact (hprim s (mem_filter.mp hs).1).2
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hy
      have hx' := (mem_filter.mp hs).2
      simpa only [hx'] using hzero s (mem_filter.mp hs).1
  calc
    S.card = ∑ x ∈ S.image Prod.fst, (S.filter (fun s ↦ s.1 = x)).card := card_eq_sum_card_image _ _
    _ ≤ ∑ _x ∈ S.image Prod.fst, 2 * (degreeY G + 1) := sum_le_sum hf
    _ = _ := by simp

theorem bounded_first_projection (S : Finset Point) (L : ℝ) (hL : 1 ≤ L)
    (hbox : ∀ s ∈ S, ∀ i, |(s.1 i : ℝ)| ≤ L) :
    ((S.image Prod.fst).card : ℝ) ≤ 9 * L ^ 2 := by
  classical
  have hsub : S.image Prod.fst ⊆ PaperP1.SmallIntegerKernel.symmetricBox 2 ⌊L⌋₊ := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (PaperP1.BidegreeOneCurveCount.integer_box_floor _ L (by linarith)).mpr (hbox s hs i)
  have hc : (S.image Prod.fst).card ≤ (2 * ⌊L⌋₊ + 1) ^ 2 := by
    simpa only [PaperP1.SmallIntegerKernel.symmetricBox_card] using Finset.card_le_card hsub
  have hcr : ((S.image Prod.fst).card : ℝ) ≤ (2 * (⌊L⌋₊ : ℝ) + 1) ^ 2 := by exact_mod_cast hc
  have hf : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  have ha : (0 : ℝ) ≤ 2 * (⌊L⌋₊ : ℝ) + 1 := by positivity
  have hb : 2 * (⌊L⌋₊ : ℝ) + 1 ≤ 3 * L := by linarith
  have hm := mul_le_mul hb hb ha (by linarith : (0 : ℝ) ≤ 3 * L)
  nlinarith

theorem coarse_real_count (G : ℤ[X][X]) (hG : G ≠ 0) (hY : 0 < degreeY G) (hgeom : Geometric G)
    (L : ℝ) (hL : 1 ≤ L) (S : Finset Point)
    (hprim : ∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
      (s.2 0).natAbs.Coprime (s.2 1).natAbs)
    (hzero : ∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0)
    (hbox : ∀ s ∈ S, ∀ i, |(s.1 i : ℝ)| ≤ L) :
    (S.card : ℝ) ≤ 18 * ((degreeY G : ℝ) + 1) * L ^ 2 := by
  have hc := finite_count G hG hY hgeom S hprim hzero
  have hcr : (S.card : ℝ) ≤ ((S.image Prod.fst).card : ℝ) * (2 * ((degreeY G : ℝ) + 1)) := by
    exact_mod_cast hc
  calc
    (S.card : ℝ) ≤ ((S.image Prod.fst).card : ℝ) * (2 * ((degreeY G : ℝ) + 1)) := hcr
    _ ≤ (9 * L ^ 2) * (2 * ((degreeY G : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (bounded_first_projection S L hL hbox) (by positivity)
    _ = _ := by ring

theorem height_pos (G : ℤ[X][X]) (hG : G ≠ 0) : 0 < height G := by
  by_contra! hh
  apply hG
  ext i j
  apply Int.natAbs_eq_zero.mp
  have hc := coefficient_natAbs_le_height G i j
  omega

theorem second_degree_one (G : ℤ[X][X]) (hG : G ≠ 0) (hY : degreeY G = 1) (hgeom : Geometric G)
    (ε : ℝ) (hε : 0 < ε) (L : ℝ) (hL : 1 ≤ L) (S : Finset Point)
    (hprim : ∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
      (s.2 0).natAbs.Coprime (s.2 1).natAbs)
    (hzero : ∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0)
    (hbox : ∀ s ∈ S, ∀ i, |(s.1 i : ℝ)| ≤ L) :
    (S.card : ℝ) ≤ 36 * L ^ ((2 : ℝ) + ε) * (height G : ℝ) ^ ε := by
  have hc := coarse_real_count G hG (by omega) hgeom L hL S hprim hzero hbox
  have hc' : (S.card : ℝ) ≤ 36 * L ^ 2 := by
    have hn : (18 : ℝ) * (1 + 1) = 36 := by norm_num
    simpa only [hY, Nat.cast_one, hn] using hc
  have hp : L ^ 2 ≤ L ^ ((2 : ℝ) + ε) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hL
      (by linarith : (2 : ℝ) ≤ 2 + ε)
  have hh : (1 : ℝ) ≤ height G := by exact_mod_cast (height_pos G hG)
  have hheight : 1 ≤ (height G : ℝ) ^ ε := Real.one_le_rpow hh hε.le
  calc
    (S.card : ℝ) ≤ 36 * L ^ 2 := hc'
    _ ≤ 36 * L ^ ((2 : ℝ) + ε) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hheight

end PaperP1.GeometricBiformCoarseCount
