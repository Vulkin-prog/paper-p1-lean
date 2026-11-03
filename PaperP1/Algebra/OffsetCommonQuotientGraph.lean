module

public import PaperP1.Algebra.CommonQuotientGraph
public import PaperP1.Algebra.FormalWordDegrees
public import Mathlib.RingTheory.Coprime.Lemmas

/-! # Reduced rational graphs and all root matches from actual disjoint offset equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetCommonQuotientGraph

open Polynomial Finset PaperP1.FormalWordPolynomials

variable {F : Type*} [Field F] [CharZero F]

theorem disjoint_coprime (I J : Finset ℤ) (hdisj : Disjoint I J) :
    IsCoprime (linearOver F I) (linearOver F J) := by
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  have hne : -(i : F) ≠ -(j : F) := by
    intro hneg
    have heq : i = j := Int.cast_injective (neg_injective hneg)
    subst j
    exact Finset.disjoint_left.mp hdisj hi hj
  simpa only [map_neg, sub_neg_eq_add] using
    (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)))

def scaled (b : F) (I : Finset ℤ) : F[X] := C b * linearOver F I

omit [CharZero F] in
theorem scaled_degree (b : F) (hb : b ≠ 0) (I : Finset ℤ) :
    (scaled b I).natDegree = I.card := by
  rw [scaled, natDegree_C_mul hb, FormalWordDegrees.linear_degree]

theorem scaled_coprime (b c : F) (hb : b ≠ 0) (hc : c ≠ 0) (I J : Finset ℤ)
    (hdisj : Disjoint I J) : IsCoprime (scaled b I) (scaled c J) := by
  rw [scaled, scaled, isCoprime_mul_units_left ((isUnit_iff_ne_zero.mpr hb).map C)
    ((isUnit_iff_ne_zero.mpr hc).map C)]
  exact disjoint_coprime I J hdisj

omit [CharZero F] in
theorem scaled_root (b : F) (I : Finset ℤ) (i : ℤ) (hi : i ∈ I) :
    (scaled b I).eval (-(i : F)) = 0 := by
  simp only [scaled, eval_mul, eval_C, linearOver, eval_prod]
  rw [Finset.prod_eq_zero_iff.mpr ⟨i, hi, by simp⟩, mul_zero]

variable {E ι : Type*} [Field E] [Algebra F E]

theorem exists_reduced_graph (a : ℕ) (ha : 0 < a) (good : Finset ι) (hgood : 2 ≤ good.card)
    (I : ι → Finset ℤ) (j : ι → ℤ) (b : ι → F)
    (hdisj : (good : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ good, (I ν).card = a)
    (hb : ∀ ν ∈ good, b ν ≠ 0) (x y t : E) (hx : Transcendental F x)
    (hcommon : ∀ ν ∈ good, algebraMap F E (b ν) * aeval x (linearOver F (I ν)) =
      t * (y + (j ν : E))) :
    ∃ p q : F[X], q ≠ 0 ∧ IsCoprime p q ∧ max p.natDegree q.natDegree = a ∧
      aeval x p = y * aeval x q ∧
      ∀ ν ∈ good, ∀ z ∈ I ν, p.eval (-(z : F)) = -(j ν : F) * q.eval (-(z : F)) := by
  classical
  obtain ⟨ν₀, hν₀, ν₁, hν₁, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < good.card)
  let A := scaled (b ν₀) (I ν₀)
  let B := scaled (b ν₁) (I ν₁)
  have hA : A.natDegree = a := (scaled_degree _ (hb ν₀ hν₀) _).trans (hcard ν₀ hν₀)
  have hB : B.natDegree = a := (scaled_degree _ (hb ν₁ hν₁) _).trans (hcard ν₁ hν₁)
  have hcop : IsCoprime A B := scaled_coprime _ _ (hb ν₀ hν₀) (hb ν₁ hν₁) _ _
    (hdisj hν₀ hν₁ hne)
  have hscaled (ν) (hν : ν ∈ good) : aeval x (scaled (b ν) (I ν)) =
      t * (y + algebraMap F E (j ν : F)) := by
    simpa only [scaled, map_mul, aeval_C, map_intCast] using hcommon ν hν
  have hj : (j ν₀ : F) ≠ (j ν₁ : F) := CommonQuotientGraph.distinct_constants
    x y t hx A B _ _ hcop (by omega) (hscaled ν₀ hν₀) (hscaled ν₁ hν₁)
  refine ⟨CommonQuotientGraph.numerator A B (j ν₀ : F) (j ν₁ : F),
    CommonQuotientGraph.denominator A B, CommonQuotientGraph.denominator_ne_zero A B hcop (by omega),
    CommonQuotientGraph.coprime A B _ _ hj hcop, CommonQuotientGraph.exact_degree A B _ _ hj a hA hB,
    CommonQuotientGraph.graph_evaluation x y t A B _ _ (hscaled ν₀ hν₀) (hscaled ν₁ hν₁), ?_⟩
  intro ν hν z hz
  exact CommonQuotientGraph.root_match x y t hx A B (scaled (b ν) (I ν)) _ _ _ _
    (hscaled ν₀ hν₀) (hscaled ν₁ hν₁) (hscaled ν hν) (scaled_root _ _ z hz)

theorem exists_reduced_graph_of_quotients (a : ℕ) (ha : 0 < a) (good : Finset ι) (hgood : 2 ≤ good.card)
    (I : ι → Finset ℤ) (j : ι → ℤ) (c : ι → F)
    (hdisj : (good : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ good, (I ν).card = a)
    (hc : ∀ ν ∈ good, c ν ≠ 0) (x y t : E) (hx : Transcendental F x)
    (hden : ∀ ν ∈ good, y + (j ν : E) ≠ 0)
    (hquot : ∀ ν ∈ good, aeval x (linearOver F (I ν)) / (y + (j ν : E)) =
      algebraMap F E (c ν) * t) :
    ∃ p q : F[X], q ≠ 0 ∧ IsCoprime p q ∧ max p.natDegree q.natDegree = a ∧
      aeval x p = y * aeval x q ∧
      ∀ ν ∈ good, ∀ z ∈ I ν, p.eval (-(z : F)) = -(j ν : F) * q.eval (-(z : F)) := by
  apply exists_reduced_graph a ha good hgood I j (fun ν ↦ (c ν)⁻¹) hdisj hcard
    (fun ν hν ↦ inv_ne_zero (hc ν hν)) x y t hx
  intro ν hν
  have h := (div_eq_iff (hden ν hν)).mp (hquot ν hν)
  have hcE : algebraMap F E (c ν) ≠ 0 := (map_ne_zero (algebraMap F E)).mpr (hc ν hν)
  rw [map_inv₀, h]
  simp only [← mul_assoc, inv_mul_cancel₀ hcE, one_mul]

end PaperP1.OffsetCommonQuotientGraph
