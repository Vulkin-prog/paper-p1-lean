module

public import PaperP1.Algebra.QuadraticPolynomialDiagonalization
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # A diagonal quadric with at most two nonzero coefficients factors over an algebraic closure -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DiagonalQuadricFactorization

open MvPolynomial Finset QuadraticPolynomialDiagonalization
open scoped Classical

variable {F : Type*} [Field F] [IsAlgClosed F]

omit [IsAlgClosed F] in
theorem linear_not_unit (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 1) (hP0 : P ≠ 0) :
    ¬IsUnit P := by
  intro hu
  have hd := hP.totalDegree hP0
  have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  omega

theorem binary_not_irreducible (w : Fin 4 → F) (a b : Fin 4) (hab : a ≠ b)
    (ha : w a ≠ 0) (hout : ∀ i, i ≠ a → i ≠ b → w i = 0) :
    ¬Irreducible (diagonal w) := by
  have heq : diagonal w = C (w a) * X a ^ 2 + C (w b) * X b ^ 2 := by
    calc
      _ = ∑ i ∈ ({a, b} : Finset (Fin 4)), C (w i) * X i ^ 2 := by
        apply Eq.symm
        apply sum_subset (subset_univ _)
        intro i _hi hnot
        have hia : i ≠ a := fun h ↦ hnot (by simp [h])
        have hib : i ≠ b := fun h ↦ hnot (by simp [h])
        rw [hout i hia hib, map_zero, zero_mul]
      _ = _ := sum_pair hab
  obtain ⟨α, hα⟩ := IsAlgClosed.isSquare (w a)
  obtain ⟨β, hβ⟩ := IsAlgClosed.isSquare (-(w b))
  have hα0 : α ≠ 0 := by
    intro hz
    apply ha
    rw [hα, hz, mul_zero]
  have hβ' : w b = -(β * β) := by rw [← hβ, neg_neg]
  let A : MvPolynomial (Fin 4) F := C α * X a + C β * X b
  let B : MvPolynomial (Fin 4) F := C α * X a - C β * X b
  have hA : A.IsHomogeneous 1 := (isHomogeneous_C_mul_X α a).add (isHomogeneous_C_mul_X β b)
  have hB : B.IsHomogeneous 1 := (isHomogeneous_C_mul_X α a).sub (isHomogeneous_C_mul_X β b)
  have hmono : Finsupp.single b (1 : ℕ) ≠ Finsupp.single a 1 := by
    intro he
    exact hab ((Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0)).mp he).symm
  have hcA : A.coeff (Finsupp.single a 1) = α := by simp [A, coeff_X, hmono]
  have hcB : B.coeff (Finsupp.single a 1) = α := by simp [B, coeff_X, hmono]
  have hA0 : A ≠ 0 := by
    intro hz
    have hh := congrArg (fun P : MvPolynomial (Fin 4) F ↦ P.coeff (Finsupp.single a 1)) hz
    exact hα0 (by simpa [hcA] using hh)
  have hB0 : B ≠ 0 := by
    intro hz
    have hh := congrArg (fun P : MvPolynomial (Fin 4) F ↦ P.coeff (Finsupp.single a 1)) hz
    exact hα0 (by simpa [hcB] using hh)
  have hf : diagonal w = A * B := by
    rw [heq]
    simp only [hα, hβ', map_mul, map_neg, A, B]
    ring
  intro hirr
  exact (hirr.isUnit_or_isUnit hf).elim (linear_not_unit A hA hA0) (linear_not_unit B hB hB0)

theorem at_least_three_nonzero (w : Fin 4 → F) (hirr : Irreducible (diagonal w)) :
    3 ≤ ((univ : Finset (Fin 4)).filter (fun i ↦ w i ≠ 0)).card := by
  let S := (univ : Finset (Fin 4)).filter (fun i ↦ w i ≠ 0)
  by_contra hn
  change ¬3 ≤ S.card at hn
  have hs : S.card ≤ 2 := by omega
  rcases (show S.card = 0 ∨ S.card = 1 ∨ S.card = 2 by omega) with hz | h1 | h2
  · have hempty : S = ∅ := card_eq_zero.mp hz
    have hw : ∀ i : Fin 4, w i = 0 := by
      intro i
      by_contra hi
      have hm : i ∈ S := mem_filter.mpr ⟨mem_univ _, hi⟩
      rw [hempty] at hm
      exact notMem_empty i hm
    apply hirr.ne_zero
    simp only [diagonal, hw, map_zero, zero_mul, sum_const_zero]
  · obtain ⟨a, ha⟩ := card_eq_one.mp h1
    obtain ⟨b, hb⟩ := exists_ne a
    have hwa : w a ≠ 0 := (mem_filter.mp (show a ∈ S by rw [ha]; simp)).2
    apply binary_not_irreducible w a b (Ne.symm hb) hwa ?_ hirr
    intro i hia _hib
    by_contra hi
    have hm : i ∈ S := mem_filter.mpr ⟨mem_univ _, hi⟩
    rw [ha, mem_singleton] at hm
    exact hia hm
  · obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp h2
    have hwa : w a ≠ 0 := (mem_filter.mp (show a ∈ S by rw [heq]; simp)).2
    apply binary_not_irreducible w a b hab hwa ?_ hirr
    intro i hia hib
    by_contra hi
    have hm : i ∈ S := mem_filter.mpr ⟨mem_univ _, hi⟩
    rw [heq, mem_insert, mem_singleton] at hm
    exact hm.elim hia hib

end PaperP1.DiagonalQuadricFactorization
