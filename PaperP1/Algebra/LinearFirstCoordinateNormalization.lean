module

public import PaperP1.Algebra.FirstCoordinateShear

/-! # Exact normalization of a nonzero leading linear coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearFirstCoordinateNormalization

open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

theorem normalize (L : MvPolynomial (Fin (n + 1)) F) (hL : L.IsHomogeneous 1)
    (ha : L.coeff (Finsupp.single 0 1) ≠ 0) :
    ∃ b : Fin n → F, FirstCoordinateShear.substitute b L =
      C (L.coeff (Finsupp.single 0 1)) * X 0 := by
  let a := L.coeff (Finsupp.single 0 1)
  let c : Fin n → F := fun i ↦ L.coeff (Finsupp.single i.succ 1)
  let b : Fin n → F := fun i ↦ -(c i / a)
  have hc (i : Fin n) : a * b i = -(c i) := by
    dsimp only [b]
    field_simp [show a ≠ 0 from ha]
  have hcancel : C a * FirstCoordinateShear.form b = -FirstCoordinateShear.form c := by
    rw [FirstCoordinateShear.form, mul_sum, FirstCoordinateShear.form, ← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [← mul_assoc, ← map_mul, hc, map_neg, neg_mul]
  have hrepr : L = C a * X 0 + FirstCoordinateShear.form c := by
    simpa only [Fin.sum_univ_succ, FirstCoordinateShear.form, a, c] using
      HomogeneousLinearForm.eq_sum L hL
  refine ⟨b, ?_⟩
  change FirstCoordinateShear.substitute b L = C a * X 0
  conv_lhs => rw [hrepr]
  rw [map_add, map_mul, FirstCoordinateShear.substitute_X_zero,
    FirstCoordinateShear.substitute_form]
  rw [show FirstCoordinateShear.substitute b (C a) = C a from
    (FirstCoordinateShear.substitute b).commutes a]
  rw [mul_add, hcancel]
  ring

theorem exists_nonzero_coefficient (L : MvPolynomial (Fin (n + 1)) F)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) :
    ∃ i : Fin (n + 1), L.coeff (Finsupp.single i 1) ≠ 0 := by
  by_contra hn
  have hz : ∀ i : Fin (n + 1), L.coeff (Finsupp.single i 1) = 0 := by
    intro i
    exact Classical.not_not.mp (fun h ↦ hn ⟨i, h⟩)
  apply hL0
  rw [HomogeneousLinearForm.eq_sum L hL]
  simp only [hz, map_zero, zero_mul, sum_const_zero]

end PaperP1.LinearFirstCoordinateNormalization
