module

public import PaperP1.Algebra.RationalInterpolationUniqueness
public import PaperP1.Algebra.IntegralRationalInterpolation

/-! # A reduced rational function fixed by a bounded integer grid has an integral presentation of grid-bounded height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformRationalInterpolation

open Polynomial PaperP1.RationalInterpolationUniqueness PaperP1.IntegralRationalInterpolation

theorem exists_integral_presentation (a B : ℕ) (hB : 1 ≤ B) (x y : Fin (2 * a + 1) → ℤ)
    (hinj : Function.Injective x) (hx : ∀ j, (x j).natAbs ≤ B) (hy : ∀ j, (y j).natAbs ≤ B)
    (p q : ℚ[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hgrid : ∀ j, p.eval (x j : ℚ) = (y j : ℚ) * q.eval (x j : ℚ)) :
    ∃ P Q : ℤ[X], Q ≠ 0 ∧ P.natDegree ≤ a ∧ Q.natDegree ≤ a ∧
      (∀ n, (P.coeff n).natAbs ≤ heightBound a B) ∧ (∀ n, (Q.coeff n).natAbs ≤ heightBound a B) ∧
      IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) ∧
      max (P.map (Int.castRingHom ℚ)).natDegree (Q.map (Int.castRingHom ℚ)).natDegree = a ∧
      ∃ δ : ℚ, δ ≠ 0 ∧ P.map (Int.castRingHom ℚ) = C δ * p ∧ Q.map (Int.castRingHom ℚ) = C δ * q := by
  obtain ⟨P, Q, hQ0, hP, hQ, hpc, hqc, hgridZ⟩ := exists_pair_nonzero_denominator a B hB x y hinj hx hy
  have hgridQ (j) : (P.map (Int.castRingHom ℚ)).eval (x j : ℚ) =
      (y j : ℚ) * (Q.map (Int.castRingHom ℚ)).eval (x j : ℚ) := by
    change (P.map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) (x j)) =
      (Int.castRingHom ℚ) (y j) * (Q.map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) (x j))
    rw [eval_map_apply, eval_map_apply, ← map_mul]
    exact congrArg (Int.castRingHom ℚ) (hgridZ j)
  obtain ⟨δ, hpδ, hqδ⟩ := unique_up_to_scalar_family a (fun j ↦ (x j : ℚ)) (fun j ↦ (y j : ℚ))
    (Int.cast_injective.comp hinj) p q (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ))
    hq0 hcop hdegree (natDegree_map_le.trans hP) (natDegree_map_le.trans hQ)
    (by simp only [Fintype.card_fin]; omega) hgrid hgridQ
  have hδ : δ ≠ 0 := by
    intro hz
    have hm : Q.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hQ0
    exact hm (hqδ.trans (by simp only [hz, C_0, zero_mul]))
  have hu : IsUnit (C δ : ℚ[X]) := (isUnit_iff_ne_zero.mpr hδ).map C
  refine ⟨P, Q, hQ0, hP, hQ, hpc, hqc, ?_, ?_, δ, hδ, hpδ, hqδ⟩
  · rw [hpδ, hqδ, isCoprime_mul_unit_left_left hu, isCoprime_mul_unit_left_right hu]
    exact hcop
  · rw [hpδ, hqδ, natDegree_C_mul hδ, natDegree_C_mul hδ]
    exact hdegree

end PaperP1.UniformRationalInterpolation
