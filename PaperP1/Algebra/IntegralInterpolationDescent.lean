module

public import PaperP1.Algebra.RationalInterpolationUniqueness
public import PaperP1.Algebra.IntegralRationalInterpolation
public import Mathlib.Algebra.Polynomial.FieldDivision

/-! # A reduced rational function over any characteristic-zero field fitting the rational grid descends to a bounded integral presentation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralInterpolationDescent

open Polynomial PaperP1.RationalInterpolationUniqueness PaperP1.IntegralRationalInterpolation

variable {F : Type*} [Field F] [CharZero F]

theorem rational_images_coprime (P Q : ℤ[X])
    (hcop : IsCoprime (P.map (Int.castRingHom F)) (Q.map (Int.castRingHom F))) :
    IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) := by
  have hc : (Rat.castHom F).comp (Int.castRingHom ℚ) = Int.castRingHom F := Subsingleton.elim _ _
  apply (Polynomial.isCoprime_map (Rat.castHom F)).mp
  simpa only [Polynomial.map_map, hc] using hcop

theorem exists_integral_presentation (a B : ℕ) (hB : 1 ≤ B) (x y : Fin (2 * a + 1) → ℤ)
    (hinj : Function.Injective x) (hx : ∀ j, (x j).natAbs ≤ B) (hy : ∀ j, (y j).natAbs ≤ B)
    (p q : F[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hgrid : ∀ j, p.eval (x j : F) = (y j : F) * q.eval (x j : F)) :
    ∃ P Q : ℤ[X], Q ≠ 0 ∧ P.natDegree ≤ a ∧ Q.natDegree ≤ a ∧
      (∀ n, (P.coeff n).natAbs ≤ heightBound a B) ∧ (∀ n, (Q.coeff n).natAbs ≤ heightBound a B) ∧
      IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) ∧
      max (P.map (Int.castRingHom F)).natDegree (Q.map (Int.castRingHom F)).natDegree = a ∧
      ∃ δ : F, δ ≠ 0 ∧ P.map (Int.castRingHom F) = C δ * p ∧ Q.map (Int.castRingHom F) = C δ * q := by
  obtain ⟨P, Q, hQ0, hP, hQ, hpc, hqc, hgridZ⟩ := exists_pair_nonzero_denominator a B hB x y hinj hx hy
  have hgridQ (j) : (P.map (Int.castRingHom F)).eval (x j : F) =
      (y j : F) * (Q.map (Int.castRingHom F)).eval (x j : F) := by
    change (P.map (Int.castRingHom F)).eval ((Int.castRingHom F) (x j)) =
      (Int.castRingHom F) (y j) * (Q.map (Int.castRingHom F)).eval ((Int.castRingHom F) (x j))
    rw [eval_map_apply, eval_map_apply, ← map_mul]
    exact congrArg (Int.castRingHom F) (hgridZ j)
  obtain ⟨δ, hpδ, hqδ⟩ := unique_up_to_scalar_family a (fun j ↦ (x j : F)) (fun j ↦ (y j : F))
    (Int.cast_injective.comp hinj) p q (P.map (Int.castRingHom F)) (Q.map (Int.castRingHom F))
    hq0 hcop hdegree (natDegree_map_le.trans hP) (natDegree_map_le.trans hQ)
    (by simp only [Fintype.card_fin]; omega) hgrid hgridQ
  have hδ : δ ≠ 0 := by
    intro hz
    have hm : Q.map (Int.castRingHom F) ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hQ0
    exact hm (hqδ.trans (by simp only [hz, C_0, zero_mul]))
  have hu : IsUnit (C δ : F[X]) := (isUnit_iff_ne_zero.mpr hδ).map C
  refine ⟨P, Q, hQ0, hP, hQ, hpc, hqc, ?_, ?_, δ, hδ, hpδ, hqδ⟩
  · apply rational_images_coprime (F := F) P Q
    rw [hpδ, hqδ, isCoprime_mul_unit_left_left hu, isCoprime_mul_unit_left_right hu]
    exact hcop
  · rw [hpδ, hqδ, natDegree_C_mul hδ, natDegree_C_mul hδ]
    exact hdegree

theorem scalar_degree_eq (P : ℤ[X]) (p : F[X]) (δ : F) (hδ : δ ≠ 0)
    (hpδ : P.map (Int.castRingHom F) = C δ * p) : P.natDegree = p.natDegree :=
  (natDegree_map_eq_of_injective (f := Int.castRingHom F) Int.cast_injective P).symm.trans
    (by rw [hpδ, natDegree_C_mul hδ])

theorem integral_point_of_scalar (P Q : ℤ[X]) (p q : F[X]) (δ : F)
    (hpδ : P.map (Int.castRingHom F) = C δ * p) (hqδ : Q.map (Int.castRingHom F) = C δ * q)
    (X Y : ℤ) (hpoint : p.eval (X : F) = (Y : F) * q.eval (X : F)) : P.eval X = Y * Q.eval X := by
  apply (Int.cast_injective (α := F))
  change (Int.castRingHom F) (P.eval X) = (Int.castRingHom F) (Y * Q.eval X)
  rw [map_mul, ← eval_map_apply, ← eval_map_apply]
  change (P.map (Int.castRingHom F)).eval (X : F) = (Y : F) * (Q.map (Int.castRingHom F)).eval (X : F)
  rw [hpδ, hqδ]
  simp only [eval_mul, eval_C]
  rw [hpoint]
  ring

theorem point_iff_of_scalar (P Q : ℤ[X]) (p q : F[X]) (δ : F) (hδ : δ ≠ 0)
    (hpδ : P.map (Int.castRingHom F) = C δ * p) (hqδ : Q.map (Int.castRingHom F) = C δ * q)
    (X Y : ℤ) : (p.eval (X : F) = (Y : F) * q.eval (X : F)) ↔ P.eval X = Y * Q.eval X := by
  constructor
  · exact integral_point_of_scalar P Q p q δ hpδ hqδ X Y
  · intro hpoint
    have hm : (P.map (Int.castRingHom F)).eval (X : F) =
        (Y : F) * (Q.map (Int.castRingHom F)).eval (X : F) := by
      change (P.map (Int.castRingHom F)).eval ((Int.castRingHom F) X) =
        (Int.castRingHom F) Y * (Q.map (Int.castRingHom F)).eval ((Int.castRingHom F) X)
      rw [eval_map_apply, eval_map_apply, ← map_mul]
      exact congrArg (Int.castRingHom F) hpoint
    rw [hpδ, hqδ] at hm
    simp only [eval_mul, eval_C] at hm
    apply mul_left_cancel₀ hδ
    exact hm.trans (by ring)

theorem exists_rational_descent (a B : ℕ) (hB : 1 ≤ B) (x y : Fin (2 * a + 1) → ℤ)
    (hinj : Function.Injective x) (hx : ∀ j, (x j).natAbs ≤ B) (hy : ∀ j, (y j).natAbs ≤ B)
    (p q : F[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hgrid : ∀ j, p.eval (x j : F) = (y j : F) * q.eval (x j : F)) :
    ∃ p₀ q₀ : ℚ[X], q₀ ≠ 0 ∧ IsCoprime p₀ q₀ ∧ max p₀.natDegree q₀.natDegree = a ∧
      (∀ X Y : ℤ, (p.eval (X : F) = (Y : F) * q.eval (X : F)) ↔
        p₀.eval (X : ℚ) = (Y : ℚ) * q₀.eval (X : ℚ)) ∧
      ∃ δ : F, δ ≠ 0 ∧ p₀.map (Rat.castHom F) = C δ * p ∧ q₀.map (Rat.castHom F) = C δ * q := by
  obtain ⟨P, Q, hQ0, _, _, _, _, hcopQ, hdegreeF, δ, hδ, hpδ, hqδ⟩ :=
    exists_integral_presentation a B hB x y hinj hx hy p q hq0 hcop hdegree hgrid
  have hpF : (P.map (Int.castRingHom F)).natDegree = P.natDegree := natDegree_map_eq_of_injective Int.cast_injective P
  have hqF : (Q.map (Int.castRingHom F)).natDegree = Q.natDegree := natDegree_map_eq_of_injective Int.cast_injective Q
  have hactual : max P.natDegree Q.natDegree = a := by simpa only [hpF, hqF] using hdegreeF
  have hpQ : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree := natDegree_map_eq_of_injective Int.cast_injective P
  have hqQ : (Q.map (Int.castRingHom ℚ)).natDegree = Q.natDegree := natDegree_map_eq_of_injective Int.cast_injective Q
  have hc : (Rat.castHom F).comp (Int.castRingHom ℚ) = Int.castRingHom F := Subsingleton.elim _ _
  have hmP : (P.map (Int.castRingHom ℚ)).map (Rat.castHom F) = P.map (Int.castRingHom F) := by rw [Polynomial.map_map, hc]
  have hmQ : (Q.map (Int.castRingHom ℚ)).map (Rat.castHom F) = Q.map (Int.castRingHom F) := by rw [Polynomial.map_map, hc]
  refine ⟨P.map (Int.castRingHom ℚ), Q.map (Int.castRingHom ℚ),
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hQ0, hcopQ, ?_, ?_, δ, hδ, hmP.trans hpδ, hmQ.trans hqδ⟩
  · simpa only [hpQ, hqQ] using hactual
  · intro X Y
    have hF := point_iff_of_scalar P Q p q δ hδ hpδ hqδ X Y
    have hR := point_iff_of_scalar (F := ℚ) P Q (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ))
      1 one_ne_zero (by rw [C_1, one_mul]) (by rw [C_1, one_mul]) X Y
    exact hF.trans hR.symm

end PaperP1.IntegralInterpolationDescent
