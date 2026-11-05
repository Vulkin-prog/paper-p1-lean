module

public import PaperP1.Algebra.PolynomialMultipleEvaluationRank
public import PaperP1.Algebra.FiniteRowKernelGap

/-! # Bounded integer interpolation retaining the full multiple-polynomial gap

The actual rational curve supplies the fractional evaluation rank gap.
The resulting integer equation vanishes on every original population point.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WidePlaneInterpolation

open Polynomial Finset RectangularPolynomialCoordinates PolynomialMultipleEvaluationRank

def entry (D : ℕ) (z : ℤ × ℤ) (i : Index D) : ℤ := z.1 ^ i.1.val * z.2 ^ i.2.val

def heightBound (D B : ℕ) : ℕ := (3 * (2 * D + 1) ^ 2 * (B ^ (4 * D) + 1)) ^ 7

theorem entry_bound (D B : ℕ) (hB : 1 ≤ B) (z : ℤ × ℤ)
    (hx : z.1.natAbs ≤ B) (hy : z.2.natAbs ≤ B) (i : Index D) :
    (entry D z i).natAbs ≤ B ^ (2 * D) := by
  simp only [entry, Int.natAbs_mul, Int.natAbs_pow]
  calc
    _ ≤ B ^ i.1.val * B ^ i.2.val := Nat.mul_le_mul (Nat.pow_le_pow_left hx _) (Nat.pow_le_pow_left hy _)
    _ = B ^ (i.1.val + i.2.val) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by have hx := i.1.isLt; have hy := i.2.isLt; omega)

theorem exists_bounded_equation (D B : ℕ) (hB : 1 ≤ B)
    (F : ℚ[X][X]) (hF : F ≠ 0) (houter : F.natDegree ≤ D)
    (hinner : ∀ y, (F.coeff y).natDegree ≤ D) (S : Finset (ℤ × ℤ))
    (hbox : ∀ z ∈ S, z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B)
    (hzero : ∀ z ∈ S, F.evalEval (z.1 : ℚ) (z.2 : ℚ) = 0) :
    ∃ Q : ℤ[X][X], Q ≠ 0 ∧ Q.natDegree ≤ 2 * D ∧
      (∀ y, (Q.coeff y).natDegree ≤ 2 * D) ∧ PlaneCurvePointCount.degree Q ≤ 4 * D ∧
      BivariateHeight.height Q ≤ heightBound D B ∧ ∀ z ∈ S, Q.evalEval z.1 z.2 = 0 := by
  classical
  let A : S → Index (2 * D) → ℤ := fun z i ↦ entry (2 * D) z.val i
  let H := B ^ (4 * D) + 1
  have hA (z : S) (i : Index (2 * D)) : |A z i| ≤ (H : ℤ) := by
    have hh : (A z i).natAbs ≤ B ^ (4 * D) := by
      simpa only [show 2 * (2 * D) = 4 * D by omega] using
        entry_bound (2 * D) B hB z.val (hbox z.val z.property).1 (hbox z.val z.property).2 i
    have hc : ((A z i).natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast (show (A z i).natAbs ≤ H by dsimp [H]; omega)
    simpa only [Int.natCast_natAbs] using hc
  have hcast : (fun z : S ↦ fun i : Index (2 * D) ↦ (A z i : ℚ)) = evaluationMatrix (2 * D) S := by
    funext z i
    simp only [A, entry, Int.cast_mul, Int.cast_pow, evaluationMatrix]
  have hrank : 8 * Module.finrank ℚ (Submodule.span ℚ
      (Set.range (fun z : S ↦ fun i : Index (2 * D) ↦ (A z i : ℚ)))) ≤
      7 * Fintype.card (Index (2 * D)) := by
    rw [hcast]
    exact fractional_rank_gap D F hF houter hinner S hzero
  have hn : 0 < Fintype.card (Index (2 * D)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    positivity
  obtain ⟨w, hw, hb, hz⟩ := FiniteRowKernelGap.exists_integer_annihilator H (by dsimp [H]; omega) hn A hA hrank
  have hcard : Fintype.card (Index (2 * D)) = (2 * D + 1) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, pow_two]
  have hcoeff (i : Index (2 * D)) : (w i).natAbs ≤ heightBound D B := by
    have hh := hb i
    rw [hcard] at hh
    have hh' : ((w i).natAbs : ℤ) ≤ (heightBound D B : ℤ) := by
      simpa only [Int.natCast_natAbs, heightBound, H] using hh
    exact_mod_cast hh'
  refine ⟨polynomial (2 * D) w, ?_, outer_degree_le _ _, inner_degree_le _ _, ?_,
    height_le (2 * D) (heightBound D B) w hcoeff, ?_⟩
  · intro hh
    apply hw
    funext i
    have hc := congrArg (fun P : ℤ[X][X] ↦ (P.coeff i.2.val).coeff i.1.val) hh
    simpa only [coefficient, Polynomial.coeff_zero, Pi.zero_apply] using hc
  · exact (total_degree_le (2 * D) w).trans_eq (by ring)
  · intro z hzS
    rw [evaluation]
    calc
      _ = ∑ i : Index (2 * D), A ⟨z, hzS⟩ i * w i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [A, entry]
        ring
      _ = 0 := hz ⟨z, hzS⟩

end PaperP1.WidePlaneInterpolation
