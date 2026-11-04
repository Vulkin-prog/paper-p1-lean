module

public import PaperP1.Algebra.BinaryLinearSubstitution
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Order.AbsoluteValue.Int
public import Mathlib.Tactic.GCongr

/-! # Exact primitive integer coordinate changes from an actual inverse matrix pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnimodularBinaryCoordinates

open Finset

theorem reconstruct {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (hBA : B * A = 1) (z : Fin 2 → R) : B.mulVec (A.mulVec z) = z := by
  rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]

theorem coordinate_injective {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (hBA : B * A = 1) : Function.Injective A.mulVec := by
  intro x y hxy
  have h := congrArg B.mulVec hxy
  simpa only [reconstruct A B hBA] using h

theorem coprime_coordinates {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (hBA : B * A = 1) (z : Fin 2 → R) (hz : IsCoprime (z 0) (z 1)) :
    IsCoprime (A.mulVec z 0) (A.mulVec z 1) := by
  obtain ⟨r, s, hbezout⟩ := hz
  refine ⟨r * B 0 0 + s * B 1 0, r * B 0 1 + s * B 1 1, ?_⟩
  calc
    _ = r * (B.mulVec (A.mulVec z)) 0 + s * (B.mulVec (A.mulVec z)) 1 := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    _ = r * z 0 + s * z 1 := by rw [reconstruct A B hBA]
    _ = 1 := hbezout

theorem primitive_iff_isCoprime (z : Fin 2 → ℤ) :
    (z 0).natAbs.Coprime (z 1).natAbs ↔ IsCoprime (z 0) (z 1) := by
  rw [Nat.coprime_iff_gcd_eq_one, Int.isCoprime_iff_gcd_eq_one, Int.gcd_def]

theorem primitive_preserved (A B : Matrix (Fin 2) (Fin 2) ℤ) (hBA : B * A = 1)
    (z : Fin 2 → ℤ) (hz : (z 0).natAbs.Coprime (z 1).natAbs) :
    (A.mulVec z 0).natAbs.Coprime (A.mulVec z 1).natAbs := by
  apply (primitive_iff_isCoprime _).mpr
  exact coprime_coordinates A B hBA z ((primitive_iff_isCoprime z).mp hz)

theorem primitive_equivalence (A B : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hBA : B * A = 1)
    (z : Fin 2 → ℤ) : (A.mulVec z 0).natAbs.Coprime (A.mulVec z 1).natAbs ↔
      (z 0).natAbs.Coprime (z 1).natAbs := by
  constructor
  · intro hz
    have h := primitive_preserved B A hAB (A.mulVec z) hz
    simpa only [reconstruct A B hBA] using h
  · exact primitive_preserved A B hBA z

theorem primitive_nonzero (z : Fin 2 → ℤ) (hz : (z 0).natAbs.Coprime (z 1).natAbs) : z ≠ 0 := by
  intro h
  rw [h] at hz
  simp at hz

theorem finite_population_card (A B : Matrix (Fin 2) (Fin 2) ℤ) (hBA : B * A = 1)
    (S : Finset (Fin 2 → ℤ)) : (S.image A.mulVec).card = S.card :=
  card_image_of_injective S (coordinate_injective A B hBA)

theorem coordinate_height (A : Matrix (Fin 2) (Fin 2) ℤ) (H L : ℕ) (z : Fin 2 → ℤ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hz : ∀ j, |z j| ≤ (L : ℤ)) (i : Fin 2) :
    |A.mulVec z i| ≤ ((2 * H * L : ℕ) : ℤ) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc
    _ ≤ |A i 0 * z 0| + |A i 1 * z 1| := abs_add_le _ _
    _ = |A i 0| * |z 0| + |A i 1| * |z 1| := by rw [abs_mul, abs_mul]
    _ ≤ (H : ℤ) * L + (H : ℤ) * L := by
      gcongr
      · exact hA i 0
      · exact hz 0
      · exact hA i 1
      · exact hz 1
    _ = _ := by push_cast; ring

end PaperP1.UnimodularBinaryCoordinates
