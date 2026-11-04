module

public import PaperP1.Diophantine.BiformCoordinateEquation
public import PaperP1.Diophantine.UnimodularBinaryCoordinates

/-! # Actual finite populations in inverse coordinates on both projective pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiformPointCoordinates

open Finset PaperP1.UnimodularBinaryCoordinates
open PaperP1.BiformCoordinateEquation PaperP1.BiformLinearCoordinates

def move {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (p : (Fin 2 → R) × (Fin 2 → R)) : (Fin 2 → R) × (Fin 2 → R) :=
  (A.mulVec p.1, B.mulVec p.2)

theorem move_inverse {R : Type*} [CommRing R] (A A' B B' : Matrix (Fin 2) (Fin 2) R)
    (hA'A : A' * A = 1) (hB'B : B' * B = 1) (p : (Fin 2 → R) × (Fin 2 → R)) :
    move A' B' (move A B p) = p := by
  exact Prod.ext (reconstruct A A' hA'A p.1) (reconstruct B B' hB'B p.2)

theorem move_injective {R : Type*} [CommRing R] (A A' B B' : Matrix (Fin 2) (Fin 2) R)
    (hA'A : A' * A = 1) (hB'B : B' * B = 1) : Function.Injective (move A B) := by
  intro p q hpq
  have h := congrArg (move A' B') hpq
  simpa only [move_inverse A A' B B' hA'A hB'B] using h

theorem population_card (A A' B B' : Matrix (Fin 2) (Fin 2) ℤ)
    (hA'A : A' * A = 1) (hB'B : B' * B = 1) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    (S.image (move A B)).card = S.card := card_image_of_injective S (move_injective A A' B B' hA'A hB'B)

theorem move_primitive (A A' B B' : Matrix (Fin 2) (Fin 2) ℤ)
    (hA'A : A' * A = 1) (hB'B : B' * B = 1) (p : (Fin 2 → ℤ) × (Fin 2 → ℤ))
    (hp : (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs) :
    ((move A B p).1 0).natAbs.Coprime ((move A B p).1 1).natAbs ∧
      ((move A B p).2 0).natAbs.Coprime ((move A B p).2 1).natAbs :=
  ⟨primitive_preserved A A' hA'A p.1 hp.1, primitive_preserved B B' hB'B p.2 hp.2⟩

theorem inverse_equation_zero {a b : ℕ} (A A' B B' : Matrix (Fin 2) (Fin 2) ℤ)
    (hAA' : A * A' = 1) (hBB' : B * B' = 1)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (hF : ∀ i, (F i).IsHomogeneous b)
    (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    MvPolynomial.eval₂ (MvPolynomial.eval (move A' B' p).2) (move A' B' p).1
        (equation (b := b) (transform (b := b) A B F)) = 0 ↔
      BidegreeOneElimination.original F p.1 p.2 = 0 := by
  rw [transformed_equation_evaluation A B F hF]
  change BidegreeOneElimination.original F (A.mulVec (A'.mulVec p.1))
    (B.mulVec (B'.mulVec p.2)) = 0 ↔ _
  rw [reconstruct A' A hAA', reconstruct B' B hBB']

theorem transported_population_zero {a b : ℕ} (A A' B B' : Matrix (Fin 2) (Fin 2) ℤ)
    (hAA' : A * A' = 1) (hBB' : B * B' = 1)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (hF : ∀ i, (F i).IsHomogeneous b)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hS : ∀ p ∈ S, BidegreeOneElimination.original F p.1 p.2 = 0) :
    ∀ q ∈ S.image (move A' B'),
      MvPolynomial.eval₂ (MvPolynomial.eval q.2) q.1
        (equation (b := b) (transform (b := b) A B F)) = 0 := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  exact (inverse_equation_zero A A' B B' hAA' hBB' F hF p).mpr (hS p hp)

theorem move_height (A B : Matrix (Fin 2) (Fin 2) ℤ) (H K L T : ℕ)
    (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) (hA : ∀ i j, |A i j| ≤ (H : ℤ))
    (hB : ∀ i j, |B i j| ≤ (K : ℤ)) (hp : ∀ j, |p.1 j| ≤ (L : ℤ))
    (hq : ∀ j, |p.2 j| ≤ (T : ℤ)) :
    (∀ i, |(move A B p).1 i| ≤ ((2 * H * L : ℕ) : ℤ)) ∧
      ∀ i, |(move A B p).2 i| ≤ ((2 * K * T : ℕ) : ℤ) :=
  ⟨coordinate_height A H L p.1 hA hp, coordinate_height B K T p.2 hB hq⟩

end PaperP1.BiformPointCoordinates
