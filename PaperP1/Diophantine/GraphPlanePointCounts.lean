module

public import PaperP1.Diophantine.GraphPlaneIncidence
public import PaperP1.Arithmetic.P3CoarseCanonicalClassCount

/-! # Exact first-moment identity for the original surface and its actual affine graph-plane sections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphPlanePointCounts

open MvPolynomial Finset P3GraphPlaneSection P3GraphPlaneAffineEvaluation
open scoped Classical

def affineZeros {F : Type} [CommRing F] [Fintype F] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) : Finset (Fin n → F) :=
  univ.filter (fun u ↦ eval (Fin.snoc u 1) P = 0)

theorem mem_affineZeros {F : Type} [CommRing F] [Fintype F] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (u : Fin n → F) :
    u ∈ affineZeros P ↔ eval (Fin.snoc u 1) P = 0 := by
  simp only [affineZeros, mem_filter, mem_univ, true_and]

theorem slice_zeros {F : Type} [CommRing F] [Fintype F]
    (P : MvPolynomial (Fin 4) F) (a : Fin 3 → F) :
    GraphPlaneIncidence.slice (affineZeros P) a = affineZeros (planeSection a P) := by
  ext u
  simp only [GraphPlaneIncidence.slice, affineZeros, mem_filter, mem_univ, true_and, affine_evaluation]

theorem first_moment {F : Type} [CommRing F] [Fintype F] (P : MvPolynomial (Fin 4) F) :
    (∑ a : Fin 3 → F, (affineZeros (planeSection a P)).card) =
      (affineZeros P).card * Fintype.card F ^ 2 := by
  simp only [← slice_zeros]
  exact GraphPlaneIncidence.first_moment (affineZeros P)

theorem canonical_zero (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (c : P3CanonicalSmoothResidues.Class p P) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    P3CoarseCanonicalClassCount.fieldCoordinates c.val ∈
      affineZeros (map (Int.castRingHom (ZMod p)) P) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  apply (mem_affineZeros _ _).mpr
  have he := IntegerPolynomialReduction.map_evaluation (Int.castRingHom (ZMod p))
    (P3CanonicalSmoothResidues.representative c.val) P
  have hc : (fun i ↦ (Int.castRingHom (ZMod p)) (P3CanonicalSmoothResidues.representative c.val i)) =
      Fin.snoc (P3CoarseCanonicalClassCount.fieldCoordinates c.val) 1 := by
    funext i
    cases i using Fin.lastCases with
    | last =>
      change (Int.castRingHom (ZMod p))
        (Fin.snoc (α := fun _ ↦ ℤ) (fun k ↦ ((c.val k).val : ℤ)) 1 (Fin.last 3)) =
        Fin.snoc (α := fun _ ↦ ZMod p) (P3CoarseCanonicalClassCount.fieldCoordinates c.val) 1 (Fin.last 3)
      simp only [Fin.snoc_last, map_one]
    | cast i =>
      simp only [P3CanonicalSmoothResidues.representative, Fin.snoc_castSucc]
      simp [P3CoarseCanonicalClassCount.fieldCoordinates]
  rw [hc] at he
  rw [← he]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr c.property.1

theorem canonical_card_le (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    Fintype.card (P3CanonicalSmoothResidues.Class p P) ≤
      (affineZeros (map (Int.castRingHom (ZMod p)) P)).card := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let S := (univ : Finset (P3CanonicalSmoothResidues.Class p P)).image
    (fun c ↦ P3CoarseCanonicalClassCount.fieldCoordinates c.val)
  have hi : Function.Injective
      (fun c : P3CanonicalSmoothResidues.Class p P ↦ P3CoarseCanonicalClassCount.fieldCoordinates c.val) :=
    (P3CoarseCanonicalClassCount.fieldCoordinates_injective p).comp Subtype.val_injective
  have hcard : S.card = Fintype.card (P3CanonicalSmoothResidues.Class p P) := by
    dsimp only [S]
    rw [card_image_of_injective _ hi, card_univ]
  have hsub : S ⊆ affineZeros (map (Int.castRingHom (ZMod p)) P) := by
    intro u hu
    obtain ⟨c, _, rfl⟩ := mem_image.mp hu
    exact canonical_zero p hp P c
  rw [← hcard]
  exact card_le_card hsub

end PaperP1.GraphPlanePointCounts
