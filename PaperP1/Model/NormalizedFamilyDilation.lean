module

public import PaperP1.Model.EvenNormalizedFamilies
public import PaperP1.Arithmetic.ScaledNormalizedIntersections

/-! # The even-rank compatibility criterion is independent of common normalization factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedFamilyDilation

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.FiniteEvenSquareClasses
  PaperP1.PrivateNormalizedFamilies

theorem union_dilate {r L : ℕ} (d : ℕ) (c X : Fin r → ℕ) :
    valueUnion (fun i ↦ d * c i) X L = dilate d (valueUnion c X L) := by
  unfold valueUnion dilate
  rw [biUnion_image]
  apply biUnion_congr rfl
  intro i _
  exact ScaledNormalizedIntersections.normalized_scale d (c i) (X i) L

theorem union_positive {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) :
    ∀ n ∈ valueUnion c X L, 0 < n := by
  intro n hn
  obtain ⟨i, _, hn⟩ := mem_biUnion.mp hn
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  exact Nat.mul_pos (hc i) (values_positive (hX i) m hm)

theorem even_independent_dilate_iff {r L d : ℕ} (hd : 0 < d) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) :
    EvenIndependentValues.Independent (valueUnion (fun i ↦ d * c i) X L) ↔
      EvenIndependentValues.Independent (valueUnion c X L) := by
  rw [union_dilate]
  exact EvenIndependentValues.dilate_iff hd _ (union_positive c X hc hX)

theorem exclusive_dilate_iff {r L d : ℕ} (hd : 0 < d) (c X : Fin r → ℕ) :
    Exclusive (fun i ↦ d * c i) X L ↔ Exclusive c X L := by
  constructor
  · intro hh i j u heq
    apply hh i j u
    simp only [Nat.mul_assoc, heq]
  · intro hh i j u heq
    apply hh i j u
    apply mul_right_injective₀ hd.ne'
    simpa only [Nat.mul_assoc] using heq

theorem union_card_dilate {r L d : ℕ} (hd : 0 < d) (c X : Fin r → ℕ) :
    (valueUnion (fun i ↦ d * c i) X L).card = (valueUnion c X L).card := by
  rw [union_dilate, dilate, card_image_of_injective _ (mul_right_injective₀ hd.ne')]

theorem even_independent_common_ratio_iff {r L a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (c d X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hd : ∀ i, 0 < d i) (hX : ∀ i, 2 ≤ X i)
    (heq : ∀ i, a * c i = b * d i) :
    EvenIndependentValues.Independent (valueUnion c X L) ↔
      EvenIndependentValues.Independent (valueUnion d X L) := by
  have hh : (fun i ↦ a * c i) = (fun i ↦ b * d i) := funext heq
  rw [← even_independent_dilate_iff ha c X hc hX, hh, even_independent_dilate_iff hb d X hd hX]

theorem exclusive_common_ratio_iff {r L a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (c d X : Fin r → ℕ) (heq : ∀ i, a * c i = b * d i) :
    Exclusive c X L ↔ Exclusive d X L := by
  have hh : (fun i ↦ a * c i) = (fun i ↦ b * d i) := funext heq
  rw [← exclusive_dilate_iff ha c X, hh, exclusive_dilate_iff hb d X]

theorem union_card_common_ratio {r L a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (c d X : Fin r → ℕ) (heq : ∀ i, a * c i = b * d i) :
    (valueUnion c X L).card = (valueUnion d X L).card := by
  have hh : (fun i ↦ a * c i) = (fun i ↦ b * d i) := funext heq
  rw [← union_card_dilate ha c X, hh, union_card_dilate hb d X]

end PaperP1.NormalizedFamilyDilation
