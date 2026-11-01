module

public import PaperP1.Arithmetic.FiniteEvenSquareClasses
public import PaperP1.Arithmetic.EvenSquareClasses

/-! # Actual complete window sets and their normalized even square-class images -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedWindowSets

open Finset PaperP1.Arithmetic PaperP1.Affine

local instance normalizedWindowPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def values (x L : ℕ) : Finset ℕ := univ.image (startCompleteVertexLabel x L)

def normalized (c x L : ℕ) : Finset ℕ := FiniteEvenSquareClasses.dilate c (values x L)

def union (a b x y L : ℕ) : Finset ℕ := normalized b x L ∪ normalized a y L

theorem mem_values {x L n : ℕ} : n ∈ values x L ↔ ∃ v : Fin (L + 1), startCompleteVertexLabel x L v = n := by
  simp only [values, mem_image, mem_univ, true_and]

theorem values_eq_interval {x L : ℕ} (hx : 0 < x) : values x L = Ico (x - 1) (x + L) := by
  ext n
  rw [mem_values, mem_Ico]
  exact exists_vertex_iff_in_window hx

theorem squareClassSpace_eq_evenImage (x L : ℕ) :
    squareClassSpace x L = EvenImage.image (K := F₂) (fun v : Fin (L + 1) ↦ parityVec (startCompleteVertexLabel x L v)) := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    apply (EvenImage.mem_image_iff _ _).mpr
    refine ⟨w.val, ?_, hw⟩
    have h := w.property
    simpa only [LinearMap.mem_ker, startVertexSum_apply] using h
  · intro hz
    obtain ⟨w, hw, hmap⟩ := (EvenImage.mem_image_iff _ _).mp hz
    refine ⟨⟨w, ?_⟩, hmap⟩
    simpa only [LinearMap.mem_ker, startVertexSum_apply] using hw

theorem space_values (x L : ℕ) : FiniteEvenSquareClasses.space (values x L) = squareClassSpace x L := by
  let v₀ : Fin (L + 1) := startRootVertex L
  have hv₀ : startCompleteVertexLabel x L v₀ ∈ values x L := mem_values.mpr ⟨v₀, rfl⟩
  rw [FiniteEvenSquareClasses.space_eq_span _ _ hv₀, squareClassSpace_eq_evenImage,
    EvenImage.image_eq_span_differences _ v₀]
  congr 1
  ext z
  constructor
  · rintro ⟨n, hn, heq⟩
    obtain ⟨v, rfl⟩ := mem_values.mp hn
    exact ⟨v, heq⟩
  · rintro ⟨v, rfl⟩
    exact ⟨startCompleteVertexLabel x L v, mem_values.mpr ⟨v, rfl⟩, rfl⟩

theorem values_positive {x L : ℕ} (hx : 2 ≤ x) : ∀ n ∈ values x L, 0 < n := by
  intro n hn
  obtain ⟨v, rfl⟩ := mem_values.mp hn
  rw [startCompleteVertexLabel_eq_offset (by omega)]
  omega

theorem card_values {x L : ℕ} (hx : 0 < x) : (values x L).card = L + 1 := by
  rw [values, card_image_of_injective _ (startCompleteVertexLabel_injective hx), card_univ, Fintype.card_fin]

theorem space_normalized {c x L : ℕ} (hc : 0 < c) (hx : 2 ≤ x) :
    FiniteEvenSquareClasses.space (normalized c x L) = squareClassSpace x L := by
  rw [normalized, FiniteEvenSquareClasses.space_dilate _ hc (values_positive hx), space_values]

theorem card_normalized {c x L : ℕ} (hc : 0 < c) (hx : 0 < x) :
    (normalized c x L).card = L + 1 := by
  rw [normalized, FiniteEvenSquareClasses.dilate, card_image_of_injective _ (mul_right_injective₀ hc.ne'), card_values hx]

theorem normalized_nonempty (c x L : ℕ) : (normalized c x L).Nonempty := by
  refine ⟨c * startCompleteVertexLabel x L (startRootVertex L), ?_⟩
  exact mem_image.mpr ⟨_, mem_values.mpr ⟨_, rfl⟩, rfl⟩

theorem space_union {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinter : (normalized b x L ∩ normalized a y L).Nonempty) :
    FiniteEvenSquareClasses.space (union a b x y L) = squareClassSpace x L ⊔ squareClassSpace y L := by
  obtain ⟨n, hn⟩ := hinter
  rw [mem_inter] at hn
  rw [union, FiniteEvenSquareClasses.space_union _ _ n hn.1 hn.2, space_normalized hb hx, space_normalized ha hy]

theorem rank_union {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinter : (normalized b x L ∩ normalized a y L).Nonempty)
    (hprivate : FiniteEvenSquareClasses.Private (union a b x y L)) :
    Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) = (union a b x y L).card - 1 := by
  rw [← space_union ha hb hx hy hinter]
  exact FiniteEvenSquareClasses.finrank_space _ hprivate

end PaperP1.NormalizedWindowSets
