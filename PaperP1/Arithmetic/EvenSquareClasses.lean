module

public import PaperP1.Affine.StartBoundaryRange
public import Mathlib.Data.Rat.Lemmas

/-!
# Effective square-class image of even window selections

Prime-exponent parity vectors represent the positive rational square classes
of the window vertices. The effective space is the image of even selections,
so local square relations are factored out before any relative nullity is used.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Affine

namespace PaperP1.Arithmetic

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def vertexParityMap (x L : ℕ) : (Fin (L + 1) → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun v => parityVec (startCompleteVertexLabel x L v))

theorem vertexParityMap_apply (x L : ℕ) (w : Fin (L + 1) → F₂) :
    vertexParityMap x L w = ∑ v, w v • parityVec (startCompleteVertexLabel x L v) := by
  simp [vertexParityMap, Fintype.linearCombination_apply]

def evenSquareClassMap (x L : ℕ) :
    LinearMap.ker (startVertexSum L) →ₗ[F₂] (ℕ →₀ F₂) :=
  (vertexParityMap x L).comp (LinearMap.ker (startVertexSum L)).subtype

def squareClassSpace (x L : ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  LinearMap.range (evenSquareClassMap x L)

instance squareClassSpaceFintype (x L : ℕ) : Fintype (squareClassSpace x L) := by
  classical
  let : Fintype (LinearMap.ker (startVertexSum L)) := Fintype.ofFinite _
  exact Fintype.ofSurjective (evenSquareClassMap x L).rangeRestrict (by
    rintro ⟨c, ⟨w, hw⟩⟩
    exact ⟨w, Subtype.ext hw⟩)

theorem squareClassSpace_eq_range_boundary (x L : ℕ) :
    squareClassSpace x L = LinearMap.range ((vertexParityMap x L).comp (startCompleteBoundary L)) := by
  ext c
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := startBoundaryToEven_surjective L w
    refine ⟨u, ?_⟩
    change vertexParityMap x L (startCompleteBoundary L u) = vertexParityMap x L w.val
    exact congrArg (vertexParityMap x L) (congrArg Subtype.val hu)
  · rintro ⟨u, rfl⟩
    exact ⟨startBoundaryToEven L u, rfl⟩

/-- The parity encoding detects precisely rational square relations. -/
theorem sum_parityVec_zero_iff_rational_square {κ : Type*} (I : Finset κ) (n : κ → ℕ)
    (hn : ∀ i ∈ I, n i ≠ 0) :
    (∑ i ∈ I, parityVec (n i) = 0) ↔ IsSquare (∏ i ∈ I, (n i : ℚ)) := by
  rw [sum_parityVec_eq_zero_iff_prod_eq_sq I n hn,
    ← isSquare_iff_exists_sq, ← Rat.isSquare_natCast_iff, Nat.cast_prod]

theorem binary_eq_zero_or_one (a : F₂) : a = 0 ∨ a = 1 := by
  revert a
  decide

def selectedVertices (L : ℕ) (w : Fin (L + 1) → F₂) : Finset (Fin (L + 1)) :=
  Finset.univ.filter fun v => w v ≠ 0

theorem vertexParityMap_eq_selected_sum (x L : ℕ) (w : Fin (L + 1) → F₂) :
    vertexParityMap x L w =
      ∑ v ∈ selectedVertices L w, parityVec (startCompleteVertexLabel x L v) := by
  rw [vertexParityMap_apply, selectedVertices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  rcases binary_eq_zero_or_one (w v) with hz | ho
  · simp [hz]
  · simp [ho]

theorem startVertexSum_eq_selected_card (L : ℕ) (w : Fin (L + 1) → F₂) :
    startVertexSum L w = ((selectedVertices L w).card : F₂) := by
  calc
    startVertexSum L w = ∑ v ∈ selectedVertices L w, (1 : F₂) := by
      rw [startVertexSum_apply, selectedVertices, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      rcases binary_eq_zero_or_one (w v) with hz | ho
      · simp [hz]
      · simp [ho]
    _ = _ := by simp

theorem startVertexSum_eq_zero_iff_even_selection (L : ℕ) (w : Fin (L + 1) → F₂) :
    startVertexSum L w = 0 ↔ Even (selectedVertices L w).card := by
  rw [startVertexSum_eq_selected_card, ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

theorem startCompleteVertexLabel_eq_offset {x L : ℕ} (hx : 0 < x) (v : Fin (L + 1)) :
    startCompleteVertexLabel x L v = (x - 1) + v.val := by
  unfold startCompleteVertexLabel
  split_ifs <;> omega

theorem startCompleteVertexLabel_injective {x L : ℕ} (hx : 0 < x) :
    Function.Injective (startCompleteVertexLabel x L) := by
  intro v w h
  apply Fin.ext
  rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hx] at h
  exact Nat.add_left_cancel h

theorem exists_vertex_iff_in_window {x L n : ℕ} (hx : 0 < x) :
    (∃ v : Fin (L + 1), startCompleteVertexLabel x L v = n) ↔ x - 1 ≤ n ∧ n < x + L := by
  constructor
  · rintro ⟨v, hv⟩
    rw [startCompleteVertexLabel_eq_offset hx] at hv
    have := v.isLt
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨n - (x - 1), by omega⟩, ?_⟩
    rw [startCompleteVertexLabel_eq_offset hx]
    dsimp
    omega

theorem vertexParityMap_zero_iff_rational_square {x L : ℕ} (hx : 2 ≤ x)
    (w : Fin (L + 1) → F₂) :
    vertexParityMap x L w = 0 ↔
      IsSquare (∏ v ∈ selectedVertices L w, (startCompleteVertexLabel x L v : ℚ)) := by
  rw [vertexParityMap_eq_selected_sum]
  apply sum_parityVec_zero_iff_rational_square
  intro v _
  rw [startCompleteVertexLabel_eq_offset (by omega)]
  omega

end PaperP1.Arithmetic
