module

public import PaperP1.Combinatorics.ComponentSelection
public import PaperP1.Combinatorics.LargePrimeComponentArithmetic

/-! # Physical and square-class injectivity of actual nontrivial component selections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentProjectionInjectivity

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ComponentSelection
  PaperP1.LargePrimeOccurrences PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution
  PaperP1.LargePrimeComponentArithmetic PaperP1.PinnedGraphResolution

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

theorem selection_at_component {V : Type*} (G : SimpleGraph V) (Q : Finset G.ConnectedComponent)
    (w : Q → F₂) (c : Q) (v : V) (hv : G.connectedComponentMk v = c.val) : selection G Q w v = w c := by
  classical
  have hmem : G.connectedComponentMk v ∈ Q := by simpa only [hv] using c.property
  change (if h : G.connectedComponentMk v ∈ Q then w ⟨G.connectedComponentMk v, h⟩ else 0) = w c
  rw [dite_eq_left hmem]
  exact congrArg w (Subtype.ext hv)

def firstProjection (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    (Q → F₂) →ₗ[F₂] (Fin (L + 1) → F₂) where
  toFun w i := selection (largePrimeGraph x y L) Q w (Sum.inl i)
  map_add' _ _ := by funext i; simp only [map_add, Pi.add_apply]
  map_smul' _ _ := by funext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

def secondProjection (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    (Q → F₂) →ₗ[F₂] (Fin (L + 1) → F₂) where
  toFun w i := selection (largePrimeGraph x y L) Q w (Sum.inr i)
  map_add' _ _ := by funext i; simp only [map_add, Pi.add_apply]
  map_smul' _ _ := by funext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

def IsFreeFamily (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) : Prop :=
  Q ⊆ nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)

theorem firstProjection_injective (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) : Function.Injective (firstProjection x y L Q) := by
  intro w w' h
  funext c
  obtain ⟨i, _j, hi, _hj⟩ := free_nontrivial_component_meets_both_blocks hx hy c.val (hQ c.property)
  have he := congrFun h i
  change selection (largePrimeGraph x y L) Q w (Sum.inl i) = selection (largePrimeGraph x y L) Q w' (Sum.inl i) at he
  simpa only [selection_at_component _ Q _ c _ hi] using he

theorem secondProjection_injective (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) : Function.Injective (secondProjection x y L Q) := by
  intro w w' h
  funext c
  obtain ⟨_i, j, _hi, hj⟩ := free_nontrivial_component_meets_both_blocks hx hy c.val (hQ c.property)
  have he := congrFun h j
  change selection (largePrimeGraph x y L) Q w (Sum.inr j) = selection (largePrimeGraph x y L) Q w' (Sum.inr j) at he
  simpa only [selection_at_component _ Q _ c _ hj] using he

theorem selection_mem_largePrimeSolution (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) (w : Q → F₂) :
    selection (largePrimeGraph x y L) Q w ∈ largePrimeSolution x y L := by
  rw [largePrimeSolution_eq_pinnedGraphSpace hx hy]
  exact selection_mem_graph _ Q (fun c hc ↦ ((mem_nontrivialUnpinnedComponents _).mp (hQ hc)).1) w

theorem component_first_private_prime (x y L : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent)
    (hc : c ∈ nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)) :
    ∃ p i, IsLargePrime L p ∧ Sum.inl i ∈ primeOccurrences x y L p ∧
      (largePrimeGraph x y L).connectedComponentMk (Sum.inl i) = c := by
  obtain ⟨v, z, hv, hadj⟩ := component_has_edge c ((mem_nontrivialUnpinnedComponents _).mp hc).2
  have hz : (largePrimeGraph x y L).connectedComponentMk z = c :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hv
  obtain ⟨hne, p, hp, hvp, hzp⟩ := largePrimeGraph_adj.mp hadj
  rcases inOppositeBlocks_of_mem_of_ne hx hy hp.1 (largePrime_gt_length hp) hvp hzp hne with
    ⟨i, j, rfl, rfl⟩ | ⟨j, i, rfl, rfl⟩
  · exact ⟨p, i, hp, hvp, hv⟩
  · exact ⟨p, i, hp, hzp, hz⟩

def firstClasses (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    (Q → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  (vertexParityMap x L).comp (firstProjection x y L Q)

theorem firstClasses_coordinate (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (w : Q → F₂) (c : Q) (p : ℕ) (hp : IsLargePrime L p) (i : Fin (L + 1))
    (hi : Sum.inl i ∈ primeOccurrences x y L p)
    (hc : (largePrimeGraph x y L).connectedComponentMk (Sum.inl i) = c.val) :
    firstClasses x y L Q w p = w c := by
  classical
  change (vertexParityMap x L (firstProjection x y L Q w)) p = w c
  rw [vertexParityMap_apply]
  rw [Finset.sum_apply']
  rw [sum_eq_single i]
  · simp only [Finsupp.smul_apply, smul_eq_mul]
    have hpar : parityVec (startCompleteVertexLabel x L i) p = 1 := mem_primeOccurrences.mp hi
    rw [hpar, mul_one]
    exact selection_at_component _ Q w c (Sum.inl i) hc
  · intro j _hj hji
    have hz : parityVec (startCompleteVertexLabel x L j) p = 0 := by
      by_contra hn
      have he := parityVec_ne_zero_unique_in_start hx (largePrime_gt_length hp)
        (parityVec_ne_zero_of_mem hi) hn
      exact hji he.symm
    simp only [Finsupp.smul_apply, hz, smul_zero]
  · exact fun h ↦ (h (mem_univ i)).elim

theorem firstClasses_injective (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hQ : IsFreeFamily x y L Q) : Function.Injective (firstClasses x y L Q) := by
  intro w w' h
  funext c
  obtain ⟨p, i, hp, hi, hc⟩ := component_first_private_prime x y L hx hy c.val (hQ c.property)
  have he := congrArg (fun a : ℕ →₀ F₂ ↦ a p) h
  simpa only [firstClasses_coordinate x y L Q hx _ c p hp i hi hc] using he

end PaperP1.ComponentProjectionInjectivity
