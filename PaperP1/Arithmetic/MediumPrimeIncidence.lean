module

public import PaperP1.Algebra.BinaryIncidenceAugmentation
public import PaperP1.Arithmetic.ShortBasisComponentStage

/-! # Actual retained medium-prime equations have a labelled incidence model -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MediumPrimeIncidence

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.MediumPrimeColumns
  PaperP1.LargePrimeGraph PaperP1.ShortBasisComponentStage PaperP1.BinaryIncidenceAugmentation

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def typedColumn (x y L z : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    Finset (mediumPrimes L z) :=
  univ.filter (fun p ↦ p.val ∈ MediumPrimeColumns.column x y L z c)

theorem mem_typedColumn (x y L z : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent)
    (p : mediumPrimes L z) :
    p ∈ typedColumn x y L z c ↔ p.val ∈ MediumPrimeColumns.column x y L z c := by
  simp only [typedColumn, mem_filter, mem_univ, true_and]

theorem typedColumn_card_le (x y L z : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    (typedColumn x y L z c).card ≤ (MediumPrimeColumns.column x y L z c).card := by
  classical
  apply card_le_card_of_injOn Subtype.val
  · intro p hp
    exact (mem_typedColumn x y L z c p).mp hp
  · intro p _hp q _hq hpq
    exact Subtype.ext hpq

theorem typedColumn_coordinate (x y L z : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent)
    (p : mediumPrimes L z) :
    binaryColumn (typedColumn x y L z c) p =
      ∑ v ∈ componentVertices (largePrimeGraph x y L) c, parityVec (twoStartCompleteVertexLabel x y L v) p.val := by
  have hmem : p.val ∈ MediumPrimeColumns.column x y L z c ↔
      ∑ v ∈ componentVertices (largePrimeGraph x y L) c, parityVec (twoStartCompleteVertexLabel x y L v) p.val ≠ 0 := by
    rw [MediumPrimeColumns.column, DisjointColumnWeights.mem_column]
    exact and_iff_right p.property
  have hbinary : ∀ a : F₂, (if a ≠ 0 then 1 else 0) = a := by decide
  simp only [binaryColumn, mem_typedColumn, hmem]
  exact hbinary _

def actualMap (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    (Q → F₂) →ₗ[F₂] (mediumPrimes L z → F₂) :=
  Fintype.linearCombination F₂ (fun c ↦ fun p ↦
    ∑ v ∈ componentVertices (largePrimeGraph x y L) c.val, parityVec (twoStartCompleteVertexLabel x y L v) p.val)

theorem columnMap_eq_actual (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    columnMap (fun c : Q ↦ typedColumn x y L z c.val) = actualMap x y L z Q := by
  have hc (c : Q) : binaryColumn (typedColumn x y L z c.val) =
      (fun p : mediumPrimes L z ↦ ∑ v ∈ componentVertices (largePrimeGraph x y L) c.val,
        parityVec (twoStartCompleteVertexLabel x y L v) p.val) := by
    funext p
    exact typedColumn_coordinate x y L z c.val p
  simp only [columnMap, hc, actualMap]

theorem retained_incidence_model (x y L z M : ℕ) :
    ∃ a b : retainedComponents x y L z M → Option (mediumPrimes L z),
      incidenceMap a b = augment.comp (actualMap x y L z (retainedComponents x y L z M)) ∧
        LinearMap.ker (incidenceMap a b) = LinearMap.ker (actualMap x y L z (retainedComponents x y L z M)) := by
  classical
  have hcard (c : retainedComponents x y L z M) : (typedColumn x y L z c.val).card ≤ 2 :=
    (typedColumn_card_le x y L z c.val).trans (retained_column_weight x y L z M c.val c.property)
  obtain ⟨a, b, he, hk⟩ := exists_incidence_model
    (fun c : retainedComponents x y L z M ↦ typedColumn x y L z c.val) hcard
  rw [columnMap_eq_actual] at he hk
  exact ⟨a, b, he, hk⟩

theorem selection_weighted_sum {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Q : Finset G.ConnectedComponent) (w : Q → F₂) (a : V → F₂) :
    (∑ v, ComponentSelection.selection G Q w v * a v) =
      ∑ c : Q, w c * ∑ v ∈ componentVertices G c.val, a v := by
  classical
  symm
  calc
    _ = ∑ c : Q, ∑ v, if G.connectedComponentMk v = c.val then w c * a v else 0 := by
      apply sum_congr rfl
      intro c _hc
      rw [mul_sum]
      simp only [componentVertices, sum_filter]
    _ = ∑ v, ∑ c : Q, if G.connectedComponentMk v = c.val then w c * a v else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro v _hv
      by_cases hmem : G.connectedComponentMk v ∈ Q
      · let c₀ : Q := ⟨G.connectedComponentMk v, hmem⟩
        rw [sum_eq_single c₀]
        · rw [ite_eq_left (show G.connectedComponentMk v = c₀.val from rfl),
            ComponentProjectionInjectivity.selection_at_component G Q w c₀ v rfl]
        · intro c _hc hne
          have hn : G.connectedComponentMk v ≠ c.val := by
            intro he
            exact hne (Subtype.ext he.symm)
          exact ite_eq_right hn
        · exact fun h ↦ (h (mem_univ c₀)).elim
      · rw [ComponentSelection.selection_zero_of_outside G w hmem, zero_mul]
        apply sum_eq_zero
        intro c _hc
        have hn : G.connectedComponentMk v ≠ c.val := by
          intro he
          exact hmem (he.symm ▸ c.property)
        exact ite_eq_right hn

theorem actualMap_coordinate (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (w : Q → F₂) (p : mediumPrimes L z) :
    actualMap x y L z Q w p = ∑ v, ComponentSelection.selection (largePrimeGraph x y L) Q w v *
      parityVec (twoStartCompleteVertexLabel x y L v) p.val := by
  simp only [actualMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (selection_weighted_sum (largePrimeGraph x y L) Q w
    (fun v ↦ parityVec (twoStartCompleteVertexLabel x y L v) p.val)).symm

theorem actual_kernel_iff (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (w : Q → F₂) : w ∈ LinearMap.ker (actualMap x y L z Q) ↔
      ∀ p ∈ mediumPrimes L z, (∑ v, ComponentSelection.selection (largePrimeGraph x y L) Q w v *
        parityVec (twoStartCompleteVertexLabel x y L v) p) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h p hp
    have he := congrFun h ⟨p, hp⟩
    simpa only [actualMap_coordinate, Pi.zero_apply] using he
  · intro h
    funext p
    rw [actualMap_coordinate]
    exact h p.val p.property

end PaperP1.MediumPrimeIncidence
