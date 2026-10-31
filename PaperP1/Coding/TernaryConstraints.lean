module

public import PaperP1.Coding.TernaryDegree

/-! # Companion T2.3 on actual restricted coordinate constraints -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryConstraints

open Finset PaperP1.Arithmetic PaperP1.CoordinateForms PaperP1.ReducedBinaryRows

local instance ternaryConstraintsPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance ternaryConstraintsDualDecidableEq {U : Type*} [AddCommGroup U] [Module F₂ U]
    (A : Submodule F₂ U) : DecidableEq (Module.Dual F₂ A) := Classical.decEq _

def finalLabels (R : Submodule F₂ (V → F₂)) (D : Finset V) :
    V → Module.Dual F₂ (zeroCoordinates (coordinateFamily R) D) :=
  restrictForm (coordinateFamily R) (zeroCoordinates (coordinateFamily R) D)

def finalRows (R : Submodule F₂ (V → F₂)) (D : Finset V) (rows : Finset (Finset V)) :
    Finset (Finset V) := reduced (finalLabels R D) rows

omit [Fintype V] [DecidableEq V] in
theorem card_le_three_of_color_injective (color : V → Fin 3) (A : Finset V)
    (hcolor : Set.InjOn color (↑A : Set V)) : A.card ≤ 3 := by
  have h := card_le_card_of_injOn color (fun _ _ ↦ mem_univ _) hcolor
  simpa using h

omit [Fintype V] [DecidableEq V] in
theorem restricted_row_sum (R : Submodule F₂ (V → F₂)) (D A : Finset V)
    (hsum : (∑ v ∈ A, coordinateFamily R v) = 0) : (∑ v ∈ A, finalLabels R D v) = 0 := by
  change (∑ v ∈ A, (zeroCoordinates (coordinateFamily R) D).dualRestrict (coordinateFamily R v)) = 0
  rw [← map_sum, hsum, map_zero]

theorem final_rows_checked (R : Submodule F₂ (V → F₂)) (D : Finset V)
    (rows : Finset (Finset V)) (color : V → Fin 3)
    (hcolor : ∀ A ∈ rows, Set.InjOn color (↑A : Set V))
    (hsum : ∀ A ∈ rows, (∑ v ∈ A, coordinateFamily R v) = 0) :
    ∀ A ∈ finalRows R D rows, IsReducedRow (finalLabels R D) A := by
  apply reduced_row
  intro A hA
  exact ⟨card_le_three_of_color_injective color A (hcolor A hA), restricted_row_sum R D A (hsum A hA)⟩

def Conclusion {W : Type*} [AddCommGroup W] [Module F₂ W]
    (L : V → W) (rows : Finset (Finset V)) (K degreeBound : ℕ) : Prop :=
  (∀ A ∈ rows, A.card = 0 ∨ A.card = 2 ∨ A.card = 3) ∧
  (∀ x y : V, x ≠ y → ({x, y} : Finset V) ∈ rows → L x = L y) ∧
  (∀ A ∈ rows, A.card = 3 → Set.InjOn L (↑A : Set V)) ∧
  (∀ x : V, L x ≠ 0 → (componentVertices rows x).card ≤ K ∧
    (ternaryIncident rows x).card ≤ degreeBound)

theorem after_regularisation_sharp (R : Submodule F₂ (V → F₂)) (D : Finset V) (K d : ℕ)
    (hreg : Regular (coordinateFamily R) (zeroCoordinates (coordinateFamily R) D) K d)
    (rows : Finset (Finset V)) (color : V → Fin 3)
    (hcolor : ∀ A ∈ rows, Set.InjOn color (↑A : Set V))
    (hsum : ∀ A ∈ rows, (∑ v ∈ A, coordinateFamily R v) = 0) :
    Conclusion (finalLabels R D) (finalRows R D rows) K (d * K ^ 2) := by
  classical
  let L := finalLabels R D
  let E := finalRows R D rows
  have hrows : ∀ A ∈ E, IsReducedRow L A := final_rows_checked R D rows color hcolor hsum
  have hK : ∀ a ∈ labelSet L, (labelClass L a).card ≤ K := fun a ha ↦ (hreg a ha).1
  have hd : ∀ a ∈ labelSet L, (PairDecompositions.pairs (labelSet L) a).card ≤ d :=
    fun a ha ↦ (hreg a ha).2
  refine ⟨fun A hA ↦ row_card_zero_two_three L A (hrows A hA), ?_,
    fun A hA hcard ↦ ternary_labels_injective L A (hrows A hA) hcard, ?_⟩
  · intro x y hxy hpair
    exact binary_labels_equal L x y hxy (hrows _ hpair).2.2
  · intro x hx
    exact ⟨binary_component_card_le L E (fun A hA ↦ (hrows A hA).2.2) K hK x hx,
      ternary_degree_bound L E hrows K d hK hd x hx⟩

/-- All source conclusions, including its original sufficient factor 2. -/
theorem companion_T2_3 (R : Submodule F₂ (V → F₂)) (D : Finset V) (K d : ℕ)
    (hreg : Regular (coordinateFamily R) (zeroCoordinates (coordinateFamily R) D) K d)
    (rows : Finset (Finset V)) (color : V → Fin 3)
    (hcolor : ∀ A ∈ rows, Set.InjOn color (↑A : Set V))
    (hsum : ∀ A ∈ rows, (∑ v ∈ A, coordinateFamily R v) = 0) :
    Conclusion (finalLabels R D) (finalRows R D rows) K (2 * d * K ^ 2) := by
  obtain ⟨hc, hb, ht, hdegree⟩ := after_regularisation_sharp R D K d hreg rows color hcolor hsum
  refine ⟨hc, hb, ht, ?_⟩
  intro x hx
  obtain ⟨hcomp, hdeg⟩ := hdegree x hx
  refine ⟨hcomp, hdeg.trans ?_⟩
  rw [two_mul, add_mul]
  exact Nat.le_add_right _ _

/-- The regularizing D is constructed here from T2.2, rather than assumed. -/
theorem companion_T2_3_exists (R : Submodule F₂ (V → F₂)) (K d : ℕ)
    (rows : Finset (Finset V)) (color : V → Fin 3)
    (hcolor : ∀ A ∈ rows, Set.InjOn color (↑A : Set V))
    (hsum : ∀ A ∈ rows, (∑ v ∈ A, coordinateFamily R v) = 0) :
    ∃ D : Finset V,
      Module.finrank F₂ R - Module.finrank F₂ (ambientRestriction R D) = D.card ∧
      (D.card : ℝ) ≤ budget (coordinateFamily R) K d ∧
      Conclusion (finalLabels R D) (finalRows R D rows) K (d * K ^ 2) := by
  obtain ⟨D, hdim, hcard, hreg⟩ := coordinate_regularisation (coordinateFamily R)
    (coordinateFamily_separates R) K d
  refine ⟨D, ?_, hcard, after_regularisation_sharp R D K d hreg rows color hcolor hsum⟩
  rw [ambientRestriction_dimension]
  omega

end PaperP1.TernaryConstraints
