module

public import PaperP1.Model.LocalRunRank
public import PaperP1.Algebra.BinaryRankOne

/-! # Physical even square-product sets and the actual local binary relation code -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalRelationSets

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.WindowRelationCode

def window (x L : ℕ) : Finset ℕ := Ico (x - 1) (x + L)

def Relation (S : Finset ℕ) : Prop := S.Nonempty ∧ Even S.card ∧ ∑ n ∈ S, parityVec n = 0

def physicalSupport (x L : ℕ) (w : Fin (L + 1) → F₂) : Finset ℕ :=
  (selectedVertices L w).image (startCompleteVertexLabel x L)

def word (x L : ℕ) (S : Finset ℕ) : Fin (L + 1) → F₂ :=
  fun i ↦ if startCompleteVertexLabel x L i ∈ S then 1 else 0

theorem relation_iff_square_product (S : Finset ℕ) (hpos : ∀ n ∈ S, 0 < n) :
    Relation S ↔ S.Nonempty ∧ Even S.card ∧ ∃ r : ℕ, S.prod id = r ^ 2 := by
  rw [Relation, sum_parityVec_eq_zero_iff_prod_eq_sq S (fun n : ℕ ↦ n) (fun n hn ↦ (hpos n hn).ne')]
  rfl

theorem image_labels_eq_window {x L : ℕ} (hx : 0 < x) :
    univ.image (startCompleteVertexLabel x L) = window x L := by
  ext n
  simp only [mem_image, mem_univ, true_and, window, mem_Ico]
  exact exists_vertex_iff_in_window hx

theorem support_subset_window {x L : ℕ} (hx : 0 < x) (w : Fin (L + 1) → F₂) :
    physicalSupport x L w ⊆ window x L := by
  rw [← image_labels_eq_window hx]
  exact image_subset_image (subset_univ _)

theorem support_card {x L : ℕ} (hx : 0 < x) (w : Fin (L + 1) → F₂) :
    (physicalSupport x L w).card = (selectedVertices L w).card :=
  card_image_of_injective _ (startCompleteVertexLabel_injective hx)

theorem mem_support_label {x L : ℕ} (hx : 0 < x) (w : Fin (L + 1) → F₂) (i : Fin (L + 1)) :
    startCompleteVertexLabel x L i ∈ physicalSupport x L w ↔ w i ≠ 0 := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := mem_image.mp h
    have heq := startCompleteVertexLabel_injective hx hji
    subst j
    exact (mem_filter.mp hj).2
  · intro hi
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩

theorem word_support {x L : ℕ} (hx : 0 < x) (w : Fin (L + 1) → F₂) :
    word x L (physicalSupport x L w) = w := by
  funext i
  rcases binary_eq_zero_or_one (w i) with h | h <;> simp [word, mem_support_label hx, h]

theorem support_injective {x L : ℕ} (hx : 0 < x) : Function.Injective (physicalSupport x L) := by
  intro w z h
  have hw := congrArg (word x L) h
  simpa only [word_support hx] using hw

theorem support_word {x L : ℕ} (hx : 0 < x) (S : Finset ℕ) (hS : S ⊆ window x L) :
    physicalSupport x L (word x L S) = S := by
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hne := (mem_filter.mp hi).2
    by_contra hnot
    exact hne (by simp [word, hnot])
  · intro hn
    have hw := mem_Ico.mp (hS hn)
    obtain ⟨i, hi⟩ := (exists_vertex_iff_in_window hx).mpr hw
    apply mem_image.mpr
    refine ⟨i, mem_filter.mpr ⟨mem_univ _, ?_⟩, hi⟩
    simp only [word, hi, hn, ite_true, ne_eq, one_ne_zero, not_false_eq_true]

theorem support_parity_sum (x L : ℕ) (w : Fin (L + 1) → F₂)
    (hx : 0 < x) : ∑ n ∈ physicalSupport x L w, parityVec n = vertexParityMap x L w := by
  rw [physicalSupport, sum_image (startCompleteVertexLabel_injective hx).injOn,
    vertexParityMap_eq_selected_sum]

theorem word_mem_code {x L : ℕ} (hx : 0 < x) (S : Finset ℕ) (hS : S ⊆ window x L) (hrel : Relation S) :
    word x L S ∈ windowRelationCode (x - 1) (L + 1) := by
  have hsupp := support_word hx S hS
  have hcard : (selectedVertices L (word x L S)).card = S.card := by
    rw [← support_card hx, hsupp]
  apply (PaperP1.LocalRunRank.mem_start_windowRelationCode hx _).mpr
  refine ⟨?_, ?_⟩
  · change vertexParityMap x L (word x L S) = 0
    rw [← support_parity_sum x L _ hx, hsupp]
    exact hrel.2.2
  · exact (startVertexSum_eq_zero_iff_even_selection L _).mpr (hcard ▸ hrel.2.1)

theorem word_ne_zero {x L : ℕ} (hx : 0 < x) (S : Finset ℕ) (hS : S ⊆ window x L) (hne : S.Nonempty) :
    word x L S ≠ 0 := by
  intro hz
  have hsupp := support_word hx S hS
  rw [hz] at hsupp
  have he : physicalSupport x L (0 : Fin (L + 1) → F₂) = ∅ := by
    simp [physicalSupport, selectedVertices]
  rw [he] at hsupp
  exact hne.ne_empty hsupp.symm

theorem relation_support {x L : ℕ} (hx : 0 < x) (w : windowRelationCode (x - 1) (L + 1))
    (hw : w ≠ 0) : Relation (physicalSupport x L w.val) := by
  have hwcode := (PaperP1.LocalRunRank.mem_start_windowRelationCode hx w.val).mp w.property
  refine ⟨?_, ?_, ?_⟩
  · by_contra hnot
    have he := not_nonempty_iff_eq_empty.mp hnot
    apply hw
    apply Subtype.ext
    have hword := word_support hx w.val
    rw [he] at hword
    funext i
    have hi := congrFun hword i
    change (if startCompleteVertexLabel x L i ∈ (∅ : Finset ℕ) then (1 : F₂) else 0) = w.val i at hi
    simpa using hi.symm
  · rw [support_card hx]
    exact (startVertexSum_eq_zero_iff_even_selection L w.val).mp hwcode.2
  · rw [support_parity_sum x L _ hx]
    exact hwcode.1

theorem unique_relation_in_window {x L : ℕ} (hx : 0 < x)
    (hrank : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (S T : Finset ℕ) (hS : S ⊆ window x L) (hT : T ⊆ window x L) (hrelS : Relation S) (hrelT : Relation T) :
    S = T := by
  let : Fintype (windowRelationCode (x - 1) (L + 1)) := Fintype.ofFinite _
  let w : windowRelationCode (x - 1) (L + 1) := ⟨word x L S, word_mem_code hx S hS hrelS⟩
  let z : windowRelationCode (x - 1) (L + 1) := ⟨word x L T, word_mem_code hx T hT hrelT⟩
  have hw : w ≠ 0 := fun h ↦ word_ne_zero hx S hS hrelS.1 (congrArg Subtype.val h)
  have hz : z ≠ 0 := fun h ↦ word_ne_zero hx T hT hrelT.1 (congrArg Subtype.val h)
  have heq := BinaryRankOne.nonzero_eq hrank w z hw hz
  have hvalues : word x L S = word x L T := congrArg Subtype.val heq
  have hsup := congrArg (physicalSupport x L) hvalues
  simpa only [support_word hx S hS, support_word hx T hT] using hsup

end PaperP1.LocalRelationSets
