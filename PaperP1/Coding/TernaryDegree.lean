module

public import PaperP1.Coding.ReducedBinaryRows
public import Mathlib.Tactic.Abel

/-! # A ternary incidence count by unordered pairs of nonzero labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedBinaryRows

open Finset PaperP1.Arithmetic PaperP1.CoordinateForms

local instance ternaryDegreePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V W : Type*} [Fintype V] [DecidableEq V] [AddCommGroup W] [Module F₂ W]

local instance ternaryLabelDecidableEq : DecidableEq W := Classical.decEq _

def firstLabel (α : W) (A : Finset W) : W := MatchingCollapse.choosePoint α A

def secondLabel (α : W) (A : Finset W) : W := α - firstLabel α A

def assignedSupports (L : V → W) (x : V) (α : W) (A : Finset W) : Finset (Finset V) :=
  ((labelClass L (firstLabel α A)) ×ˢ (labelClass L (secondLabel α A))).image
    fun p ↦ {x, p.1, p.2}

def ternaryIncident (rows : Finset (Finset V)) (x : V) : Finset (Finset V) :=
  rows.filter fun A ↦ A.card = 3 ∧ x ∈ A

omit [Module F₂ W] in
theorem partner_labels_mem {S A : Finset W} {α : W} (hA : A ∈ PairDecompositions.pairs S α) :
    firstLabel α A ∈ S ∧ secondLabel α A ∈ S := by
  obtain ⟨hAS, hcard, hsum⟩ := PairDecompositions.mem_pairs.mp hA
  have hn : A.Nonempty := card_pos.mp (by omega)
  have hfirst := MatchingCollapse.choosePoint_mem α hn
  obtain ⟨b, _, hAb, hab⟩ := PairDecompositions.pair_partner hcard hsum hfirst
  have hsecond : secondLabel α A = b := by
    unfold secondLabel
    unfold firstLabel
    exact sub_eq_iff_eq_add.mpr (hab.symm.trans (add_comm _ _))
  exact ⟨hAS hfirst, hAS (by rw [hsecond, hAb]; simp)⟩

omit [Module F₂ W] in
theorem assignedSupports_card_le (L : V → W) (K : ℕ)
    (hK : ∀ a ∈ labelSet L, (labelClass L a).card ≤ K)
    (x : V) {α : W} {A : Finset W} (hA : A ∈ PairDecompositions.pairs (labelSet L) α) :
    (assignedSupports L x α A).card ≤ K ^ 2 := by
  obtain ⟨ha, hb⟩ := partner_labels_mem hA
  calc
    _ ≤ ((labelClass L (firstLabel α A)) ×ˢ (labelClass L (secondLabel α A))).card := card_image_le
    _ = (labelClass L (firstLabel α A)).card * (labelClass L (secondLabel α A)).card := card_product _ _
    _ ≤ K * K := Nat.mul_le_mul (hK _ ha) (hK _ hb)
    _ = _ := (pow_two K).symm

theorem ternary_row_covered (L : V → W) (A : Finset V) (hA : IsReducedRow L A)
    (hcard : A.card = 3) (x : V) (hx : x ∈ A) :
    ∃ E ∈ PairDecompositions.pairs (labelSet L) (L x), A ∈ assignedSupports L x (L x) E := by
  obtain ⟨y, z, _, _, _, hshape, hy0, hz0, hlabel, hpair⟩ := ternary_partners L A hA hcard x hx
  let E : Finset W := {L y, L z}
  have hE : E ∈ PairDecompositions.pairs (labelSet L) (L x) := by
    apply PairDecompositions.mem_pairs.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      simp only [E, mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact (mem_labelSet L _).mpr ⟨hy0, y, rfl⟩
      · exact (mem_labelSet L _).mpr ⟨hz0, z, rfl⟩
    · exact card_pair_eq_two_iff.mpr hlabel
    · simpa only [E, sum_pair hlabel] using hpair
  refine ⟨E, hE, ?_⟩
  have hfirst : firstLabel (L x) E ∈ E := MatchingCollapse.choosePoint_mem _ (by simp [E])
  simp only [E, mem_insert, mem_singleton] at hfirst
  rcases hfirst with hfirst | hfirst
  · have hsecond : secondLabel (L x) E = L z := by
      unfold secondLabel
      rw [hfirst, ← hpair]
      abel
    apply mem_image.mpr
    refine ⟨(y, z), mem_product.mpr ⟨?_, ?_⟩, hshape.symm⟩
    · exact (mem_labelClass L _ y).mpr hfirst.symm
    · exact (mem_labelClass L _ z).mpr hsecond.symm
  · have hsecond : secondLabel (L x) E = L y := by
      unfold secondLabel
      rw [hfirst, ← hpair]
      abel
    apply mem_image.mpr
    refine ⟨(z, y), mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (mem_labelClass L _ z).mpr hfirst.symm
    · exact (mem_labelClass L _ y).mpr hsecond.symm
    · change ({x, z, y} : Finset V) = A
      rw [pair_comm z y]
      exact hshape.symm

theorem ternary_degree_bound (L : V → W) (rows : Finset (Finset V))
    (hrows : ∀ A ∈ rows, IsReducedRow L A) (K d : ℕ)
    (hK : ∀ a ∈ labelSet L, (labelClass L a).card ≤ K)
    (hd : ∀ a ∈ labelSet L, (PairDecompositions.pairs (labelSet L) a).card ≤ d)
    (x : V) (hx : L x ≠ 0) : (ternaryIncident rows x).card ≤ d * K ^ 2 := by
  let P := PairDecompositions.pairs (labelSet L) (L x)
  have hcover : ternaryIncident rows x ⊆ P.biUnion (assignedSupports L x (L x)) := by
    intro A hA
    obtain ⟨hArows, hcard, hxA⟩ := mem_filter.mp hA
    obtain ⟨E, hEP, hAE⟩ := ternary_row_covered L A (hrows A hArows) hcard x hxA
    exact mem_biUnion.mpr ⟨E, hEP, hAE⟩
  calc
    _ ≤ (P.biUnion (assignedSupports L x (L x))).card := card_le_card hcover
    _ ≤ ∑ E ∈ P, (assignedSupports L x (L x) E).card := card_biUnion_le
    _ ≤ ∑ _E ∈ P, K ^ 2 := sum_le_sum fun E hE ↦ assignedSupports_card_le L K hK x hE
    _ = P.card * K ^ 2 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (hd _ ((mem_labelSet L _).mpr ⟨hx, x, rfl⟩))

omit [Fintype V] in
theorem ternary_labels_injective (L : V → W) (A : Finset V) (hA : IsReducedRow L A)
    (hcard : A.card = 3) : Set.InjOn L (↑A : Set V) := by
  intro x hx y hy hxy
  obtain ⟨a, b, _, _, _, hshape, ha0, hb0, _, hpair⟩ := ternary_partners L A hA hcard x hx
  have hxa : L x ≠ L a := by
    intro h
    have hz : L a + L b = L a + 0 := by rw [add_zero, hpair]; exact h
    exact hb0 (add_left_cancel hz)
  have hxb : L x ≠ L b := by
    intro h
    have hz : L a + L b = 0 + L b := by rw [zero_add, hpair]; exact h
    exact ha0 (add_right_cancel hz)
  change y ∈ A at hy
  rw [hshape] at hy
  simp only [mem_insert, mem_singleton] at hy
  rcases hy with h | h | h
  · exact h.symm
  · exact False.elim (hxa (h ▸ hxy))
  · exact False.elim (hxb (h ▸ hxy))

end PaperP1.ReducedBinaryRows
