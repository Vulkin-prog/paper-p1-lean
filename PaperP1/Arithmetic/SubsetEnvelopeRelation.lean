module

public import PaperP1.Arithmetic.SubsetEnvelopeGraph
public import PaperP1.Arithmetic.AsymmetricEnvelopeRelation

/-! # Actual finite new selections lift to the graph with all ghost coordinates zero -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetEnvelopeRelation

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEvenLoss
  PaperP1.AsymmetricEnvelopeGraph PaperP1.SubsetEnvelopeGraph PaperP1.LargePrimeGraph
  PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution PaperP1.LargePrimeOccurrences

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def newWord (y H R : ℕ) (V : Finset ℕ) (hV : V ⊆ Ico (y - R) (y - R + (H + 1)))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ V)) : Fin (H + 1) → F₂ :=
  FinitePiExtension.extend (SubsetEnvelopeGraph.index y H R V hV) w.val

def word (x y H R : ℕ) (A V : Finset ℕ) (hV : V ⊆ Ico (y - R) (y - R + (H + 1)))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ V)) : Occurrence H → F₂ :=
  Sum.elim (AsymmetricEnvelopeRelation.oldWord x H R A) (newWord y H R V hV w)

theorem new_combination {y H R : ℕ} (hy : R < y) (V : Finset ℕ)
    (hV : V ⊆ Ico (y - R) (y - R + (H + 1)))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ V)) :
    EvenImage.combination (fun i : Fin (H + 1) ↦ largeParity H (startCompleteVertexLabel (start y R) H i))
      (newWord y H R V hV w) = EvenImage.evenMap (SubsetEvenLoss.data H V) w := by
  apply FinitePiExtension.combination_extend (SubsetEnvelopeGraph.index y H R V hV) (SubsetEvenLoss.data H V)
  intro n
  rw [index_label hy V hV]
  rfl

theorem word_mem_largePrimeSolution {x y H R : ℕ} (hx : R < x) (hy : R < y) (A V : Finset ℕ)
    (hA : A ⊆ Ico (x - R) (x - R + (H + 1))) (hV : V ⊆ Ico (y - R) (y - R + (H + 1)))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ V))
    (he : (∑ n ∈ A, largeParity H n) = EvenImage.evenMap (SubsetEvenLoss.data H V) w) :
    word x y H R A V hV w ∈ largePrimeSolution (start x R) (start y R) H := by
  apply mem_largePrimeSolution_iff_boundary_prime_equations.mpr
  intro p hp
  have hHp : H < p := by have hh := hp.2; omega
  have hs := (AsymmetricEnvelopeRelation.old_combination hx A hA).trans
    (he.trans (new_combination hy V hV w).symm)
  have hc := congrArg (fun a : ℕ →₀ F₂ ↦ a p) hs
  simp only [EvenImage.combination_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    TruncatedAnchorWitness.parity_above H _ p hHp] at hc
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin (H + 1), AsymmetricEnvelopeRelation.oldWord x H R A i *
      parityVec (startCompleteVertexLabel (start x R) H i) p) +
    (∑ j : Fin (H + 1), newWord y H R V hV w j * parityVec (startCompleteVertexLabel (start y R) H j) p) = 0
  rw [hc]
  have hdouble : ∀ a : F₂, a + a = 0 := by decide
  exact hdouble _

theorem word_mem_space {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V A : Finset ℕ)
    (hAU : A ⊆ U) (hA : A ⊆ Ico (x - R) (x - R + (H + 1)))
    (hV : V ⊆ Ico (y - R) (y - R + (H + 1)))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ V))
    (he : (∑ n ∈ A, largeParity H n) = EvenImage.evenMap (SubsetEvenLoss.data H V) w) :
    word x y H R A V hV w ∈ SubsetEnvelopeGraph.space x y H R U V := by
  classical
  have horig : word x y H R A V hV w ∈
      PinnedGraphSpace (largePrimeGraph (start x R) (start y R) H)
        (pinnedVertices (start x R) (start y R) H) := by
    rw [← largePrimeSolution_eq_pinnedGraphSpace (by have hh := start_ge_two hx; omega)
      (by have hh := start_ge_two hy; omega)]
    exact word_mem_largePrimeSolution hx hy A V hA hV w he
  refine ⟨horig.1, ?_⟩
  intro v hv
  rcases mem_union.mp hv with hv | hv
  · rcases mem_union.mp hv with hv | hv
    · exact horig.2 v hv
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      have hn : startCompleteVertexLabel (start x R) H i ∉ A :=
        fun hh ↦ (mem_filter.mp hi).2 (hAU hh)
      rw [label_eq hx] at hn
      change ForwardSubsetSelections.coefficients (x - R) (H + 1) A i = 0
      simp only [ForwardSubsetSelections.coefficients, hn, ite_false]
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    apply FinitePiExtensionSupport.extend_zero_outside
    intro n heq
    have hlabel := congrArg (startCompleteVertexLabel (start y R) H) heq
    rw [index_label hy V hV] at hlabel
    exact (mem_filter.mp hj).2 (hlabel ▸ n.property)

theorem represent {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ)
    (hU : U ⊆ Ico (x - R) (x - R + (H + 1)))
    (hV : V ⊆ Ico (y - R) (y - R + (H + 1)))
    (w : (oldSpace H U).comap (EvenImage.evenMap (SubsetEvenLoss.data H V))) :
    ∃ u : SubsetEnvelopeGraph.space x y H R U V,
      ∀ j : Fin (H + 1), u.val (Sum.inr j) = newWord y H R V hV w.val j := by
  obtain ⟨A, hAU, he⟩ := BinarySpanSelections.exists_subset_sum (largeParity H) U
    (EvenImage.evenMap (SubsetEvenLoss.data H V) w.val) w.property
  exact ⟨⟨word x y H R A V hV w.val,
    word_mem_space hx hy U V A hAU (hAU.trans hU) hV w.val he⟩, fun _ ↦ rfl⟩

end PaperP1.SubsetEnvelopeRelation
