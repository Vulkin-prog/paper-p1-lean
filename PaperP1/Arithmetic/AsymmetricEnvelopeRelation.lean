module

public import PaperP1.Arithmetic.AsymmetricEnvelopeGraph
public import PaperP1.Arithmetic.ForwardSubsetSelections
public import PaperP1.Arithmetic.TruncatedAnchorWitness

/-! # Every actual even-loss selection lifts into the envelope graph with all unused coordinates pinned -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricEnvelopeRelation

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEvenLoss
  PaperP1.AsymmetricEnvelopeGraph PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution
  PaperP1.PinnedGraphResolution PaperP1.LargePrimeOccurrences

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def oldWord (x H R : ℕ) (A : Finset ℕ) : Fin (H + 1) → F₂ :=
  ForwardSubsetSelections.coefficients (x - R) (H + 1) A

def newWord (L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H)
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1)))) : Fin (H + 1) → F₂ :=
  FinitePiExtension.extend (targetIndex L H R hnew hamb) w.val

def word (x L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (A : Finset ℕ)
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1)))) : Occurrence H → F₂ :=
  Sum.elim (oldWord x H R A) (newWord L H R hnew hamb w)

theorem old_combination {x H R : ℕ} (hx : R < x) (A : Finset ℕ)
    (hA : A ⊆ Ico (x - R) (x - R + (H + 1))) :
    EvenImage.combination (fun i : Fin (H + 1) ↦ largeParity H (startCompleteVertexLabel (start x R) H i))
      (oldWord x H R A) = ∑ n ∈ A, largeParity H n := by
  rw [EvenImage.combination_apply]
  simp_rw [label_eq hx]
  exact ForwardSubsetSelections.sum_coefficients (x - R) (H + 1) A hA _

theorem new_combination {y L H R : ℕ} (hy : R < y) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H)
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1)))) :
    EvenImage.combination (fun i : Fin (H + 1) ↦ largeParity H (startCompleteVertexLabel (start y R) H i))
      (newWord L H R hnew hamb w) = EvenImage.evenMap (newData H y L) w := by
  apply FinitePiExtension.combination_extend (targetIndex L H R hnew hamb) (newData H y L)
  intro i
  rw [target_label hy hnew hamb]
  rfl

theorem word_mem_largePrimeSolution {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (A : Finset ℕ)
    (hA : A ⊆ Ico (x - R) (x - R + (H + 1)))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1))))
    (he : (∑ n ∈ A, largeParity H n) = EvenImage.evenMap (newData H y L) w) :
    word x L H R hnew hamb A w ∈ largePrimeSolution (start x R) (start y R) H := by
  apply mem_largePrimeSolution_iff_boundary_prime_equations.mpr
  intro p hp
  have hHp : H < p := by have hh := hp.2; omega
  have hs := (old_combination hx A hA).trans (he.trans (new_combination hy hnew hamb w).symm)
  have hc := congrArg (fun a : ℕ →₀ F₂ ↦ a p) hs
  simp only [EvenImage.combination_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    TruncatedAnchorWitness.parity_above H _ p hHp] at hc
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin (H + 1), oldWord x H R A i * parityVec (startCompleteVertexLabel (start x R) H i) p) +
    (∑ j : Fin (H + 1), newWord L H R hnew hamb w j * parityVec (startCompleteVertexLabel (start y R) H j) p) = 0
  rw [hc]
  have hdouble : ∀ a : F₂, a + a = 0 := by decide
  exact hdouble _

theorem word_mem_space {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old A : Finset ℕ) (hAold : A ⊆ old)
    (hA : A ⊆ Ico (x - R) (x - R + (H + 1)))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1))))
    (he : (∑ n ∈ A, largeParity H n) = EvenImage.evenMap (newData H y L) w) :
    word x L H R hnew hamb A w ∈ space x y L H R hnew hamb old := by
  classical
  have horig : word x L H R hnew hamb A w ∈
      PinnedGraphSpace (largePrimeGraph (start x R) (start y R) H)
        (pinnedVertices (start x R) (start y R) H) := by
    rw [← largePrimeSolution_eq_pinnedGraphSpace (by have hh := start_ge_two hx; omega)
      (by have hh := start_ge_two hy; omega)]
    exact word_mem_largePrimeSolution hx hy hnew hamb A hA w he
  refine ⟨horig.1, ?_⟩
  intro v hv
  rcases mem_union.mp hv with hv | hv
  · rcases mem_union.mp hv with hv | hv
    · exact horig.2 v hv
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      have hn : startCompleteVertexLabel (start x R) H i ∉ A :=
        fun hh ↦ (mem_filter.mp hi).2 (hAold hh)
      rw [label_eq hx] at hn
      change ForwardSubsetSelections.coefficients (x - R) (H + 1) A i = 0
      simp only [ForwardSubsetSelections.coefficients, hn, ite_false]
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    exact FinitePiExtensionSupport.extend_zero_outside _ w.val j (mem_filter.mp hj).2

theorem represent {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ))
    (w : Submodule.comap (EvenImage.evenMap (newData H y L)) (oldSpace H old)) :
    ∃ u : space x y L H R hnew hamb old,
      ∀ j : Fin (H + 1), u.val (Sum.inr j) = newWord L H R hnew hamb w.val j := by
  obtain ⟨A, hAold, he⟩ := BinarySpanSelections.exists_subset_sum (largeParity H) old
    (EvenImage.evenMap (newData H y L) w.val) w.property
  have hA : A ⊆ Ico (x - R) (x - R + (H + 1)) :=
    fun _ hn ↦ old_forward hx hamb (hold _ (hAold hn))
  exact ⟨⟨word x L H R hnew hamb A w.val, word_mem_space hx hy hnew hamb old A hAold hA w.val he⟩,
    fun _ ↦ rfl⟩

end PaperP1.AsymmetricEnvelopeRelation
