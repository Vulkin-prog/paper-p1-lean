module

public import PaperP1.Arithmetic.TruncatedAnchorWitness
public import PaperP1.Arithmetic.ForwardSubsetSelections

/-! # Literal selected subsets supply truncated anchors and detect new-only defects -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TruncatedSubsetAnchor

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEvenLoss PaperP1.ForwardSubsetSelections
  PaperP1.TruncatedAnchorWitness PaperP1.PrivateWindowPrimes

theorem of_subsets {U V H : ℕ} {A I : Finset ℕ}
    (hA : A ⊆ Ico U (U + H)) (hI : I ⊆ Ico V (V + H))
    (he : (∑ n ∈ A, largeParity H n) = ∑ n ∈ I, largeParity H n)
    (i : Fin H) (hi : U + i.val ∈ A) : AnchoredRelation U V H i := by
  refine ⟨coefficients U H A, coefficients V H I, ?_, ?_⟩
  · simp only [coefficients, hi, ite_true, ne_eq, one_ne_zero, not_false_eq_true]
  · rw [sum_coefficients U H A hA, sum_coefficients V H I hI]
    exact he

theorem defective_of_zero_subset {U H : ℕ} {A : Finset ℕ} (hA : A ⊆ Ico U (U + H))
    (hzero : (∑ n ∈ A, largeParity H n) = 0) {n : ℕ} (hn : n ∈ A) :
    DefectivePredicate.HDefective H n := by
  classical
  obtain ⟨i, he, hci⟩ := index_of_mem U H A hA hn
  have hsum : (∑ j : Fin H, coefficients U H A j • largeParity H (U + j.val)) = 0 :=
    (sum_coefficients U H A hA _).trans hzero
  intro p _hp hHp
  by_contra hparity
  have hpi : parityVec (U + i.val) p ≠ 0 := by rw [he]; exact hparity
  have hfirst : (∑ j : Fin H, coefficients U H A j * parityVec (U + j.val) p) =
      coefficients U H A i * parityVec (U + i.val) p := by
    apply sum_eq_single i
    · intro j _ hji
      rw [parity_other_vertex_zero hHp i j hji.symm hpi, mul_zero]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  have hcoord := congrArg (fun z : ℕ →₀ F₂ ↦ z p) hsum
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    parity_above H _ p hHp, Finsupp.zero_apply] at hcoord
  rw [hfirst] at hcoord
  exact (mul_ne_zero hci hpi) hcoord

end PaperP1.TruncatedSubsetAnchor
