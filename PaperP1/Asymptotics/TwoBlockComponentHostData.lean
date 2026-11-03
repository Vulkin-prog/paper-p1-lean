module

public import PaperP1.Arithmetic.TwoBlockComponentPatterns
public import PaperP1.Asymptotics.SmoothDegreeOneHostCount

/-! # Actual unpinned graph components construct the full smooth integer-system witness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoBlockComponentHostData

open Finset PaperP1.Arithmetic PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution
  PaperP1.LargePrimeGraphResolution PaperP1.TwoBlockComponentSquares PaperP1.TwoBlockComponentPatterns
  PaperP1.SplitRadicalPatternPool PaperP1.SplitRadicalPointHeight PaperP1.DefectivePredicate

theorem exists_pattern (k a K x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : Fin k → (largePrimeGraph x y L).ConnectedComponent) (hcinj : Function.Injective c)
    (hfree : ∀ i, ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) (c i))
    (hleft : ∀ i, (leftOffsets x y L (c i)).card = a)
    (hright : ∀ i, (rightOffsets x y L (c i)).card = 1) (hK : a + 1 ≤ K) :
    ∃ q ∈ pool k L (10 * (L + 1)) K, SmoothDegreeOneHostCount.Valid a K q ∧ ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) (x : ℤ) * ((y : ℤ) + q.1.2 i) := by
  classical
  have hexj (i) : ∃ j : ℤ, rightOffsets x y L (c i) = {j} := card_eq_one.mp (hright i)
  choose j hj using hexj
  have hI : Pairwise fun i t ↦ Disjoint (leftOffsets x y L (c i)) (leftOffsets x y L (c t)) :=
    fun _ _ hne ↦ left_disjoint _ _ (fun h ↦ hne (hcinj h))
  have hjinj : Function.Injective j := by
    intro i t heq
    by_contra hne
    have hd := right_disjoint (c i) (c t) (fun h ↦ hne (hcinj h))
    have hi : j i ∈ rightOffsets x y L (c i) := by rw [hj i]; exact mem_singleton_self _
    have ht : j i ∈ rightOffsets x y L (c t) := by rw [hj t, heq]; exact mem_singleton_self _
    exact disjoint_left.mp hd hi ht
  let q : Pattern k := ((fun i ↦ leftOffsets x y L (c i), j),
    fun i ↦ oddPrimeSupport (product x y L (c i)))
  have hpool : q ∈ pool k L (10 * (L + 1)) K := by
    apply (mem_pool k L (10 * (L + 1)) K q).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (TwoBlockComponentPatterns.left_bound (c i)), ?_⟩
      change (leftOffsets x y L (c i)).card ≤ K
      rw [hleft i]
      omega
    · intro i
      have hsub := (BoundedIntegerMotifs.subset_offsets (L + 1) (rightOffsets x y L (c i))).mpr
        (TwoBlockComponentPatterns.right_bound (c i))
      exact hsub (by rw [hj i]; exact mem_singleton_self _)
    · intro i
      exact support hx hy (c i) (hfree i)
  refine ⟨q, hpool, ⟨hI, hjinj, hleft, ?_⟩, ?_⟩
  · intro i
    change (leftOffsets x y L (c i)).card + 1 ≤ K
    rw [hleft i]
    exact hK
  · choose w hw using (fun i ↦ square_roots hx hy (c i) (j i) (hj i))
    exact ⟨w, hw⟩

end PaperP1.TwoBlockComponentHostData
