module

public import PaperP1.Arithmetic.ThreeBlockCoordinates
public import PaperP1.Algebra.TernaryPairwiseRigidity

/-! # Pairwise rigidity is derived from the actual injective local square-class maps -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeBlockRigidity

open PaperP1.Arithmetic PaperP1.ThreeBlockCoordinates PaperP1.ColoredPrimeConstraints

theorem pairwise_rigid (X : Fin 3 → ℕ) (L : ℕ)
    (hinj : ∀ i, Function.Injective (evenSquareClassMap (X i) L))
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L))) :
    PairwiseRigid Prod.fst (data X L) := by
  intro k f hsupport hparity hblocks
  have hk : blockClass X L f k = 0 := blockClass_zero_of_vanishing (fun j ↦ hsupport (k, j) rfl)
  have hzero := TernaryPairwiseRigidity.ternary_missing_zero (fun i ↦ squareClassSpace (X i) L) hpair
    (blockClass X L f) (blockClass_mem hblocks) (sum_blockClass_eq_zero hparity) k hk
  funext v
  exact block_zero_of_class_zero hinj hblocks v.1 (hzero v.1) v.2

end PaperP1.ThreeBlockRigidity
