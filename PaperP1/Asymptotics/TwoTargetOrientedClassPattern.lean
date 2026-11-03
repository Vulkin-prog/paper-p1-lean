module

public import PaperP1.Asymptotics.TwoTargetSingletonClassData
public import PaperP1.Arithmetic.CoefficientPatternGrids
public import PaperP1.Arithmetic.TwoTargetSelectedGrids

/-! # A fixed actual oriented class pattern retains its exact selected grids -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetOrientedClassPattern

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetClassSourceCover PaperP1.SmallPrimeBudget
  PaperP1.CoefficientSplitRadicalPatterns PaperP1.SplitRadicalPointHeight

local instance orientedPatternPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def pattern {s L k : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Fin k → Module.Dual F₂ M) (j : Fin 2) : Pattern k :=
  ((fun i ↦ targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev,
    fun i ↦ targetOffsets (LabelClassPartition.part (label X M) (α i)) j),
    fun i ↦ squarefreeKernel (targetProduct X M (α i)))

theorem total_degree_le {s L k K : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Fin k → Module.Dual F₂ M) (j : Fin 2)
    (hsize : ∀ i, (LabelClassPartition.part (label X M) (α i)).card ≤ K) (i : Fin k) :
    ((pattern X M α j).1.1 i).card + ((pattern X M α j).1.2 i).card ≤ K := by
  have h := (TwoTargetClassOffsets.total_card_le (LabelClassPartition.part (label X M) (α i))).trans (hsize i)
  fin_cases j
  · change (targetOffsets (LabelClassPartition.part (label X M) (α i)) 1).card +
      (targetOffsets (LabelClassPartition.part (label X M) (α i)) 0).card ≤ K
    omega
  · exact h

theorem pattern_mem {s L k K : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Fin k → Module.Dual F₂ M) (j : Fin 2) (Q : Finset ℕ)
    (hsize : ∀ i, (LabelClassPartition.part (label X M) (α i)).card ≤ K)
    (hcoeff : ∀ i, squarefreeKernel (targetProduct X M (α i)) ∈ Q) :
    pattern X M α j ∈ pool k L K Q := by
  apply (mem_pool _ _ _ _ _).mpr
  refine ⟨?_, ?_, hcoeff⟩
  · intro i
    exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (offset_bound _ j.rev),
      (Nat.le_add_right _ _).trans (total_degree_le X M α j hsize i)⟩
  · intro i
    exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (offset_bound _ j),
      (Nat.le_add_left _ _).trans (total_degree_le X M α j hsize i)⟩

theorem valid {s L k K : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Fin k → Module.Dual F₂ M) (j : Fin 2) (hinj : Function.Injective α)
    (hboth : ∀ i : Fin k, ∀ u : Fin 2,
      (targetOffsets (LabelClassPartition.part (label X M) (α i)) u).Nonempty)
    (hsize : ∀ i, (LabelClassPartition.part (label X M) (α i)).card ≤ K) :
    CoefficientNonalignedHostCount.Valid K (pattern X M α j) := by
  have hdisj (u : Fin 2) : Pairwise fun i n : Fin k ↦
      Disjoint (targetOffsets (LabelClassPartition.part (label X M) (α i)) u)
        (targetOffsets (LabelClassPartition.part (label X M) (α n)) u) :=
    fun _ _ hne ↦ class_offsets_disjoint X M (fun h ↦ hne (hinj h)) u
  exact ⟨hdisj j.rev, hdisj j, fun i ↦ hboth i j.rev, fun i ↦ hboth i j,
    total_degree_le X M α j hsize⟩

theorem degree_one_valid {s L k K a : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Fin k → Module.Dual F₂ M) (j : Fin 2) (hinj : Function.Injective α) (ha : 0 < a)
    (hdegrees : ∀ i, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev).card = a ∧
      (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).card = 1)
    (hsize : ∀ i, (LabelClassPartition.part (label X M) (α i)).card ≤ K) :
    CoefficientDegreeOneHostCount.Valid K (pattern X M α j) := by
  have hboth (i : Fin k) (u : Fin 2) :
      (targetOffsets (LabelClassPartition.part (label X M) (α i)) u).Nonempty := by
    have hleft : (targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev).Nonempty :=
      card_pos.mp (by rw [(hdegrees i).1]; exact ha)
    have hright : (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).Nonempty :=
      card_pos.mp (by rw [(hdegrees i).2]; decide)
    fin_cases j <;> fin_cases u <;> assumption
  exact ⟨valid X M α j hinj hboth hsize, a, ha, hdegrees⟩

theorem grids {s L k : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Fin k → Module.Dual F₂ M) (j : Fin 2) :
    CoefficientPatternGrids.left (pattern X M α j) =
      TwoTargetSelectedGrids.gridOffsets (fun i ↦ LabelClassPartition.part (label X M) (α i)) j.rev ∧
    CoefficientPatternGrids.right (pattern X M α j) =
      TwoTargetSelectedGrids.gridOffsets (fun i ↦ LabelClassPartition.part (label X M) (α i)) j := ⟨rfl, rfl⟩

theorem roots {s y z L k : ℕ} (x : Fin s → ℕ) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (M : Submodule F₂ (code (TwoTargetWindowSections.starts x y z) L))
    (α : Fin k → Module.Dual F₂ M) (j : Fin 2)
    (hsquare : ∀ i, IsSquare (((squarefreeKernel (targetProduct (TwoTargetWindowSections.starts x y z) M (α i)) : ℕ) : ℤ) *
      targetProduct (TwoTargetWindowSections.starts x y z) M (α i))) :
    ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient (pattern (TwoTargetWindowSections.starts x y z) M α j) i *
      integerProduct ((pattern (TwoTargetWindowSections.starts x y z) M α j).1.1 i) (if j = 0 then (z : ℤ) else y) *
      integerProduct ((pattern (TwoTargetWindowSections.starts x y z) M α j).1.2 i) (if j = 0 then (y : ℤ) else z) := by
  choose w hw using (fun i ↦ square_roots x hy hz M (α i) (hsquare i))
  refine ⟨w, ?_⟩
  intro i
  fin_cases j
  · change w i ^ 2 = (squarefreeKernel (targetProduct (TwoTargetWindowSections.starts x y z) M (α i)) : ℤ) *
      integerProduct (targetOffsets (LabelClassPartition.part (label _ M) (α i)) 1) (z : ℤ) *
      integerProduct (targetOffsets (LabelClassPartition.part (label _ M) (α i)) 0) (y : ℤ)
    calc
      _ = (squarefreeKernel (targetProduct (TwoTargetWindowSections.starts x y z) M (α i)) : ℤ) *
        integerProduct (targetOffsets (LabelClassPartition.part (label _ M) (α i)) 0) (y : ℤ) *
        integerProduct (targetOffsets (LabelClassPartition.part (label _ M) (α i)) 1) (z : ℤ) := hw i
      _ = _ := by ring
  · exact hw i

end PaperP1.TwoTargetOrientedClassPattern
