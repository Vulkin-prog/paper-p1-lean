module

public import PaperP1.Asymptotics.TwoTargetOrientedClassPattern
public import PaperP1.Asymptotics.WeakAlignedSelectedGrids

/-! # Actual surviving label classes give their common coefficients, exact oriented grids and geometric admissibility -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetSelectedClassData

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetClassSourceCover PaperP1.SmallPrimeBudget PaperP1.DisjointRecoverySubspace
  PaperP1.CoefficientSplitRadicalPatterns PaperP1.SplitRadicalPointHeight PaperP1.TwoTargetMixedClassData
  PaperP1.TwoTargetOrientedClassPattern PaperP1.CoefficientPatternGrids PaperP1.TwoTargetUnitExclusion

local instance selectedClassDataPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem uniform_patterns (s t k : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
        ((boundedCoefficients x L H t N).card : ℝ) ≤ (N : ℝ) ^ ε ∧
        ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
        ∀ a b : ℕ, 0 < a → 0 < b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
          EnlargedPairGeometry.Geometric a b y z L →
        ∀ M : Submodule F₂ (code (starts x y z) L),
          NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) M (s + 1) t →
        ∀ U : Finset (Fin (L + 1) × Fin (L + 1)),
          (NormalizedUnitCount.units a b y z L \ U).card ≤ 1 →
        ∀ α : Fin k → Module.Dual F₂ M, (∀ i, α i ≠ 0) →
          (∀ i, α i ∉ excludedLabels (label (starts x y z) M) U) →
          (∀ i, (LabelClassPartition.part (label (starts x y z) M) (α i)).card ≤ t - 1) ∧
          ∀ j : Fin 2,
            pattern (starts x y z) M α j ∈ pool k L (t - 1) (boundedCoefficients x L H t N) ∧
            SourceCurvePointCover.Admissible (left (pattern (starts x y z) M α j))
              (right (pattern (starts x y z) M α j))
              (if j = 0 then ((z : ℤ), (y : ℤ)) else ((y : ℤ), (z : ℤ))) ∧
            ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient (pattern (starts x y z) M α j) i *
              integerProduct ((pattern (starts x y z) M α j).1.1 i) (if j = 0 then (z : ℤ) else y) *
              integerProduct ((pattern (starts x y z) M α j).1.2 i) (if j = 0 then (y : ℤ) else z) := by
  obtain ⟨Ne, _hNe, he⟩ := TwoTargetIntrinsicEnumeration.uniform_enumeration s t ht D C ε hD hε
  obtain ⟨Ng, _hNg, hg⟩ := WeakAlignedSelectedGrids.uniform_admissible C k (t - 1)
  refine ⟨max 3 (max Ne Ng), by omega, ?_⟩
  intro N hN L H hband hHlo hHhi x hx
  obtain ⟨hcard, hclass⟩ := he N (by omega) L H hband hHlo hHhi x hx
  refine ⟨(show ((boundedCoefficients x L H t N).card : ℝ) ≤
    (TwoTargetCoefficientEnumeration.coefficients x L H t).card by exact_mod_cast bounded_card_le x L H t N).trans hcard, ?_⟩
  intro y z hy hz a b ha hb haH hbH hgeom M hno U hremaining α hnonzero hsafe
  have hcoeff (i) := hclass y z hy hz M hno (α i) (hnonzero i)
  have hsize (i) := coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code (starts x y z) L)) M
    (s + 1) t (by omega) hno (α i) (hnonzero i)
  have hadmiss := hg N (by omega) L hband y z hy hz a b ha hb haH hbH hgeom s
    (fun i ↦ LabelClassPartition.part (label (starts x y z) M) (α i)) hsize U hremaining
    (fun i ↦ class_avoids_endpoints (label (starts x y z) M) U (α i) (hsafe i))
  refine ⟨hsize, ?_⟩
  intro j
  refine ⟨pattern_mem _ M α j _ hsize
    (fun i ↦ mem_filter.mpr ⟨(hcoeff i).1, (hcoeff i).2.1, (hcoeff i).2.2.1⟩), ?_, ?_⟩
  · rw [(grids _ M α j).1, (grids _ M α j).2]
    exact hadmiss j
  · exact roots x (by have h := (mem_Ico.mp hy).1; omega)
      (by have h := (mem_Ico.mp hz).1; omega) M α j (fun i ↦ (hcoeff i).2.2.2)

end PaperP1.TwoTargetSelectedClassData
