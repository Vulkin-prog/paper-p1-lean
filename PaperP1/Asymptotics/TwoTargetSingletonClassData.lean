module

public import PaperP1.Asymptotics.TwoTargetMixedClassData
public import PaperP1.Asymptotics.CoefficientDegreeOneHostCount

/-! # Actual mixed classes with one singleton target construct oriented degree-one systems -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetSingletonClassData

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetClassSourceCover PaperP1.SmallPrimeBudget PaperP1.DisjointRecoverySubspace
  PaperP1.CoefficientSplitRadicalPatterns PaperP1.SplitRadicalPointHeight PaperP1.TwoTargetMixedClassData

local instance singletonClassDataPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem exists_pattern {s y z L t k a : ℕ} (x : Fin s → ℕ) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (M : Submodule F₂ (code (starts x y z) L)) (Q : Finset ℕ) (j : Fin 2) (ha : 0 < a)
    (α : Fin k → Module.Dual F₂ M) (hinj : Function.Injective α)
    (hdegrees : ∀ i, (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j.rev).card = a ∧
      (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j).card = 1)
    (hsize : ∀ i, (LabelClassPartition.part (label (starts x y z) M) (α i)).card ≤ t - 1)
    (hcoeff : ∀ i, squarefreeKernel (targetProduct (starts x y z) M (α i)) ∈ Q)
    (hsquare : ∀ i, IsSquare (((squarefreeKernel (targetProduct (starts x y z) M (α i)) : ℕ) : ℤ) *
      targetProduct (starts x y z) M (α i))) :
    ∃ q ∈ pool k L (t - 1) Q, CoefficientDegreeOneHostCount.Valid (t - 1) q ∧
      ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i *
        integerProduct (q.1.1 i) (if j = 0 then (z : ℤ) else y) *
        integerProduct (q.1.2 i) (if j = 0 then (y : ℤ) else z) := by
  classical
  let D := fun i ↦ LabelClassPartition.part (label (starts x y z) M) (α i)
  let q : Pattern k := ((fun i ↦ targetOffsets (D i) j.rev, fun i ↦ targetOffsets (D i) j),
    fun i ↦ squarefreeKernel (targetProduct (starts x y z) M (α i)))
  have htotal (i) : (targetOffsets (D i) j.rev).card + (targetOffsets (D i) j).card ≤ t - 1 := by
    have h := (total_card_le (D i)).trans (hsize i)
    fin_cases j
    · change (targetOffsets (D i) 1).card + (targetOffsets (D i) 0).card ≤ t - 1
      omega
    · exact h
  have hpool : q ∈ pool k L (t - 1) Q := by
    apply (mem_pool _ _ _ _ _).mpr
    refine ⟨?_, ?_, hcoeff⟩
    · intro i
      exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (offset_bound (D i) j.rev),
        (Nat.le_add_right _ _).trans (htotal i)⟩
    · intro i
      exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (offset_bound (D i) j),
        (Nat.le_add_left _ _).trans (htotal i)⟩
  have hdisj (u : Fin 2) : Pairwise fun i n : Fin k ↦ Disjoint (targetOffsets (D i) u) (targetOffsets (D n) u) :=
    fun _ _ hne ↦ class_offsets_disjoint _ M (fun h ↦ hne (hinj h)) u
  have hneI (i) : (targetOffsets (D i) j.rev).Nonempty := card_pos.mp (by rw [(hdegrees i).1]; exact ha)
  have hneJ (i) : (targetOffsets (D i) j).Nonempty := card_pos.mp (by rw [(hdegrees i).2]; decide)
  refine ⟨q, hpool, ⟨⟨hdisj j.rev, hdisj j, hneI, hneJ, htotal⟩, a, ha, hdegrees⟩, ?_⟩
  choose w hw using (fun i ↦ square_roots x hy hz M (α i) (hsquare i))
  refine ⟨w, ?_⟩
  intro i
  fin_cases j
  · change w i ^ 2 = (squarefreeKernel (targetProduct (starts x y z) M (α i)) : ℤ) *
      integerProduct (targetOffsets (D i) 1) (z : ℤ) * integerProduct (targetOffsets (D i) 0) (y : ℤ)
    calc
      _ = (squarefreeKernel (targetProduct (starts x y z) M (α i)) : ℤ) *
        integerProduct (targetOffsets (D i) 0) (y : ℤ) * integerProduct (targetOffsets (D i) 1) (z : ℤ) := hw i
      _ = _ := by ring
  · exact hw i

theorem uniform_patterns (s t : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
        ((boundedCoefficients x L H t N).card : ℝ) ≤ (N : ℝ) ^ ε ∧
        ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
        ∀ M : Submodule F₂ (code (starts x y z) L),
          NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) M (s + 1) t →
        ∀ k : ℕ, ∀ j : Fin 2, ∀ a : ℕ, 0 < a →
        ∀ α : Fin k → Module.Dual F₂ M, Function.Injective α → (∀ i, α i ≠ 0) →
          (∀ i, (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j.rev).card = a ∧
            (targetOffsets (LabelClassPartition.part (label (starts x y z) M) (α i)) j).card = 1) →
          ∃ q ∈ pool k L (t - 1) (boundedCoefficients x L H t N),
            CoefficientDegreeOneHostCount.Valid (t - 1) q ∧
            ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i *
              integerProduct (q.1.1 i) (if j = 0 then (z : ℤ) else y) *
              integerProduct (q.1.2 i) (if j = 0 then (y : ℤ) else z) := by
  obtain ⟨N₀, hN₀, hu⟩ := TwoTargetIntrinsicEnumeration.uniform_enumeration s t ht D C ε hD hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband hHlo hHhi x hx
  obtain ⟨hcard, hclass⟩ := hu N hN L H hband hHlo hHhi x hx
  refine ⟨(show ((boundedCoefficients x L H t N).card : ℝ) ≤
    (TwoTargetCoefficientEnumeration.coefficients x L H t).card by exact_mod_cast bounded_card_le x L H t N).trans hcard, ?_⟩
  intro y z hy hz M hno k j a ha α hinj hnonzero hdegrees
  have hcoeff (i) := hclass y z hy hz M hno (α i) (hnonzero i)
  have hsize (i) := coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code (starts x y z) L)) M
    (s + 1) t (by omega) hno (α i) (hnonzero i)
  have hypos : 1 ≤ y := by have h := (mem_Ico.mp hy).1; omega
  have hzpos : 1 ≤ z := by have h := (mem_Ico.mp hz).1; omega
  exact exists_pattern x hypos hzpos M _ j ha α hinj hdegrees hsize
    (fun i ↦ mem_filter.mpr ⟨(hcoeff i).1, (hcoeff i).2.1, (hcoeff i).2.2.1⟩)
    (fun i ↦ (hcoeff i).2.2.2)

end PaperP1.TwoTargetSingletonClassData
