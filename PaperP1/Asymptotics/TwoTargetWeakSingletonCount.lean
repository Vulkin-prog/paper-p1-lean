module

public import PaperP1.Asymptotics.TwoTargetSelectedClassData
public import PaperP1.Asymptotics.CoefficientSelectedDegreeOneHostCount

/-! # Many surviving mixed singleton classes in either fixed orientation have subpower many aligned target pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetWeakSingletonCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetMixedClassData PaperP1.TwoTargetOrientedClassPattern PaperP1.TwoTargetUnitExclusion PaperP1.CriticalCoefficientPatterns PaperP1.DisjointRecoverySubspace

local instance weakSingletonPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem uniform_hosts (s t : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k (t - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) → ∀ j : Fin 2,
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≤ (L + 1) ^ 3 ∧ b ≤ (L + 1) ^ 3 ∧
          EnlargedPairGeometry.Geometric a b p.1 p.2 L ∧ ∃ M : Submodule F₂ (code (starts x p.1 p.2) L),
          NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x p.1 p.2) L)) M (s + 1) t ∧
          ∃ U : Finset (Fin (L + 1) × Fin (L + 1)), (NormalizedUnitCount.units a b p.1 p.2 L \ U).card ≤ 1 ∧
          ∃ c : ℕ, 0 < c ∧ ∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
            (∀ i, α i ∉ excludedLabels (label (starts x p.1 p.2) M) U) ∧
            ∀ i, (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j.rev).card = c ∧
              (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j).card = 1) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε) := by
  obtain ⟨k, hk, hcount⟩ := CoefficientSelectedDegreeOneHostCount.uniform_hosts C (2 * (t - 1) : ℕ) ε
    (t - 1) (Nat.cast_nonneg _) hε
  obtain ⟨Ne, _hNe, henumerate⟩ := TwoTargetSelectedClassData.uniform_patterns s t k ht D C
    (coefficientMargin (ε / 2) k) hD (margin_pos (by positivity) k)
  refine ⟨k, hk, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hcount hCover hPila
  refine ⟨A, hA, max Ne Nc, ?_⟩
  intro N hN L H hband hHlo hHhi x hx j F hdyadic hclasses
  obtain ⟨hcard, hpatterns⟩ := henumerate N (by omega) L H hband hHlo hHhi x hx
  classical
  let castPair : ℕ × ℕ → ℤ × ℤ := fun p ↦
    if j = 0 then (p.2, p.1) else (p.1, p.2)
  have hcast : Function.Injective castPair := by
    intro p q h
    by_cases hj : j = 0
    · have h1 : (p.2 : ℤ) = (q.2 : ℤ) := by simpa only [castPair, hj, ite_true] using congrArg Prod.fst h
      have h2 : (p.1 : ℤ) = (q.1 : ℤ) := by simpa only [castPair, hj, ite_true] using congrArg Prod.snd h
      exact Prod.ext (by exact_mod_cast h2) (by exact_mod_cast h1)
    · have h1 : (p.1 : ℤ) = (q.1 : ℤ) := by simpa only [castPair, hj, ite_false] using congrArg Prod.fst h
      have h2 : (p.2 : ℤ) = (q.2 : ℤ) := by simpa only [castPair, hj, ite_false] using congrArg Prod.snd h
      exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hbound := hc N (by omega) L hband (boundedCoefficients x L H t N) hcard (by
    intro d hd
    obtain ⟨hdpos, hdhi⟩ := bounded_coefficient x L H t N d hd
    refine ⟨hdpos, ?_⟩
    rw [Real.rpow_natCast]
    exact_mod_cast hdhi) (F.image castPair) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      obtain ⟨hy, hz⟩ := hdyadic q hq
      have hylo : (N : ℤ) ≤ (q.1 : ℤ) := by exact_mod_cast (mem_Ico.mp hy).1
      have hzlo : (N : ℤ) ≤ (q.2 : ℤ) := by exact_mod_cast (mem_Ico.mp hz).1
      by_cases hj : j = 0
      · simpa only [castPair, hj, ite_true, Int.natAbs_natCast] using
          And.intro hzlo ⟨hylo, (mem_Ico.mp hz).2.le, (mem_Ico.mp hy).2.le⟩
      · simpa only [castPair, hj, ite_false, Int.natAbs_natCast] using
          And.intro hylo ⟨hzlo, (mem_Ico.mp hy).2.le, (mem_Ico.mp hz).2.le⟩) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      obtain ⟨a, b, ha, hb, haH, hbH, hgeom, M, hno, U, hremaining, c, hc, α, hinj, hα, hsafe, hdegrees⟩ := hclasses q hq
      obtain ⟨hsize, hdata⟩ := hpatterns q.1 q.2 (hdyadic q hq).1 (hdyadic q hq).2
        a b ha hb haH hbH hgeom M hno U hremaining α hα hsafe
      obtain ⟨hqpool, hadmiss, w, hw⟩ := hdata j
      refine ⟨pattern _ M α j, hqpool, degree_one_valid _ M α j hinj hc hdegrees hsize, ?_, w, ?_⟩
      · by_cases hj : j = 0 <;> simpa only [castPair, hj, ite_true, ite_false] using hadmiss
      · by_cases hj : j = 0 <;> simpa only [castPair, hj, ite_true, ite_false] using hw)
  simpa only [card_image_of_injective _ hcast] using hbound

end PaperP1.TwoTargetWeakSingletonCount
