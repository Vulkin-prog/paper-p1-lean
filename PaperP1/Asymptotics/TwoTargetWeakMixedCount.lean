module

public import PaperP1.Asymptotics.TwoTargetSelectedClassData
public import PaperP1.Asymptotics.CoefficientSelectedHostCount

/-! # Actual aligned target pairs with many surviving mixed classes have half-power cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetWeakMixedCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetMixedClassData PaperP1.TwoTargetOrientedClassPattern PaperP1.TwoTargetUnitExclusion PaperP1.CriticalCoefficientPatterns PaperP1.DisjointRecoverySubspace

local instance weakMixedPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem uniform_hosts (s t : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ Ds k : ℕ, 0 < Ds ∧ (UniformSourceSurfaceCover.UniformCover k (t - 1) Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≤ (L + 1) ^ 3 ∧ b ≤ (L + 1) ^ 3 ∧
          EnlargedPairGeometry.Geometric a b p.1 p.2 L ∧ ∃ M : Submodule F₂ (code (starts x p.1 p.2) L),
          NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x p.1 p.2) L)) M (s + 1) t ∧
          ∃ U : Finset (Fin (L + 1) × Fin (L + 1)), (NormalizedUnitCount.units a b p.1 p.2 L \ U).card ≤ 1 ∧
          ∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
            (∀ i, α i ∉ excludedLabels (label (starts x p.1 p.2) M) U) ∧
            ∀ i : Fin k, ∀ j : Fin 2,
              (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j).Nonempty) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, hcount⟩ := CoefficientSelectedHostCount.uniform_hosts C (2 * (t - 1) : ℕ) ε
    (t - 1) (Nat.cast_nonneg _) hε
  obtain ⟨Ne, _hNe, henumerate⟩ := TwoTargetSelectedClassData.uniform_patterns s t k ht D C
    (coefficientMargin (ε / 2) k) hD (margin_pos (by positivity) k)
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hcount hCover hPila
  refine ⟨A, hA, max Ne Nc, ?_⟩
  intro N hN L H hband hHlo hHhi x hx F hdyadic hclasses
  obtain ⟨hcard, hpatterns⟩ := henumerate N (by omega) L H hband hHlo hHhi x hx
  classical
  let castPair : ℕ × ℕ → ℤ × ℤ := fun p ↦ (p.1, p.2)
  have hcast : Function.Injective castPair := by
    intro p q h
    apply Prod.ext
    · have h1 : (p.1 : ℤ) = (q.1 : ℤ) := congrArg Prod.fst h
      exact_mod_cast h1
    · have h2 : (p.2 : ℤ) = (q.2 : ℤ) := congrArg Prod.snd h
      exact_mod_cast h2
  have hbound := hc N (by omega) L hband (boundedCoefficients x L H t N) hcard (by
    intro d hd
    obtain ⟨hdpos, hdhi⟩ := bounded_coefficient x L H t N d hd
    refine ⟨hdpos, ?_⟩
    rw [Real.rpow_natCast]
    exact_mod_cast hdhi) (F.image castPair) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      obtain ⟨hy, hz⟩ := hdyadic q hq
      change (N : ℤ) ≤ (q.1 : ℤ) ∧ (N : ℤ) ≤ (q.2 : ℤ) ∧
        (q.1 : ℤ).natAbs ≤ 2 * N ∧ (q.2 : ℤ).natAbs ≤ 2 * N
      exact ⟨by exact_mod_cast (mem_Ico.mp hy).1, by exact_mod_cast (mem_Ico.mp hz).1,
        by simpa only [castPair, Int.natAbs_natCast] using (mem_Ico.mp hy).2.le,
        by simpa only [castPair, Int.natAbs_natCast] using (mem_Ico.mp hz).2.le⟩) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      obtain ⟨a, b, ha, hb, haH, hbH, hgeom, M, hno, U, hremaining, α, hinj, hα, hsafe, hboth⟩ := hclasses q hq
      obtain ⟨hsize, hdata⟩ := hpatterns q.1 q.2 (hdyadic q hq).1 (hdyadic q hq).2
        a b ha hb haH hbH hgeom M hno U hremaining α hα hsafe
      obtain ⟨hqpool, hadmiss, w, hw⟩ := hdata 1
      refine ⟨pattern _ M α 1, hqpool, valid _ M α 1 hinj hboth hsize, ?_, w, ?_⟩
      · simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, castPair] using hadmiss
      · simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, castPair] using hw)
  simpa only [card_image_of_injective _ hcast] using hbound

end PaperP1.TwoTargetWeakMixedCount
