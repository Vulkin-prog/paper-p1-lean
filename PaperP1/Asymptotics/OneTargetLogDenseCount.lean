module

public import PaperP1.Asymptotics.OneTargetClassSystem
public import PaperP1.Asymptotics.LogarithmicSourceCoefficientCount
public import PaperP1.Asymptotics.LogarithmicUnivariateCount

/-! # An unconditional dense target count for every logarithmic length and comparable target interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneTargetLogDenseCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassSourceCover PaperP1.TwoTargetCoefficientEnumeration
  PaperP1.TwoTargetClassCoefficients PaperP1.TwoTargetLabelSelection PaperP1.CriticalCoefficientPatterns

local instance oneTargetLogDensePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance intersectionAddCommGroup {y L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup ↥(W ⊓ squareClassSpace y L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ℕ →₀ F₂) (W ⊓ squareClassSpace y L)
local instance codeAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin s ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ P) := Classical.decEq _

theorem uniform_count (s : ℕ) (a b D η ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hη : 0 < η) (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L ≥ L₀,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ x : Fin s → ℕ, (∀ i, 2 ≤ x i) →
        (∀ i : Fin s × Fin (L + 1), FixedSourceCertificate.sourceValues x (L + 1) i ≤ N ^ 2) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ S : Finset ℕ,
        (∀ y ∈ S, 2 ≤ y ∧ a * N ≤ y ∧ (y : ℝ) ≤ b * N ∧
          η * L ≤ (Module.finrank F₂ ↥(W ⊓ squareClassSpace y L) : ℝ)) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨t, ht, hregularize⟩ := OneTargetPhysicalRegularization.uniform_subspace s η hη
  obtain ⟨Nq, _hNq, hq⟩ := LogarithmicSourceCoefficientCount.uniform_count s (sourceBound s t) D D
    (coefficientMargin (ε / 2) 2) hD (margin_pos (by positivity) 2)
  obtain ⟨Nc, _hNc, hc⟩ := LogarithmicUnivariateCount.uniform_count a b D ε (t - 1) ha hD hε
  obtain ⟨J, hJ⟩ := exists_nat_gt (4 / η)
  refine ⟨max 1 J, by omega, max 3 (max Nq Nc), by omega, ?_⟩
  intro N hN L hL hwidth x hx hheight W hW S hS
  have hlarge : (4 : ℝ) ≤ η * L := by
    have hbase := (div_lt_iff₀ hη).mp hJ
    have hJL : (J : ℝ) ≤ L := by exact_mod_cast (show J ≤ L by omega)
    have hmono := mul_le_mul_of_nonneg_left hJL hη.le
    linarith only [hbase, hmono]
  let Q := coefficients x L (L + 1) t
  have hQcard : (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin (ε / 2) 2 :=
    hq N (by omega) L (L + 1) hwidth hwidth _ hheight
  have hQpos : ∀ d ∈ Q, 0 < d := fun _ hd ↦ SourceSupportedCoefficientPool.pool_pos _ _ _ hd
  apply hc N (by omega) L hwidth Q hQcard hQpos S
  intro y hy
  obtain ⟨hy2, hylo, hyhi, hdense⟩ := hS y hy
  obtain ⟨P, hno, hdim, hinj, hzero⟩ := hregularize x y 2 L (by omega) W hW
  have hdimP : 2 ≤ Module.finrank F₂ P := by
    have h : (2 : ℝ) ≤ Module.finrank F₂ P := by linarith only [hlarge, hdense, hdim]
    exact_mod_cast h
  have hlabels : 2 ≤ (targetLabels (starts x y 2) P 0).card :=
    hdimP.trans (OneTargetPhysicalRegularization.dimension_le_labels _ P 0 hinj)
  exact ⟨hylo, hyhi, OneTargetClassSystem.of_two_labels x hx hy2 (by omega) P ht hno hzero hlabels⟩

end PaperP1.OneTargetLogDenseCount
