module

public import PaperP1.Asymptotics.TwoTargetIntrinsicEnumeration
public import PaperP1.Arithmetic.TwoTargetPhysicalBudgets

/-! # A single recovery parameter before all source geometry and the actual common coefficient list -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPhysicalEnumeration

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetCoefficientEnumeration
  PaperP1.TwoTargetClassSourceCover PaperP1.DisjointRecoverySubspace PaperP1.SmallPrimeBudget

local instance physicalEnumerationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_enumeration (s : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ D C ε : ℝ, 0 ≤ D → 0 < ε →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ L →
        L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
        ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
          ((coefficients x L H t).card : ℝ) ≤ (N : ℝ) ^ ε ∧
          ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
          ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
          Disjoint W (squareClassSpace y L) → Disjoint W (squareClassSpace z L) →
          ∃ P : Submodule F₂ (code (starts x y z) L),
            NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t ∧
            (Module.finrank F₂ (Kernel y z L W) : ℝ) - ξ * L / 4 ≤ Module.finrank F₂ P ∧
            (∀ j : Fin 2, Function.Injective ((projection (starts x y z) L (Sum.inr j)).comp P.subtype)) ∧
            ∀ α : Module.Dual F₂ P, α ≠ 0 →
              squarefreeKernel (targetProduct (starts x y z) P α) ∈ coefficients x L H t ∧
              0 < squarefreeKernel (targetProduct (starts x y z) P α) ∧
              squarefreeKernel (targetProduct (starts x y z) P α) ≤ N ^ (2 * (t - 1)) ∧
              IsSquare (((squarefreeKernel (targetProduct (starts x y z) P α) : ℕ) : ℤ) *
                targetProduct (starts x y z) P α) := by
  obtain ⟨t, ht, hregularize⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace s ξ hξ
  refine ⟨t, ht, ?_⟩
  intro D C ε hD hε
  obtain ⟨N₀, hN₀, henumerate⟩ := TwoTargetIntrinsicEnumeration.uniform_enumeration s t ht D C ε hD hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband hL hHlo hHhi x hx
  obtain ⟨hpool, hclasses⟩ := henumerate N hN L H hband hHlo hHhi x hx
  refine ⟨hpool, ?_⟩
  intro y z hy hz W hW hWY hWZ
  obtain ⟨P, hno, hdim, hinj⟩ := hregularize x y z L hL W hW hWY hWZ
  exact ⟨P, hno, hdim, hinj, hclasses y z hy hz P hno⟩

end PaperP1.TwoTargetPhysicalEnumeration
