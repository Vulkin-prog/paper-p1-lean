module

public import PaperP1.Model.RetainedGoodEdges
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Companion T12.1 on the actual regular windows and good-edge family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedClassTheorem

open Filter PaperP1.RetainedGoodEdges PaperP1.Model.InfiniteStarts

theorem companion_T12_1 (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        PaperP1.Algebra.Hereditary (Retained H N L) ∧
        (∀ I : Finset ℕ, Retained H N L I → runRelativeNullity L I ≠ 0 →
          ∃ e ∈ PaperP1.GoodEdgeCompression.goodEdges H N L,
            e ⊆ I ∧ runRelativeNullity L I = runRelativeNullity L e ∧
              ∀ q : Finset ℕ, q ⊆ I → q.card = 2 → 0 < runRelativeNullity L q → q = e) ∧
        (∀ I : Finset ℕ, I ⊆ PaperP1.RegularStarts.regularStarts N L →
          PaperP1.Algebra.OrderedBoundary (Retained H N L) I →
            0 < runRelativeNullity L I ∧ (runRelativeNullity L I : ℝ) ≤ 4 * L / 3 + 1 ∧
              (runRelativeNullity L I : ℝ) < 3 * L / 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop ((C + 7) * Real.log 2)))
  refine ⟨max 2 Nl, ?_⟩
  intro N hN L hband H
  have hlower : C + 7 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hlog2).mpr (hNl N (by omega))
  have hLreal : (7 : ℝ) ≤ L := by linarith [(abs_le.mp hband).1]
  have hL : 7 ≤ L := by exact_mod_cast hLreal
  refine ⟨hereditary H N L, ?_, ?_⟩
  · intro I hI hnot
    exact unique_dependent_pair H N L I hI hnot
  · intro I hreg hboundary
    exact finite_boundary_bound (by omega) hL I hreg hboundary

end PaperP1.RetainedClassTheorem
