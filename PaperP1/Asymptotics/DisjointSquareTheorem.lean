module

public import PaperP1.Asymptotics.DisjointSquareEquations
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Companion T4.1 with two equations and arbitrary nonzero integer coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointSquareTheorem

open Finset PaperP1.Model

def solutions {j : ℕ} (a b : ℝ) (N : ℕ) (P : Fin j → Finset ℤ) (D : Fin j → ℤ) : Finset ℤ := by
  classical
  exact (Icc ⌈a * N⌉ ⌊b * N⌋).filter fun z ↦ ∀ i, IsSquare (D i * ∏ u ∈ P i, (z + u))

theorem mem_solutions {j : ℕ} (a b : ℝ) (N : ℕ) (P : Fin j → Finset ℤ) (D : Fin j → ℤ) (z : ℤ) :
    z ∈ solutions a b N P D ↔
      a * N ≤ z ∧ (z : ℝ) ≤ b * N ∧ ∀ i, IsSquare (D i * ∏ u ∈ P i, (z + u)) := by
  classical
  simp only [solutions, mem_filter, mem_Icc, Int.ceil_le, Int.le_floor, and_assoc]

/-- One threshold precedes every offset list and every nonzero integer
coefficient. In particular no coefficient-height restriction is needed. -/
theorem two_equation_count (a b K D₀ C ε : ℝ) (ha : 0 < a) (hD₀ : 0 < D₀) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ P : Fin 2 → Finset ℤ, ∀ D : Fin 2 → ℤ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ i, (P i).Nonempty) → (∀ i, ((P i).card : ℝ) ≤ K) → Disjoint (P 0) (P 1) →
      (∀ i, ∀ u ∈ P i, (u.natAbs : ℝ) ≤ D₀ * (L + 1 : ℕ)) → (∀ i, D i ≠ 0) →
      ((solutions a b N P D).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let E := D₀ * CriticalBandScale.upperScale + 2
  obtain ⟨NS, hNS⟩ := DisjointSquareEquations.integer_two_equations a b ha ⌈K⌉₊ E 1 ε hε
  obtain ⟨NG, hNG⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨NL, hNL⟩ := ElementaryLogGrowth.log_ge_eventually 1
  refine ⟨max NS (max NG NL), ?_⟩
  intro N hN L P D hband hnonempty hdegrees hdisjoint hroots hcoeff
  let W := ⌈D₀ * (L + 1 : ℕ)⌉₊ + 1
  have hW : 0 < W := by dsimp [W]; omega
  have hBhi := (hNG N (by omega) L hband).2.2.2.2.2
  have hlog := (hNL N (by omega)).1
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ D₀ * (L + 1 : ℕ) by positivity)).le
  have hwidth : (W : ℝ) ≤ E * (Real.log N) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    have hWcast : (W : ℝ) = (⌈D₀ * (L + 1 : ℕ)⌉₊ : ℝ) + 1 := by simp only [W, Nat.cast_add, Nat.cast_one]
    rw [hWcast]
    dsimp [E]
    nlinarith only [hceil, mul_le_mul_of_nonneg_left hBhi hD₀.le, hlog]
  have hrootNat : ∀ i, ∀ u ∈ P i, u.natAbs ≤ W := by
    intro i u hu
    have hle := (hroots i u hu).trans (Nat.le_ceil (D₀ * (L + 1 : ℕ)))
    have hnat : u.natAbs ≤ ⌈D₀ * (L + 1 : ℕ)⌉₊ := by exact_mod_cast hle
    dsimp [W]
    omega
  have hdegreeNat : ∀ i, (P i).card ≤ ⌈K⌉₊ := by
    intro i
    exact_mod_cast (hdegrees i).trans (Nat.le_ceil K)
  have hrootUnion : ∀ u ∈ P 0 ∪ P 1, u.natAbs ≤ W := by
    intro u hu
    rcases mem_union.mp hu with hu | hu
    · exact hrootNat 0 u hu
    · exact hrootNat 1 u hu
  apply hNS N (by omega) W (P 0) (P 1) (D 0) (D 1) hW (hnonempty 0) (hnonempty 1)
    hdisjoint (hdegreeNat 0) (hdegreeNat 1) hwidth hrootUnion (hcoeff 0) (hcoeff 1) (solutions a b N P D)
  intro z hz
  obtain ⟨hzlo, hzhi, hsq⟩ := (mem_solutions a b N P D z).mp hz
  exact ⟨hzlo, hzhi, hsq 0, hsq 1⟩

/-- Complete source T4.1 on arbitrary fixed comparable positive intervals.
The number of equations can always be two; the source polynomial-height
condition on the coefficients is unnecessary. -/
theorem companion_T4_1 (a b K D₀ C ε : ℝ) (ha : 0 < a) (hD₀ : 0 < D₀) (hε : 0 < ε) :
    ∃ j : ℕ, j = 2 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      ∀ P : Fin j → Finset ℤ, ∀ D : Fin j → ℤ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (∀ i, (P i).Nonempty) → (∀ i, ((P i).card : ℝ) ≤ K) →
        (∀ i k, i ≠ k → Disjoint (P i) (P k)) →
        (∀ i, ∀ u ∈ P i, (u.natAbs : ℝ) ≤ D₀ * (L + 1 : ℕ)) → (∀ i, D i ≠ 0) →
        ((solutions a b N P D).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := two_equation_count a b K D₀ C ε ha hD₀ hε
  refine ⟨2, rfl, N₀, ?_⟩
  intro N hN L P D hband hnonempty hdegrees hdisjoint hroots hcoeff
  exact hN₀ N hN L P D hband hnonempty hdegrees (hdisjoint 0 1 (by decide)) hroots hcoeff

end PaperP1.DisjointSquareTheorem
