module

public import PaperP1.Asymptotics.DyadicQuadraticBudgets
public import PaperP1.Asymptotics.SelectedQuadraticError

/-! # Actual finite selected-block/divisor/dyadic cells and their counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedQuadraticCells

open Finset PaperP1.SplitOffsetProducts PaperP1.GroupedPrescribedDivisors
open PaperP1.SelectedQuadraticBudget PaperP1.QuadraticKernelExponents

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Index := Finset ℤ × (ℕ × ℕ)

def codes (P : Finset (Finset ℤ)) (e' N : ℕ) : Finset Index :=
  P ×ˢ (e'.divisors ×ˢ PaperP1.DyadicQuadraticBudgets.indices N)

def threshold (d : ℕ) (β δ η : ℝ) : ℝ := (β - 2 * δ) / ((d : ℝ) / 2) + η
def baseExponent (d : ℕ) (β δ : ℝ) : ℝ := 1 / 2 + β / (2 * d) - δ / d

def cell (S : Finset ℕ) (e' N d : ℕ) (β δ η : ℝ) (i : Index) : Finset ℕ :=
  S.filter fun n ↦ assigned e' n i.1 = i.2.1 ∧ Nat.log2 (kernel i.1 n) = i.2.2 ∧
    weight e' n i.1 / Real.log N ≤ threshold d β δ η

theorem mem_cell (S : Finset ℕ) (e' N d : ℕ) (β δ η : ℝ) (i : Index) (n : ℕ) :
    n ∈ cell S e' N d β δ η i ↔ n ∈ S ∧ assigned e' n i.1 = i.2.1 ∧
      Nat.log2 (kernel i.1 n) = i.2.2 ∧ weight e' n i.1 / Real.log N ≤ threshold d β δ η := by
  simp only [cell, mem_filter]

theorem base_identity (d : ℕ) (β δ : ℝ) :
    baseExponent d β δ = 1 / 2 + ((β - 2 * δ) / ((d : ℝ) / 2)) / 4 := by
  unfold baseExponent
  ring

theorem affine_le_base (d : ℕ) (β δ β₀ β₁ δ₁ η : ℝ) (hβ : β₀ ≤ β₁)
    (hselect : β₁ - 2 * δ₁ ≤ threshold d β δ η) :
    affine β₀ δ₁ ≤ baseExponent d β δ + η / 4 := by
  rw [base_identity]
  unfold affine threshold at *
  linarith

theorem normalized_kernel_le (N q : ℕ) (β : ℝ) (hN : 2 ≤ N) (hq : 0 < q)
    (hupper : (q : ℝ) ≤ (N : ℝ) ^ β) : Real.log q / Real.log N ≤ β := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog := Real.log_le_log (by exact_mod_cast hq : (0 : ℝ) < q) hupper
  rw [Real.log_rpow hn] at hlog
  exact (div_le_iff₀ hl).mpr hlog

theorem cover (S : Finset ℕ) (P : Finset (Finset ℤ)) (e' N d : ℕ) (β δ η : ℝ)
    (he' : 0 < e') (hN : 0 < N)
    (hselected : ∀ n ∈ S, ∃ B ∈ P, weight e' n B / Real.log N ≤ threshold d β δ η)
    (hheight : ∀ n ∈ S, ∀ B ∈ P, kernel B n ≤ N ^ 6) :
    ∀ n ∈ S, ∃ i ∈ codes P e' N, n ∈ cell S e' N d β δ η i := by
  intro n hn
  obtain ⟨B, hB, hweight⟩ := hselected n hn
  let d₀ := assigned e' n B
  let j := Nat.log2 (kernel B n)
  have hd : d₀ ∈ e'.divisors := Nat.mem_divisors.mpr ⟨assigned_divides_divisor e' n B, he'.ne'⟩
  have hj : j ∈ PaperP1.DyadicQuadraticBudgets.indices N :=
    PaperP1.DyadicQuadraticBudgets.mem_indices N (kernel B n) hN (kernel_pos B n) (hheight n hn B hB)
  refine ⟨(B, d₀, j), mem_product.mpr ⟨hB, mem_product.mpr ⟨hd, hj⟩⟩, ?_⟩
  exact (mem_cell S e' N d β δ η _ n).mpr ⟨hn, rfl, rfl, hweight⟩

theorem uniform_cell_count (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e' d : ℕ, ∀ β δ η : ℝ, ∀ S : Finset ℕ, ∀ i : Index,
      (W : ℝ) ≤ D * (Real.log N) ^ A₀ → 0 < e' → i.2.1 ∣ e' → i.1.card = 2 →
      (∀ a ∈ i.1, a.natAbs ≤ W) → (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N) →
      ((cell S e' N d β δ η i).card : ℝ) ≤ (N : ℝ) ^ (baseExponent d β δ + η / 4 + ε) := by
  obtain ⟨Nq, hNq⟩ := PaperP1.ShiftedQuadraticKernelCount.two_factor_count D A₀ ε hε
  refine ⟨max 2 Nq, ?_⟩
  intro N hN W e' d β δ η S i hwidth he' hd hB hA hS
  have hNtwo : 2 ≤ N := by omega
  have hdpos : 0 < i.2.1 := Nat.pos_of_dvd_of_pos hd he'
  let F := cell S e' N d β δ η i
  let βj := PaperP1.DyadicQuadraticBudgets.exponent N i.2.2
  change (F.card : ℝ) ≤ _
  by_cases hne : F.Nonempty
  · have hcount := hNq N (by omega) W i.2.1 i.1 βj hwidth hdpos hB hA F (by
      intro n hn
      obtain ⟨hnS, hassigned, hlog, _⟩ := (mem_cell S e' N d β δ η i n).mp hn
      have hwindow := PaperP1.DyadicQuadraticBudgets.real_window N (kernel i.1 n) i.2.2 hNtwo
        (kernel_pos i.1 n) hlog
      have hdiv := assigned_divides_block e' n i.1
      rw [hassigned] at hdiv
      exact ⟨(hS n hnS).1, (hS n hnS).2, hwindow.1, hwindow.2.1, hdiv⟩)
    obtain ⟨n₀, hn₀⟩ := hne
    obtain ⟨_, hassigned, hlog, hweight⟩ := (mem_cell S e' N d β δ η i n₀).mp hn₀
    have hβ := (PaperP1.DyadicQuadraticBudgets.real_window N (kernel i.1 n₀) i.2.2 hNtwo
      (kernel_pos i.1 n₀) hlog).2.2
    have hselect : Real.log (kernel i.1 n₀) / Real.log N -
        2 * (Real.log i.2.1 / Real.log N) ≤ threshold d β δ η := by
      unfold weight at hweight
      rw [hassigned] at hweight
      calc
        _ = (Real.log (kernel i.1 n₀) - 2 * Real.log i.2.1) / Real.log N := by ring
        _ ≤ _ := hweight
    have haffine := affine_le_base d β δ βj (Real.log (kernel i.1 n₀) / Real.log N)
      (Real.log i.2.1 / Real.log N) η hβ hselect
    apply hcount.trans
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by linarith)
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _

end PaperP1.SelectedQuadraticCells
