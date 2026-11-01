module

public import PaperP1.Diophantine.QuadraticKernelFibres
public import PaperP1.Asymptotics.UniformReal
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The fixed-kernel branch with an actual prescribed divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedQuadraticKernelCount

open Finset PaperP1.QuadraticKernelFibres

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def values (X h Q e : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ Q ≤ kernel h n ∧ kernel h n < 2 * Q ∧ e ∣ kernel h n

theorem mem_values (X h Q e n : ℕ) : n ∈ values X h Q e ↔
    0 < n ∧ n ≤ X ∧ Q ≤ kernel h n ∧ kernel h n < 2 * Q ∧ e ∣ kernel h n := by
  simp only [values, mem_filter, mem_Icc]
  omega

theorem divisible_positive_card (Q e : ℕ) (he : 0 < e) (S : Finset ℕ)
    (hS : ∀ q ∈ S, 0 < q ∧ q < 2 * Q ∧ e ∣ q) : S.card ≤ (2 * Q) / e := by
  have hcard : S.card ≤ (Finset.Icc 1 ((2 * Q) / e)).card := by
    apply card_le_card_of_injOn (fun q ↦ q / e)
    · intro q hq
      obtain ⟨hqpos, hqQ, heq⟩ := hS q hq
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hqpos heq) he,
        Nat.div_le_div_right hqQ.le⟩
    · intro q hq r hr heq
      change q / e = r / e at heq
      have hqrec := Nat.div_mul_cancel (hS q hq).2.2
      have hrrec := Nat.div_mul_cancel (hS r hr).2.2
      rw [heq] at hqrec
      omega
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hcard

theorem first_branch_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ X h Q e : ℕ, 0 < h → 0 < e → X ≤ N ^ K → h ≤ N ^ K →
      ∀ S : Finset ℕ,
        (∀ n ∈ S, 0 < n ∧ n ≤ X ∧ kernel h n < 2 * Q ∧ e ∣ kernel h n) →
          (S.card : ℝ) ≤ (N : ℝ) ^ ε * ((Q : ℝ) / e) := by
  obtain ⟨Nf, hNf⟩ := fixed_kernel_count K (ε / 2) (by positivity)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) 2) (ε / 2) (by positivity)
  refine ⟨max 1 (max Nf Nc), ?_⟩
  intro N hN X h Q e hh he hX hhN S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hc : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have himage : (S.image (kernel h)).card ≤ (2 * Q) / e := by
    apply divisible_positive_card Q e he
    intro q hq
    obtain ⟨n, hnS, rfl⟩ := mem_image.mp hq
    exact ⟨kernel_pos h n, (hS n hnS).2.2⟩
  have hquot : (((2 * Q) / e : ℕ) : ℝ) ≤ 2 * (Q : ℝ) / e := by
    apply (le_div_iff₀ her).mpr
    exact_mod_cast Nat.div_mul_le_self (2 * Q) e
  have himageR : ((S.image (kernel h)).card : ℝ) ≤ 2 * (Q : ℝ) / e :=
    (by exact_mod_cast himage : ((S.image (kernel h)).card : ℝ) ≤ (((2 * Q) / e : ℕ) : ℝ)).trans hquot
  calc
    (S.card : ℝ) = ∑ q ∈ S.image (kernel h), ((S.filter fun n ↦ kernel h n = q).card : ℝ) := by
      have hi := congrArg (fun m : ℕ ↦ (m : ℝ)) (card_eq_sum_card_image (kernel h) S)
      simpa only [Nat.cast_sum] using hi
    _ ≤ ∑ _q ∈ S.image (kernel h), (N : ℝ) ^ (ε / 2) := by
      apply sum_le_sum
      intro q _
      apply hNf N (by omega) X h q hh hX hhN
      intro n hnS
      obtain ⟨hnS, hnq⟩ := mem_filter.mp hnS
      exact ⟨(hS n hnS).1, (hS n hnS).2.1, hnq⟩
    _ = ((S.image (kernel h)).card : ℝ) * (N : ℝ) ^ (ε / 2) := by simp
    _ ≤ (2 * (Q : ℝ) / e) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right himageR (Real.rpow_nonneg hn.le _)
    _ = (2 * (N : ℝ) ^ (ε / 2)) * ((Q : ℝ) / e) := by ring
    _ ≤ ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) * ((Q : ℝ) / e) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn.le _)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem actual_values_first_branch (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ X h Q e : ℕ, 0 < h → 0 < e → X ≤ N ^ K → h ≤ N ^ K →
      ((values X h Q e).card : ℝ) ≤ (N : ℝ) ^ ε * ((Q : ℝ) / e) := by
  obtain ⟨N₀, hN₀⟩ := first_branch_count K ε hε
  refine ⟨N₀, ?_⟩
  intro N hN X h Q e hh he hX hhN
  apply hN₀ N hN X h Q e hh he hX hhN
  intro n hn
  obtain ⟨hnpos, hnX, _, hnQ, hne⟩ := (mem_values X h Q e n).mp hn
  exact ⟨hnpos, hnX, hnQ, hne⟩

end PaperP1.PrescribedQuadraticKernelCount
