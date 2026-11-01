module

public import PaperP1.Arithmetic.WindowPoolCount

/-! # Every prime pool contains all positive squares -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquarePoolLower

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate PaperP1.LargeOddKernel
  PaperP1.SmoothSquarefreeCount PaperP1.WindowPoolCount

theorem oddPrimeSupport_square (a : ℕ) : oddPrimeSupport (a ^ 2) = ∅ := by
  ext p
  simp only [mem_oddPrimeSupport_iff_parityVec_ne_zero, parityVec_pow_two, Finsupp.zero_apply,
    ne_eq, not_true_eq_false, notMem_empty]

theorem naturalValues_card_ge_sqrt (P : Finset ℕ) (X : ℕ) : Nat.sqrt X ≤ (naturalValues P X).card := by
  have hinj : Set.InjOn (fun a : ℕ ↦ a ^ 2) (Icc 1 (Nat.sqrt X)) := by
    intro a _ b _ hab
    nlinarith
  have hsub : (Icc 1 (Nat.sqrt X)).image (fun a : ℕ ↦ a ^ 2) ⊆ naturalValues P X := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    obtain ⟨ha, haX⟩ := mem_Icc.mp ha
    apply mem_naturalValues.mpr
    exact ⟨by nlinarith, Nat.le_sqrt'.mp haX, by rw [oddPrimeSupport_square]; exact empty_subset _⟩
  have h := card_le_card hsub
  rw [card_image_of_injOn hinj, Nat.card_Icc] at h
  simpa using h

theorem sqrt_le_twice_nat_sqrt {N : ℕ} (hN : 1 ≤ N) : Real.sqrt N ≤ 2 * (Nat.sqrt N : ℝ) := by
  have hroot : 1 ≤ Nat.sqrt N := Nat.le_sqrt'.mpr (by simpa using hN)
  have hsq := Nat.lt_succ_sqrt' N
  have hsqR : (N : ℝ) < (Nat.sqrt N + 1 : ℝ) ^ 2 := by exact_mod_cast hsq
  have hrootR : (1 : ℝ) ≤ Nat.sqrt N := by exact_mod_cast hroot
  apply (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 2 * (Nat.sqrt N : ℝ))).mpr
  nlinarith

theorem poolValues_card_lower {N B : ℕ} (R : Finset ℕ) (hN : 1 ≤ N) :
    Real.sqrt N / 2 ≤ (poolValues R B (3 * N)).card := by
  have hNat := (Nat.sqrt_le_sqrt (show N ≤ 3 * N by omega)).trans
    (naturalValues_card_ge_sqrt (PaperP1.ConditionalWindowRank.primePool R B) (3 * N))
  have hR : (Nat.sqrt N : ℝ) ≤ (poolValues R B (3 * N)).card := by exact_mod_cast hNat
  have h := sqrt_le_twice_nat_sqrt hN
  linarith

end PaperP1.SquarePoolLower
