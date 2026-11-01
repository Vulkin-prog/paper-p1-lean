module

public import PaperP1.Arithmetic.TruncatedKernelProducts
public import PaperP1.Arithmetic.ModeratePrimeAssignments

/-! # Actual anchor values and their bounded prime product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModerateAnchors

open Finset PaperP1.RankinSmallKernel PaperP1.TruncatedKernelProducts

abbrev Anchor (r B N : ℕ) := Fin r × (Finset.Ico N (2 * N)) × (Fin B × Fin B)

abbrev Receiver {r : ℕ} (a : Fin r) := {j : Fin r // j ≠ a}

def firstValue {r B N : ℕ} (A : Anchor r B N) : ℕ := A.2.1.val - 1 + A.2.2.1.val

def secondValue {r B N : ℕ} (A : Anchor r B N) : ℕ := A.2.1.val - 1 + A.2.2.2.val

def product {r B N : ℕ} (Y : ℝ) (A : Anchor r B N) : ℕ :=
  truncatedKernel Y (firstValue A) * truncatedKernel Y (secondValue A)

def primes {r B N : ℕ} (Y : ℝ) (A : Anchor r B N) : Finset ℕ := (product Y A).primeFactors

def Good {r B N : ℕ} (Y T : ℝ) (A : Anchor r B N) : Prop :=
  A.2.2.1 ≠ A.2.2.2 ∧ T < (truncatedKernel Y (firstValue A) : ℝ) ∧
    T < (truncatedKernel Y (secondValue A) : ℝ)

theorem card_anchor (r B N : ℕ) : Fintype.card (Anchor r B N) = r * N * B ^ 2 := by
  simp only [Anchor, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.card_Ico,
    two_mul, Nat.add_sub_cancel_left]
  ring

theorem card_receiver {r : ℕ} (a : Fin r) : Fintype.card (Receiver a) = r - 1 := by
  simpa only [Receiver, Fintype.card_fin, Fintype.card_subtype_eq] using
    Fintype.card_subtype_compl (fun j : Fin r ↦ j = a)

theorem values_bounds {r B N : ℕ} (hN : 10 ≤ N) (hBN : B ≤ N + 1) (A : Anchor r B N) :
    0 < firstValue A ∧ firstValue A ≤ 3 * N ∧ 0 < secondValue A ∧ secondValue A ≤ 3 * N := by
  have hc := mem_Ico.mp A.2.1.property
  have hu := A.2.2.1.isLt
  have hv := A.2.2.2.isLt
  dsimp [firstValue, secondValue]
  omega

theorem values_dist_le {r B N : ℕ} (A : Anchor r B N) : Nat.dist (firstValue A) (secondValue A) ≤ B := by
  have hu := A.2.2.1.isLt
  have hv := A.2.2.2.isLt
  rcases le_total (firstValue A) (secondValue A) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    dsimp [firstValue, secondValue]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    dsimp [firstValue, secondValue]
    omega

theorem good_values_ne {r B N : ℕ} (Y T : ℝ) (A : Anchor r B N) (hA : Good Y T A) :
    firstValue A ≠ secondValue A := by
  intro h
  have hval : A.2.2.1.val = A.2.2.2.val := Nat.add_left_cancel h
  exact hA.1 (Fin.ext hval)

theorem anchor_data {r B N : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 0 ≤ T) (A : Anchor r B N) (hA : Good Y T A) :
    0 < product Y A ∧ (primes Y A).prod id = product Y A ∧ product Y A ≤ 9 * N ^ 2 ∧
      T ^ 2 < (product Y A : ℝ) ∧
      (primes Y A).card ≤ PaperP1.PrimeProductBudget.assignmentExponent N Y ∧
      ∀ p ∈ primes Y A, Nat.Prime p ∧ Y < (p : ℝ) := by
  have hY1 : 1 < Y := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  obtain ⟨hn, hnN, hm, hmN⟩ := values_bounds hN hBN A
  have hne := good_values_ne Y T A hA
  have hdist : (Nat.dist (firstValue A) (secondValue A) : ℝ) ≤ Y :=
    (by exact_mod_cast values_dist_le A : (Nat.dist (firstValue A) (secondValue A) : ℝ) ≤ B).trans hY
  have hsq : Squarefree (product Y A) := kernel_pair_squarefree Y _ _ hne hdist
  refine ⟨Nat.mul_pos (kernel_pos Y _) (kernel_pos Y _), ?_,
    kernel_pair_upper Y _ _ N hn hm hnN hmN,
    kernel_pair_gt_square Y _ _ T hT hA.2.1 hA.2.2,
    kernel_pair_card_le_assignmentExponent Y hY1 _ _ N hn hm hne hdist hnN hmN, ?_⟩
  · exact Nat.prod_primeFactors_of_squarefree hsq
  · intro p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, kernel_pair_prime_above Y _ _ p hp⟩

end PaperP1.ModerateAnchors
