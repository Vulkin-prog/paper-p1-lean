module

public import PaperP1.Arithmetic.ModeratePrimeAssignments
public import PaperP1.Arithmetic.MultiAnchorModuli

/-! # Counting actual moderate receiving tuples for t anchor kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorAssignments

open Finset PaperP1.PrimeAssignments PaperP1.ModeratePrimeAssignments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def receiverCost (t : ℕ) (P : Finset ℕ) (B N : ℕ) : ℝ :=
  (6 * (B : ℝ)) ^ t * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι /
    (↑(P.prod id) : ℝ)

theorem card_receiving_le {P : Finset ℕ} {B : ℕ} (t U N : ℕ) (hU : 1 ≤ U)
    (hN : 3 ^ t < N) (hB : 1 ≤ B) (hP : ∀ p ∈ P, Nat.Prime p)
    (hprod : P.prod id ≤ (3 * N) ^ t) (f : Code (ι := ι) P B)
    (hf : f ∈ moderateCodes P B N) :
    ((receiving U N f).card : ℝ) ≤ receiverCost (ι := ι) t P B N := by
  have hgroups : (∏ i, groupModulus f i) ≤ (3 * N) ^ t := by
    rw [product_groupModulus]
    exact hprod
  have hA : (1 : ℝ) ≤ 6 * B := by
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hupper (i : ι) : (groupModulus f i : ℝ) ≤ (6 * (B : ℝ)) * N := by
    have h : (groupModulus f i : ℝ) ≤ 6 * (N : ℝ) * B := by
      exact_mod_cast (mem_moderateCodes P B N f).mp hf i
    nlinarith
  have hcost := PaperP1.MultiAnchorModuli.product_cost_le t N hN (groupModulus f)
    (PaperP1.ModerateReceiverCost.modulus_pos (groupPrime f)
      (fun i p ↦ (groupPrime_prime hP f i p).pos)) hgroups (6 * (B : ℝ)) hA hupper
  have hcount := PaperP1.ModerateReceiverCost.card_assignments_le_cost U N
    (groupPrime f) (groupOffset f) hU (groupPrime_pairwise_coprime hP f)
  have h := hcount.trans hcost
  change ((receiving U N f).card : ℝ) ≤
    (6 * (B : ℝ)) ^ t * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι /
      (↑(∏ i, groupModulus f i) : ℝ) at h
  rw [product_groupModulus] at h
  exact h

theorem card_covered_le (t : ℕ) (P : Finset ℕ) (B U N : ℕ) (hU : 1 ≤ U)
    (hN : 3 ^ t < N) (hB : 1 ≤ B) (hP : ∀ p ∈ P, Nat.Prime p)
    (hprod : P.prod id ≤ (3 * N) ^ t) :
    ((covered (ι := ι) P B U N).card : ℝ) ≤
      (↑((Fintype.card ι * B) ^ P.card) : ℝ) * receiverCost (ι := ι) t P B N := by
  have hnonneg : 0 ≤ receiverCost (ι := ι) t P B N := by unfold receiverCost; positivity
  calc
    _ ≤ ((∑ f ∈ moderateCodes (ι := ι) P B N, (receiving U N f).card : ℕ) : ℝ) := by
      exact_mod_cast (card_biUnion_le : (covered (ι := ι) P B U N).card ≤ _)
    _ = ∑ f ∈ moderateCodes (ι := ι) P B N, ((receiving U N f).card : ℝ) := by norm_cast
    _ ≤ ∑ _f ∈ moderateCodes (ι := ι) P B N, receiverCost (ι := ι) t P B N :=
      sum_le_sum (fun f hf ↦ card_receiving_le t U N hU hN hB hP hprod f hf)
    _ = ((moderateCodes (ι := ι) P B N).card : ℝ) * receiverCost (ι := ι) t P B N := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_moderateCodes_le (ι := ι) P B N) hnonneg

end PaperP1.MultiAnchorAssignments
