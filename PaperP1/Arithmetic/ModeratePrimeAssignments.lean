module

public import PaperP1.Arithmetic.PrimeAssignments

/-! # Counting all moderate assignments of a fixed actual prime product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModeratePrimeAssignments

open Finset PaperP1.PrimeAssignments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def receiving {P : Finset ℕ} {B : ℕ} (U N : ℕ) (f : Code (ι := ι) P B) : Finset (ι → ℕ) :=
  PaperP1.ModerateReceiverCost.assignments U N (groupPrime f) (groupOffset f)

def moderateCodes (P : Finset ℕ) (B N : ℕ) : Finset (Code (ι := ι) P B) := by
  classical
  exact univ.filter fun f ↦ ∀ i, groupModulus f i ≤ 6 * N * B

def covered (P : Finset ℕ) (B U N : ℕ) : Finset (ι → ℕ) :=
  (moderateCodes (ι := ι) P B N).biUnion fun f ↦ receiving U N f

def receiverCost (P : Finset ℕ) (B N : ℕ) : ℝ :=
  36 * (B : ℝ) ^ 2 * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(P.prod id) : ℝ)

theorem mem_moderateCodes (P : Finset ℕ) (B N : ℕ) (f : Code (ι := ι) P B) :
    f ∈ moderateCodes P B N ↔ ∀ i, groupModulus f i ≤ 6 * N * B := by
  classical
  simp only [moderateCodes, mem_filter, mem_univ, true_and]

theorem mem_receiving {P : Finset ℕ} {B : ℕ} (U N : ℕ) (f : Code (ι := ι) P B) (z : ι → ℕ) :
    z ∈ receiving U N f ↔ ∀ i, z i ∈ Finset.Ico U (U + N) ∧
      ∀ p : P, (f p).1 = i → p.val ∣ z i - 1 + (f p).2.val := by
  rw [receiving, PaperP1.ModerateReceiverCost.mem_assignments]
  constructor
  · intro h i
    refine ⟨(h i).1, ?_⟩
    intro p hp
    exact (h i).2 ⟨p, hp⟩
  · intro h i
    exact ⟨(h i).1, fun p ↦ (h i).2 p.val p.property⟩

theorem card_moderateCodes_le (P : Finset ℕ) (B N : ℕ) :
    (moderateCodes (ι := ι) P B N).card ≤ (Fintype.card ι * B) ^ P.card := by
  classical
  calc
    _ ≤ (univ : Finset (Code (ι := ι) P B)).card := card_filter_le _ _
    _ = Fintype.card (Code (ι := ι) P B) := card_univ
    _ = _ := card_codes P B

theorem card_receiving_le {P : Finset ℕ} {B : ℕ} (U N : ℕ) (hU : 1 ≤ U)
    (hN : 10 ≤ N) (hB : 1 ≤ B) (hP : ∀ p ∈ P, Nat.Prime p)
    (hprod : P.prod id ≤ 9 * N ^ 2) (f : Code (ι := ι) P B) (hf : f ∈ moderateCodes P B N) :
    ((receiving U N f).card : ℝ) ≤ receiverCost (ι := ι) P B N := by
  have hgroups : (∏ i, groupModulus f i) ≤ 9 * N ^ 2 := by
    rw [product_groupModulus]
    exact hprod
  have h := PaperP1.ModerateReceiverCost.card_assignments_le_moderate U N B hU hN hB
    (groupPrime f) (groupOffset f) (fun i p ↦ (groupPrime_prime hP f i p).pos)
    (groupPrime_pairwise_coprime hP f) hgroups ((mem_moderateCodes P B N f).mp hf)
  change ((receiving U N f).card : ℝ) ≤
    36 * (B : ℝ) ^ 2 * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι /
      (↑(∏ i, groupModulus f i) : ℝ) at h
  rw [product_groupModulus] at h
  exact h

theorem card_covered_le (P : Finset ℕ) (B U N : ℕ) (hU : 1 ≤ U)
    (hN : 10 ≤ N) (hB : 1 ≤ B) (hP : ∀ p ∈ P, Nat.Prime p) (hprod : P.prod id ≤ 9 * N ^ 2) :
    ((covered (ι := ι) P B U N).card : ℝ) ≤
      (↑((Fintype.card ι * B) ^ P.card) : ℝ) * receiverCost (ι := ι) P B N := by
  have hnonneg : 0 ≤ receiverCost (ι := ι) P B N := by unfold receiverCost; positivity
  calc
    _ ≤ ((∑ f ∈ moderateCodes (ι := ι) P B N, (receiving U N f).card : ℕ) : ℝ) := by
      exact_mod_cast (card_biUnion_le : (covered (ι := ι) P B U N).card ≤ _)
    _ = ∑ f ∈ moderateCodes (ι := ι) P B N, ((receiving U N f).card : ℝ) := by norm_cast
    _ ≤ ∑ _f ∈ moderateCodes (ι := ι) P B N, receiverCost (ι := ι) P B N :=
      sum_le_sum (fun f hf ↦ card_receiving_le U N hU hN hB hP hprod f hf)
    _ = ((moderateCodes (ι := ι) P B N).card : ℝ) * receiverCost (ι := ι) P B N := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_moderateCodes_le (ι := ι) P B N) hnonneg

end PaperP1.ModeratePrimeAssignments
