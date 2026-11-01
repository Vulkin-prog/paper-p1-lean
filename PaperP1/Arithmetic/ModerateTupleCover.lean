module

public import PaperP1.Arithmetic.ModerateAnchors

/-! # The finite anchored moderate-certificate cover of ordered window tuples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModerateTupleCover

open Finset PaperP1.ModerateAnchors

def lift {r : ℕ} (a : Fin r) (c : ℕ) (z : Receiver a → ℕ) : Fin r → ℕ :=
  fun j ↦ if h : j = a then c else z ⟨j, h⟩

def anchorTuples {r B N : ℕ} (Y : ℝ) (A : Anchor r B N) : Finset (Fin r → ℕ) :=
  (PaperP1.ModeratePrimeAssignments.covered (ι := Receiver A.1) (primes Y A) B N N).image
    (lift A.1 A.2.1.val)

def goodAnchors (r B N : ℕ) (Y T : ℝ) : Finset (Anchor r B N) := by
  classical
  exact univ.filter (Good Y T)

def tupleCover (r B N : ℕ) (Y T : ℝ) : Finset (Fin r → ℕ) :=
  (goodAnchors r B N Y T).biUnion (anchorTuples Y)

def uniformCost (r B N : ℕ) (Y T : ℝ) : ℝ :=
  36 * (B : ℝ) ^ 2 * 2 ^ (r - 1) * (N : ℝ) ^ (r - 1) *
    (↑(r * B) : ℝ) ^ (PaperP1.PrimeProductBudget.assignmentExponent N Y) / T ^ 2

theorem lift_at_anchor {r : ℕ} (a : Fin r) (c : ℕ) (z : Receiver a → ℕ) : lift a c z a = c := by
  simp [lift]

theorem lift_at_receiver {r : ℕ} (a : Fin r) (c : ℕ) (z : Receiver a → ℕ) (j : Receiver a) :
    lift a c z j.val = z j := by
  simp only [lift, dite_eq_right j.property]

theorem lift_restrict {r : ℕ} (a : Fin r) (z : Fin r → ℕ) :
    lift a (z a) (fun j : Receiver a ↦ z j.val) = z := by
  funext j
  by_cases h : j = a
  · simp [lift, h]
  · simp [lift, h]

theorem mem_anchorTuples {r B N : ℕ} (Y : ℝ) (A : Anchor r B N) (z : Fin r → ℕ) :
    z ∈ anchorTuples Y A ↔ z A.1 = A.2.1.val ∧
      (fun j : Receiver A.1 ↦ z j.val) ∈
        PaperP1.ModeratePrimeAssignments.covered (primes Y A) B N N := by
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    refine ⟨lift_at_anchor _ _ _, ?_⟩
    have heq : (fun j : Receiver A.1 ↦ lift A.1 A.2.1.val w j.val) = w := by
      funext j
      exact lift_at_receiver _ _ _ j
    rw [heq]
    exact hw
  · rintro ⟨ha, hrecv⟩
    apply mem_image.mpr
    refine ⟨(fun j : Receiver A.1 ↦ z j.val), hrecv, ?_⟩
    rw [← ha]
    exact lift_restrict _ _

theorem mem_goodAnchors (r B N : ℕ) (Y T : ℝ) (A : Anchor r B N) :
    A ∈ goodAnchors r B N Y T ↔ Good Y T A := by
  classical
  simp only [goodAnchors, mem_filter, mem_univ, true_and]

theorem mem_tupleCover (r B N : ℕ) (Y T : ℝ) (z : Fin r → ℕ) :
    z ∈ tupleCover r B N Y T ↔ ∃ A : Anchor r B N, Good Y T A ∧ z A.1 = A.2.1.val ∧
      (fun j : Receiver A.1 ↦ z j.val) ∈
        PaperP1.ModeratePrimeAssignments.covered (primes Y A) B N N := by
  simp only [tupleCover, mem_biUnion, mem_goodAnchors, mem_anchorTuples]

theorem card_anchorTuples_le {r B N : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) (A : Anchor r B N) (hA : Good Y T A) :
    ((anchorTuples Y A).card : ℝ) ≤ uniformCost r B N Y T := by
  obtain ⟨_, hprod, hupper, hlower, hcard, hP⟩ := anchor_data hN hB hBN Y T hY (by linarith) A hA
  have hr : 1 ≤ r := by have := A.1.isLt; omega
  have hbase : 1 ≤ r * B := Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))
  have hcount : (Fintype.card (Receiver A.1) * B) ^ (primes Y A).card ≤
      (r * B) ^ PaperP1.PrimeProductBudget.assignmentExponent N Y := by
    rw [card_receiver]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right B (Nat.sub_le r 1)) _).trans
      (Nat.pow_le_pow_right hbase hcard)
  have hcountR : (↑((Fintype.card (Receiver A.1) * B) ^ (primes Y A).card) : ℝ) ≤
      (↑(r * B) : ℝ) ^ PaperP1.PrimeProductBudget.assignmentExponent N Y := by exact_mod_cast hcount
  have hcostNonneg : 0 ≤ PaperP1.ModeratePrimeAssignments.receiverCost (ι := Receiver A.1) (primes Y A) B N := by
    unfold PaperP1.ModeratePrimeAssignments.receiverCost
    positivity
  have hcost : PaperP1.ModeratePrimeAssignments.receiverCost (ι := Receiver A.1) (primes Y A) B N ≤
      36 * (B : ℝ) ^ 2 * 2 ^ (r - 1) * (N : ℝ) ^ (r - 1) / T ^ 2 := by
    unfold PaperP1.ModeratePrimeAssignments.receiverCost
    rw [card_receiver, hprod]
    exact div_le_div_of_nonneg_left (by positivity) (by nlinarith : 0 < T ^ 2) hlower.le
  have hbound := PaperP1.ModeratePrimeAssignments.card_covered_le (ι := Receiver A.1)
    (primes Y A) B N N (by omega) hN (by omega) (fun p hp ↦ (hP p hp).1)
    (by rw [hprod]; exact hupper)
  calc
    _ ≤ ((PaperP1.ModeratePrimeAssignments.covered (ι := Receiver A.1) (primes Y A) B N N).card : ℝ) := by
      exact_mod_cast (card_image_le : (anchorTuples Y A).card ≤ _)
    _ ≤ _ := hbound
    _ ≤ (↑(r * B) : ℝ) ^ PaperP1.PrimeProductBudget.assignmentExponent N Y *
        (36 * (B : ℝ) ^ 2 * 2 ^ (r - 1) * (N : ℝ) ^ (r - 1) / T ^ 2) :=
      mul_le_mul hcountR hcost hcostNonneg (by positivity)
    _ = _ := by unfold uniformCost; ring

theorem card_tupleCover_le (r B N : ℕ) (hr : 1 ≤ r) (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) :
    ((tupleCover r B N Y T).card : ℝ) ≤
      36 * (r : ℝ) * (B : ℝ) ^ 4 * 2 ^ (r - 1) * (N : ℝ) ^ r / T ^ 2 *
        (↑(r * B) : ℝ) ^ PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  have hnonneg : 0 ≤ uniformCost r B N Y T := by unfold uniformCost; positivity
  have hanchors : (goodAnchors r B N Y T).card ≤ r * N * B ^ 2 := by
    classical
    calc
      _ ≤ (univ : Finset (Anchor r B N)).card := card_filter_le _ _
      _ = _ := by rw [card_univ, card_anchor]
  have hNpow : (N : ℝ) ^ (r - 1) * (N : ℝ) = (N : ℝ) ^ r := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  calc
    _ ≤ ((∑ A ∈ goodAnchors r B N Y T, (anchorTuples Y A).card : ℕ) : ℝ) := by
      exact_mod_cast (card_biUnion_le : (tupleCover r B N Y T).card ≤ _)
    _ = ∑ A ∈ goodAnchors r B N Y T, ((anchorTuples Y A).card : ℝ) := by norm_cast
    _ ≤ ∑ _A ∈ goodAnchors r B N Y T, uniformCost r B N Y T :=
      sum_le_sum (fun A hA ↦ card_anchorTuples_le hN hB hBN Y T hY hT A ((mem_goodAnchors r B N Y T A).mp hA))
    _ = ((goodAnchors r B N Y T).card : ℝ) * uniformCost r B N Y T := by simp
    _ ≤ (↑(r * N * B ^ 2) : ℝ) * uniformCost r B N Y T :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hanchors) hnonneg
    _ = _ := by
      unfold uniformCost
      rw [← hNpow]
      push_cast
      ring

end PaperP1.ModerateTupleCover
