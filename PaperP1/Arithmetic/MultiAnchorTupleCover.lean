module

public import PaperP1.Arithmetic.MultiAnchorValues
public import PaperP1.Arithmetic.MultiAnchorAssignments
public import PaperP1.Arithmetic.ModerateTupleCover

/-! # A finite cover of ordered tuples with t actual moderate anchors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorTupleCover

open Finset PaperP1.MultiAnchorValues
open PaperP1.ModerateAnchors (Receiver card_receiver)
open PaperP1.ModerateTupleCover (lift lift_at_anchor lift_at_receiver lift_restrict)

def anchorTuples {t r B N : ℕ} (Y : ℝ) (A : Anchor t r B N) : Finset (Fin r → ℕ) :=
  (PaperP1.ModeratePrimeAssignments.covered (ι := Receiver A.1) (primes Y A) B N N).image
    (lift A.1 A.2.1.val)

def goodAnchors (t r B N : ℕ) (Y T : ℝ) : Finset (Anchor t r B N) := by
  classical
  exact univ.filter (Good Y T)

def tupleCover (t r B N : ℕ) (Y T : ℝ) : Finset (Fin r → ℕ) :=
  (goodAnchors t r B N Y T).biUnion (anchorTuples Y)

def uniformCost (t r B N : ℕ) (Y T : ℝ) : ℝ :=
  (6 * (B : ℝ)) ^ t * 2 ^ (r - 1) * (N : ℝ) ^ (r - 1) *
    (↑(r * B) : ℝ) ^ (PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y) / T ^ t

theorem mem_anchorTuples {t r B N : ℕ} (Y : ℝ) (A : Anchor t r B N) (z : Fin r → ℕ) :
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

theorem mem_goodAnchors (t r B N : ℕ) (Y T : ℝ) (A : Anchor t r B N) :
    A ∈ goodAnchors t r B N Y T ↔ Good Y T A := by
  classical
  simp only [goodAnchors, mem_filter, mem_univ, true_and]

theorem mem_tupleCover (t r B N : ℕ) (Y T : ℝ) (z : Fin r → ℕ) :
    z ∈ tupleCover t r B N Y T ↔ ∃ A : Anchor t r B N, Good Y T A ∧
      z A.1 = A.2.1.val ∧ (fun j : Receiver A.1 ↦ z j.val) ∈
        PaperP1.ModeratePrimeAssignments.covered (primes Y A) B N N := by
  simp only [tupleCover, mem_biUnion, mem_goodAnchors, mem_anchorTuples]

theorem card_anchorTuples_le {t r B N : ℕ} (ht : 1 ≤ t) (hN : 3 ^ t < N)
    (hB : 2 ≤ B) (hBN : B ≤ N + 1) (Y T : ℝ) (hY : (B : ℝ) ≤ Y)
    (hT : 1 ≤ T) (A : Anchor t r B N) (hA : Good Y T A) :
    ((anchorTuples Y A).card : ℝ) ≤ uniformCost t r B N Y T := by
  have hNtwo : 2 ≤ N := by
    have : 0 < (3 : ℕ) ^ t := by positivity
    omega
  obtain ⟨_, hprod, hupper, hlower, hcard, hP⟩ :=
    anchor_data ht hNtwo hB hBN Y T hY hT A hA
  have hr : 1 ≤ r := by have := A.1.isLt; omega
  have hbase : 1 ≤ r * B := Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))
  have hcount : (Fintype.card (Receiver A.1) * B) ^ (primes Y A).card ≤
      (r * B) ^ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y := by
    rw [card_receiver]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right B (Nat.sub_le r 1)) _).trans
      (Nat.pow_le_pow_right hbase hcard)
  have hcountR : (↑((Fintype.card (Receiver A.1) * B) ^ (primes Y A).card) : ℝ) ≤
      (↑(r * B) : ℝ) ^ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y := by
    exact_mod_cast hcount
  have hcostNonneg : 0 ≤ PaperP1.MultiAnchorAssignments.receiverCost
      (ι := Receiver A.1) t (primes Y A) B N := by
    unfold PaperP1.MultiAnchorAssignments.receiverCost
    positivity
  have hcost : PaperP1.MultiAnchorAssignments.receiverCost
      (ι := Receiver A.1) t (primes Y A) B N ≤
      (6 * (B : ℝ)) ^ t * 2 ^ (r - 1) * (N : ℝ) ^ (r - 1) / T ^ t := by
    unfold PaperP1.MultiAnchorAssignments.receiverCost
    rw [card_receiver, hprod]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos (by linarith) t) hlower.le
  have hbound := PaperP1.MultiAnchorAssignments.card_covered_le
    (ι := Receiver A.1) t (primes Y A) B N N (by omega) hN (by omega)
    (fun p hp ↦ (hP p hp).1) (by rw [hprod]; exact hupper)
  calc
    _ ≤ ((PaperP1.ModeratePrimeAssignments.covered
        (ι := Receiver A.1) (primes Y A) B N N).card : ℝ) := by
      exact_mod_cast (card_image_le : (anchorTuples Y A).card ≤ _)
    _ ≤ _ := hbound
    _ ≤ (↑(r * B) : ℝ) ^ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y *
        ((6 * (B : ℝ)) ^ t * 2 ^ (r - 1) * (N : ℝ) ^ (r - 1) / T ^ t) :=
      mul_le_mul hcountR hcost hcostNonneg (by positivity)
    _ = _ := by unfold uniformCost; ring

theorem card_tupleCover_le (t r B N : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (hN : 3 ^ t < N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) :
    ((tupleCover t r B N Y T).card : ℝ) ≤
      (6 : ℝ) ^ t * r * (B : ℝ) ^ (2 * t) * 2 ^ (r - 1) * (N : ℝ) ^ r / T ^ t *
        (↑(r * B) : ℝ) ^ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y := by
  have hnonneg : 0 ≤ uniformCost t r B N Y T := by unfold uniformCost; positivity
  have hanchors : (goodAnchors t r B N Y T).card ≤ r * N * B ^ t := by
    classical
    calc
      _ ≤ (univ : Finset (Anchor t r B N)).card := card_filter_le _ _
      _ = _ := by rw [card_univ, card_anchor]
  have hNpow : (N : ℝ) ^ (r - 1) * (N : ℝ) = (N : ℝ) ^ r := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  have hBpow : (B : ℝ) ^ (2 * t) = ((B : ℝ) ^ t) ^ 2 := by
    rw [Nat.mul_comm 2 t, pow_mul]
  calc
    _ ≤ ((∑ A ∈ goodAnchors t r B N Y T, (anchorTuples Y A).card : ℕ) : ℝ) := by
      exact_mod_cast (card_biUnion_le : (tupleCover t r B N Y T).card ≤ _)
    _ = ∑ A ∈ goodAnchors t r B N Y T, ((anchorTuples Y A).card : ℝ) := by norm_cast
    _ ≤ ∑ _A ∈ goodAnchors t r B N Y T, uniformCost t r B N Y T :=
      sum_le_sum (fun A hA ↦ card_anchorTuples_le ht hN hB hBN Y T hY hT A
        ((mem_goodAnchors t r B N Y T A).mp hA))
    _ = ((goodAnchors t r B N Y T).card : ℝ) * uniformCost t r B N Y T := by simp
    _ ≤ (↑(r * N * B ^ t) : ℝ) * uniformCost t r B N Y T :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hanchors) hnonneg
    _ = _ := by
      unfold uniformCost
      rw [← hNpow, hBpow]
      push_cast
      rw [mul_pow]
      ring

end PaperP1.MultiAnchorTupleCover
