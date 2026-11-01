module

public import PaperP1.Arithmetic.ShortIntervalCongruences
public import PaperP1.Arithmetic.ModerateModuli
public import Mathlib.Data.Fintype.Pi

/-! # The actual receiving-centre cost of a fixed moderate congruence certificate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModerateReceiverCost

open Finset PaperP1.ShortIntervalCongruences

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

def modulus (G : ∀ i, κ i → ℕ) (i : ι) : ℕ := ∏ p, G i p

def assignments (U N : ℕ) (G w : ∀ i, κ i → ℕ) : Finset (ι → ℕ) := by
  classical
  exact Fintype.piFinset fun i ↦ fibre U N (G i) (w i)

theorem mem_assignments (U N : ℕ) (G w : ∀ i, κ i → ℕ) (z : ι → ℕ) :
    z ∈ assignments U N G w ↔ ∀ i, z i ∈ Finset.Ico U (U + N) ∧
      ∀ p, G i p ∣ z i - 1 + w i p := by
  classical
  simp only [assignments, Fintype.mem_piFinset, mem_fibre]

omit [Fintype ι] in
theorem modulus_pos (G : ∀ i, κ i → ℕ) (hG : ∀ i p, 1 ≤ G i p) (i : ι) :
    1 ≤ modulus G i := by
  exact one_le_prod (fun p _ ↦ hG i p)

theorem card_assignments_le_cost (U N : ℕ) (G w : ∀ i, κ i → ℕ) (hU : 1 ≤ U)
    (hcop : ∀ i, Pairwise (fun p q ↦ Nat.Coprime (G i p) (G i q))) :
    ((assignments U N G w).card : ℝ) ≤ ∏ i, (1 + (N : ℝ) / modulus G i) := by
  classical
  rw [assignments, Fintype.card_piFinset, Nat.cast_prod]
  apply prod_le_prod₀
  · intro i _
    exact Nat.cast_nonneg _
  · intro i _
    have hcard : ((fibre U N (G i) (w i)).card : ℝ) ≤ ((N / modulus G i + 1 : ℕ) : ℝ) := by
      exact_mod_cast card_fibre_le U N (G i) (w i) hU (hcop i)
    have hdiv : ((N / modulus G i : ℕ) : ℝ) ≤ (N : ℝ) / modulus G i := Nat.cast_div_le
    simp only [Nat.cast_add, Nat.cast_one] at hcard
    linarith

theorem card_assignments_le_moderate (U N B : ℕ) (hU : 1 ≤ U) (hN : 10 ≤ N) (hB : 1 ≤ B)
    (G w : ∀ i, κ i → ℕ) (hG : ∀ i p, 1 ≤ G i p)
    (hcop : ∀ i, Pairwise (fun p q ↦ Nat.Coprime (G i p) (G i q)))
    (hprod : (∏ i, modulus G i) ≤ 9 * N ^ 2) (hupper : ∀ i, modulus G i ≤ 6 * N * B) :
    ((assignments U N G w).card : ℝ) ≤
      36 * (B : ℝ) ^ 2 * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι /
        (↑(∏ i, modulus G i) : ℝ) := by
  have hA : (1 : ℝ) ≤ 6 * B := by
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hupperR (i : ι) : (modulus G i : ℝ) ≤ (6 * (B : ℝ)) * N := by
    have h : (modulus G i : ℝ) ≤ 6 * (N : ℝ) * B := by exact_mod_cast hupper i
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hcost := PaperP1.ModerateModuli.product_cost_le N hN (modulus G)
    (modulus_pos G hG) hprod (6 * (B : ℝ)) hA hupperR
  calc
    _ ≤ ∏ i, (1 + (N : ℝ) / modulus G i) := card_assignments_le_cost U N G w hU hcop
    _ ≤ (6 * (B : ℝ)) ^ 2 * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι /
        (↑(∏ i, modulus G i) : ℝ) := hcost
    _ = _ := by ring

end PaperP1.ModerateReceiverCost
