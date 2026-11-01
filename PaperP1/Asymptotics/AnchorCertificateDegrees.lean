module

public import PaperP1.Arithmetic.AnchorCertificateGraph
public import PaperP1.Asymptotics.ShortCertificateDegreeBudget

/-! # Actual incoming and outgoing certificate counts with exponent 1/A -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchorCertificateDegrees

open Finset Filter PaperP1.AnchorCertificateGraph

theorem uniform_degrees (C t : ℕ) (hC : 1 ≤ C) (ht : 1 ≤ t) (A E ε : ℝ)
    (hA : 0 < A) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, (W : ℝ) ≤ E * Real.log N →
      ∀ G : Finset ℕ, (∀ n ∈ G, W < n ∧ n ≤ C * N) → ∀ x ∈ G,
      ((outgoing G (C * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε) ∧
      ((incoming G (C * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε) := by
  let D := 2 * E + 1
  let H := 2 * (C : ℝ) * D
  let K := (t : ℝ) * Real.exp 1
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hH : 1 ≤ H := by
    have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [H]
    nlinarith only [hCr, hD]
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hexp : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hK : 1 ≤ K := by
    dsimp [K]
    exact htR.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg t))
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp
    (PaperP1.ShortCertificateDegreeBudget.product_le_power_eventually A H D K ε t hA hH hD (by linarith) hε)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2))
  refine ⟨max 2 (max Nb Nl), ?_⟩
  intro N hN W hwidth G hG x hx
  let B := 2 * W + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hl2 : 2 ≤ Real.log N := hNl N (by omega)
  have hl : 0 < Real.log N := by linarith
  have hBwidth : (B : ℝ) ≤ D * Real.log N := by
    dsimp [B, D]
    push_cast
    nlinarith only [hwidth, hl2]
  have hZeq : (threshold (C * N) W : ℝ) = 2 * (C : ℝ) * N * B := by
    dsimp [threshold, B]
    rw [PaperP1.BoundedIntegerMotifs.offsets_card]
    push_cast
    ring
  have hZpos : 0 < threshold (C * N) W := by
    have hNpos : 0 < N := by omega
    have hCp : 0 < C := by omega
    dsimp [threshold]
    rw [PaperP1.BoundedIntegerMotifs.offsets_card]
    positivity
  have hheight : (threshold (C * N) W : ℝ) ≤ H * N * Real.log N := by
    rw [hZeq]
    have hmul := mul_le_mul_of_nonneg_left hBwidth (by positivity : (0 : ℝ) ≤ 2 * C * N)
    simpa only [H, mul_assoc, mul_left_comm, mul_comm] using hmul
  have horder := PaperP1.ShortCertificateOrder.passage_le_upper A H N (threshold (C * N) W)
    hA hH (by omega) hl2 hZpos hheight
  have hbase : 1 ≤ K * B := by
    exact hK.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hBr (by linarith : 0 ≤ K))
  have hcost : (B : ℝ) ^ t * (K * B) ^ order (C * N) W ((Real.log N) ^ A) ≤
      (N : ℝ) ^ (1 / A + ε) := by
    calc
      _ ≤ (B : ℝ) ^ t * (K * B) ^ PaperP1.ShortCertificateOrder.upper A H N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase horder) (pow_nonneg (Nat.cast_nonneg B) t)
      _ ≤ _ := hNb N (by omega) B hB hBwidth
  have hY : 1 < (Real.log N) ^ A := Real.one_lt_rpow (by linarith) hA
  have hout := outgoing_count G (C * N) W t x ((Real.log N) ^ A) ht hY hG hx
  have hin := incoming_count G (C * N) W t x ((Real.log N) ^ A) ht hY hG hx
  have hout' : ((outgoing G (C * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤
      (B : ℝ) ^ t * (K * B) ^ order (C * N) W ((Real.log N) ^ A) := by
    simpa only [B, K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hout
  have hin' : ((incoming G (C * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤
      (B : ℝ) ^ t * (K * B) ^ order (C * N) W ((Real.log N) ^ A) := by
    simpa only [B, K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hin
  exact ⟨hout'.trans hcost, hin'.trans hcost⟩

end PaperP1.AnchorCertificateDegrees
