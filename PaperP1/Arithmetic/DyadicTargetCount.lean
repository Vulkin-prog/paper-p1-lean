module

public import PaperP1.Arithmetic.DyadicEndpointPairs

/-! # A finite target pool for all bounded affine parameter choices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicTargetCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.DyadicTargetInterior

def codes (a H : ℕ) : Finset ((ℕ × ℕ) × ℤ) :=
  ((Icc 1 (2 * a * H)) ×ˢ (Icc 1 H)) ×ˢ (Icc (-(H : ℤ)) (H : ℤ))

def decode (t : ℕ) (w : (ℕ × ℕ) × ℤ) : ℕ := (((w.1.1 : ℤ) * t + w.2) / w.1.2).toNat

def pool (a H t : ℕ) : Finset ℕ := (codes a H).image (decode t)

theorem codes_card (a H : ℕ) : (codes a H).card = 2 * a * H * H * (2 * H + 1) := by
  have hc : (Icc 1 (2 * a * H)).card = 2 * a * H := by rw [Nat.card_Icc]; omega
  have hd : (Icc 1 H).card = H := by rw [Nat.card_Icc]; omega
  have hh : (Icc (-(H : ℤ)) (H : ℤ)).card = 2 * H + 1 := by
    simpa only [Nat.cast_zero, zero_sub, zero_add] using DyadicEndpointPairs.integer_interval_card 0 H
  rw [codes, card_product, card_product, hc, hd, hh]

theorem pool_card (a H t : ℕ) : (pool a H t).card ≤ 2 * a * H * H * (2 * H + 1) := by
  exact card_image_le.trans_eq (codes_card a H)

theorem mem_pool {a H t c d z : ℕ} {h : ℤ} (hc : 0 < c) (hd : 0 < d)
    (hcH : c ≤ 2 * a * H) (hdH : d ≤ H) (hh : |h| ≤ H)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) : z ∈ pool a H t := by
  have hcode : ((c, d), h) ∈ codes a H := by
    apply mem_product.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hc, hcH⟩, mem_Icc.mpr ⟨hd, hdH⟩⟩, ?_⟩
    exact mem_Icc.mpr (abs_le.mp hh)
  apply mem_image.mpr
  refine ⟨((c, d), h), hcode, ?_⟩
  change (((c : ℤ) * t + h) / (d : ℤ)).toNat = z
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [← htarget, Int.mul_ediv_cancel_left _ hdZ, Int.toNat_natCast]

theorem actual_target_mem_pool {N L x y z a b c d t H : ℕ} {h : ℤ} (hN : 0 < N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hc : 0 < c) (hd : 0 < d) (hdH : d ≤ H) (hh : |h| ≤ H)
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : a * (2 * H * ((L + 1) + 1)) + (L + 1) < N) : z ∈ pool a H t := by
  have hsrcA := (ActualDyadicInterior.source_parameter_bounds hN hx i hbaseX).1
  have hsrcB := (ActualDyadicInterior.source_parameter_bounds hN hy j hbaseY).2
  have ht := ActualDyadicInterior.parameter_large hN hx i hbaseX hsize
  have hcmax := (weak_ratio_bounds hsrcA hsrcB (mem_Ico.mp hz).1
    (Nat.le_of_lt (mem_Ico.mp hz).2) hdH hh htarget ht).2
  exact mem_pool hc hd (hcmax.trans (Nat.mul_le_mul_left (2 * a) hdH)) hdH hh htarget

theorem pool_card_cubic {a H t : ℕ} (hH : 1 ≤ H) : (pool a H t).card ≤ 6 * a * H ^ 3 := by
  have h := Nat.mul_le_mul_left (2 * a * H * H) (show 2 * H + 1 ≤ 3 * H by omega)
  have hcard := pool_card a H t
  nlinarith only [h, hcard]

theorem pool_card_polynomial {a H t B J : ℕ} (hH : 1 ≤ H) (hheight : H ≤ B ^ J) :
    (pool a H t).card ≤ 6 * a * B ^ (3 * J) := by
  calc
    _ ≤ 6 * a * H ^ 3 := pool_card_cubic hH
    _ ≤ 6 * a * (B ^ J) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hheight 3)
    _ = _ := by rw [← pow_mul]; congr 2; omega

end PaperP1.DyadicTargetCount
