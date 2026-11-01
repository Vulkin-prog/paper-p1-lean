module

public import PaperP1.Arithmetic.NormalizedMotifs
public import PaperP1.Arithmetic.TwoProgressionResidualRank

/-! # Exact interval geometry of the deduplicated normalized pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedPairGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.TwoProgressionPrimeRows PaperP1.NormalizedMotifs

theorem values_closed {x L : ℕ} (hx : 0 < x) :
    NormalizedWindowSets.values x L = Icc (x - 1) (x - 1 + L) := by
  rw [values_eq_interval hx]
  ext n
  simp only [mem_Ico, mem_Icc]
  omega

theorem normalized_progression {a x L : ℕ} (hx : 0 < x) :
    normalized a x L = progression a (x - 1) L := by
  rw [normalized, FiniteEvenSquareClasses.dilate, values_closed hx]
  rfl

theorem union_card_le {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
    (NormalizedWindowSets.union a b x y L).card ≤ 2 * (L + 1) := by
  have h := card_union_le (normalized b x L) (normalized a y L)
  rw [card_normalized hb hx, card_normalized ha hy] at h
  exact h.trans (by omega)

theorem union_bounds {a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (i j : Fin (L + 1)) (hunit : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j)
    (n : ℕ) (hn : n ∈ NormalizedWindowSets.union a b x y L) :
    b * startCompleteVertexLabel x L i - b * L ≤ n ∧ n ≤ b * startCompleteVertexLabel x L i + b * L := by
  have hnZ : (n : ℤ) ∈ (NormalizedWindowSets.union a b x y L).image (fun n : ℕ ↦ (n : ℤ)) :=
    mem_image.mpr ⟨n, hn, rfl⟩
  rw [translated_motif hx hy i j hunit] at hnZ
  obtain ⟨w, hw, heq⟩ := mem_image.mp hnZ
  have hbound := abs_le.mp (motif_bound hab i j w hw)
  have hlo : ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) ≤ (n : ℤ) + ((b * L : ℕ) : ℤ) := by
    push_cast
    push_cast at heq
    linarith
  have hhi : (n : ℤ) ≤ ((b * startCompleteVertexLabel x L i + b * L : ℕ) : ℤ) := by
    push_cast
    push_cast at heq
    linarith
  have hloN : b * startCompleteVertexLabel x L i ≤ n + b * L := by exact_mod_cast hlo
  exact ⟨by omega, by exact_mod_cast hhi⟩

theorem anchor_geometry {N b x L : ℕ} (hN : 8 * (L + 1) ≤ N) (hxN : N ≤ x) (hb : 0 < b)
    (i : Fin (L + 1)) :
    b * L ≤ b * startCompleteVertexLabel x L i ∧
    4 * b * L ≤ b * startCompleteVertexLabel x L i - b * L ∧
      N ≤ 2 * (b * startCompleteVertexLabel x L i - b * L) := by
  have hx : 0 < x := by omega
  have hlabel : N - 1 ≤ startCompleteVertexLabel x L i := by
    have hmem := mem_Ico.mp ((values_eq_interval hx).symm ▸ (mem_values.mpr ⟨i, rfl⟩))
    omega
  have hL : L ≤ startCompleteVertexLabel x L i := by omega
  have hfive : 5 * L ≤ startCompleteVertexLabel x L i := by omega
  have hA : b * L ≤ b * startCompleteVertexLabel x L i := Nat.mul_le_mul_left b hL
  have hprod : b * (startCompleteVertexLabel x L i - L) + b * L = b * startCompleteVertexLabel x L i := by
    rw [← mul_add, Nat.sub_add_cancel hL]
  have hUeq : b * startCompleteVertexLabel x L i - b * L = b * (startCompleteVertexLabel x L i - L) := by omega
  have hUge : startCompleteVertexLabel x L i - L ≤ b * startCompleteVertexLabel x L i - b * L := by
    rw [hUeq]
    simpa only [one_mul] using Nat.mul_le_mul_right (startCompleteVertexLabel x L i - L) (show 1 ≤ b by omega)
  have hfiveMul := Nat.mul_le_mul_left b hfive
  refine ⟨hA, ?_⟩
  constructor
  · nlinarith
  · omega

theorem logarithmic_width {B R : ℕ} (hB : 2 ≤ B) (hR : 0 < R) (hwidth : R ≤ 2 * B ^ 4) :
    Real.log (64 * (R : ℝ)) ≤ 11 * Real.log B := by
  have hpow : 128 ≤ B ^ 7 := by
    have h := Nat.pow_le_pow_left hB 7
    norm_num at h
    exact h
  have hRbound : 64 * R ≤ B ^ 11 := by
    have hmul := Nat.mul_le_mul_right (B ^ 4) hpow
    have h64 := Nat.mul_le_mul_left 64 hwidth
    have hcombine : B ^ 7 * B ^ 4 = B ^ 11 := by rw [← pow_add]
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 64 * (R : ℝ)) (by exact_mod_cast hRbound : 64 * (R : ℝ) ≤ (B : ℝ) ^ 11)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

end PaperP1.NormalizedPairGeometry
