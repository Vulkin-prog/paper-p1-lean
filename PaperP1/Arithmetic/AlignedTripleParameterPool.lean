module

public import PaperP1.Arithmetic.DyadicTargetCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # A literal polynomial-size pool contains every bounded affine target of an exact source channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTripleParameterPool

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

abbrev Code (L : ℕ) := Σ _t : ℕ, (Fin (L + 1) × Fin (L + 1)) × ℕ

def pool (N L a J : ℕ) : Finset (Code L) :=
  (range (3 * N)).sigma fun t ↦ (univ : Finset (Fin (L + 1) × Fin (L + 1))) ×ˢ
    DyadicTargetCount.pool a ((L + 1) ^ J) t

def family (a b : ℕ) {L : ℕ} (p : Code L) : Finset ℕ :=
  {a * p.1 + 1 - p.2.1.1.val, b * p.1 + 1 - p.2.1.2.val, p.2.2}

def families (N L a b J : ℕ) : Finset (Finset ℕ) := (pool N L a J).image (family a b)

theorem pool_card (N L a J : ℕ) : (pool N L a J).card ≤ 18 * a * N * (L + 1) ^ (3 * J + 2) := by
  have hH : 1 ≤ (L + 1) ^ J := Nat.one_le_pow _ _ (by omega)
  calc
    _ = ∑ t ∈ range (3 * N), (L + 1) ^ 2 * (DyadicTargetCount.pool a ((L + 1) ^ J) t).card := by
      rw [pool, card_sigma]
      apply sum_congr rfl
      intro t _
      rw [card_product, card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]
    _ ≤ ∑ _t ∈ range (3 * N), (L + 1) ^ 2 * (6 * a * (L + 1) ^ (3 * J)) :=
      sum_le_sum (fun _ _ ↦ Nat.mul_le_mul_left _ (DyadicTargetCount.pool_card_polynomial hH le_rfl))
    _ = (3 * N) * ((L + 1) ^ 2 * (6 * a * (L + 1) ^ (3 * J))) := by
      simp only [sum_const, Nat.nsmul_eq_mul, card_range]
    _ = _ := by rw [pow_add]; ring

theorem families_card (N L a b J : ℕ) : (families N L a b J).card ≤ 18 * a * N * (L + 1) ^ (3 * J + 2) :=
  card_image_le.trans (pool_card N L a J)

theorem source_mem_pool {N L a b c d x y z t J : ℕ} {h : ℤ}
    (hN : 2 ≤ N) (ha : 0 < a)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hc : 0 < c) (hd : 0 < d) (hdH : d ≤ (L + 1) ^ J) (hh : |h| ≤ ((L + 1) ^ J : ℕ))
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : a * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) :
    ∃ p ∈ pool N L a J, family a b p = {x, y, z} := by
  have hxpos : 0 < x := by have hh := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have hh := (mem_Ico.mp hy).1; omega
  have hzpool := DyadicTargetCount.actual_target_mem_pool (by omega : 0 < N)
    hx hy hz hc hd hdH hh i j hbaseX hbaseY htarget hsize
  have hlabel := mem_Ico.mp ((NormalizedWindowSets.values_eq_interval hxpos).symm ▸
    (NormalizedWindowSets.mem_values.mpr ⟨i, rfl⟩))
  have hmul : t ≤ a * t := by simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ a by omega)
  have htN : t < 3 * N := by
    have hxy := mem_Ico.mp hx
    omega
  have hxf : a * t + 1 - i.val = x := by
    rw [startCompleteVertexLabel_eq_offset hxpos] at hbaseX
    omega
  have hyf : b * t + 1 - j.val = y := by
    rw [startCompleteVertexLabel_eq_offset hypos] at hbaseY
    omega
  refine ⟨⟨t, ((i, j), z)⟩, mem_sigma.mpr ⟨mem_range.mpr htN, mem_product.mpr ⟨mem_univ _, hzpool⟩⟩, ?_⟩
  change {a * t + 1 - i.val, b * t + 1 - j.val, z} = {x, y, z}
  rw [hxf, hyf]

theorem source_mem_families {N L a b c d x y z t J : ℕ} {h : ℤ}
    (hN : 2 ≤ N) (ha : 0 < a)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hc : 0 < c) (hd : 0 < d) (hdH : d ≤ (L + 1) ^ J) (hh : |h| ≤ ((L + 1) ^ J : ℕ))
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : a * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) :
    {x, y, z} ∈ families N L a b J := by
  obtain ⟨p, hp, hpf⟩ := source_mem_pool hN ha hx hy hz hc hd hdH hh i j hbaseX hbaseY htarget hsize
  exact mem_image.mpr ⟨p, hp, hpf⟩

end PaperP1.AlignedTripleParameterPool
