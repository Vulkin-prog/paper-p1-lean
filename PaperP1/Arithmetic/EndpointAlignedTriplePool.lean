module

public import PaperP1.Arithmetic.AlignedTripleParameterPool

/-! # Every endpoint source and bounded affine target has a polynomial-size literal parameter pool -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EndpointAlignedTriplePool

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def radius (L J : ℕ) : ℕ := (L + 1) + 2 * (L + 1) ^ J
def Near (N a b R t : ℕ) : Prop := |(a : ℤ) * t - N| ≤ R ∨ |(b : ℤ) * t - 2 * N| ≤ R
def parameters (N a b R : ℕ) : Finset ℕ := (range (3 * N)).filter (Near N a b R)
def pool (N L a b J : ℕ) : Finset (AlignedTripleParameterPool.Code L) :=
  (parameters N a b (radius L J)).sigma fun t ↦
    (univ : Finset (Fin (L + 1) × Fin (L + 1))) ×ˢ DyadicTargetCount.pool a ((L + 1) ^ J) t
def families (N L a b J : ℕ) : Finset (Finset ℕ) :=
  (pool N L a b J).image (AlignedTripleParameterPool.family a b)

theorem parameters_card {N a b R : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (parameters N a b R).card ≤ 4 * R + 2 := by
  have haI : Set.InjOn (fun t : ℕ ↦ 1 * (a * t)) (range (3 * N) : Set ℕ) := by
    intro t _ u _ hh
    apply mul_right_injective₀ ha.ne'
    simpa only [one_mul] using hh
  have hbI : Set.InjOn (fun t : ℕ ↦ 1 * (b * t)) (range (3 * N) : Set ℕ) := by
    intro t _ u _ hh
    apply mul_right_injective₀ hb.ne'
    simpa only [one_mul] using hh
  have hA := DyadicEndpointPairs.endpoint_filter_card (range (3 * N)) (fun t ↦ a * t) 1 N R haI
  have hB := DyadicEndpointPairs.endpoint_filter_card (range (3 * N)) (fun t ↦ b * t) 1 (2 * N) R hbI
  have heq : parameters N a b R =
      (range (3 * N)).filter (fun t ↦ |((a * t : ℕ) : ℤ) - N| ≤ R) ∪
      (range (3 * N)).filter (fun t ↦ |((b * t : ℕ) : ℤ) - 2 * N| ≤ R) := by
    ext t
    simp only [parameters, Near, mem_filter, mem_union, Nat.cast_mul]
    tauto
  rw [heq]
  have hU := card_union_le ((range (3 * N)).filter fun t ↦ |((a * t : ℕ) : ℤ) - N| ≤ R)
    ((range (3 * N)).filter fun t ↦ |((b * t : ℕ) : ℤ) - 2 * N| ≤ R)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, one_mul] at hA hB hU ⊢
  omega

theorem radius_budget (L J : ℕ) : 4 * radius L J + 2 ≤ 14 * (L + 1) ^ (J + 1) := by
  have hB : L + 1 ≤ (L + 1) ^ (J + 1) := le_self_pow (by omega) (by omega)
  have hH : (L + 1) ^ J ≤ (L + 1) ^ (J + 1) := by
    rw [pow_succ]
    simpa only [mul_one] using Nat.mul_le_mul_left ((L + 1) ^ J) (show 1 ≤ L + 1 by omega)
  unfold radius
  nlinarith only [hB, hH]

theorem pool_card {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N L J : ℕ) :
    (pool N L a b J).card ≤ 84 * a * (L + 1) ^ (4 * J + 3) := by
  have hH : 1 ≤ (L + 1) ^ J := Nat.one_le_pow _ _ (by omega)
  have hpower : (L + 1) ^ (J + 1) * (L + 1) ^ 2 * (L + 1) ^ (3 * J) = (L + 1) ^ (4 * J + 3) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = ∑ t ∈ parameters N a b (radius L J), (L + 1) ^ 2 * (DyadicTargetCount.pool a ((L + 1) ^ J) t).card := by
      rw [pool, card_sigma]
      apply sum_congr rfl
      intro t _
      rw [card_product, card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]
    _ ≤ ∑ _t ∈ parameters N a b (radius L J), (L + 1) ^ 2 * (6 * a * (L + 1) ^ (3 * J)) :=
      sum_le_sum (fun _ _ ↦ Nat.mul_le_mul_left _ (DyadicTargetCount.pool_card_polynomial hH le_rfl))
    _ = (parameters N a b (radius L J)).card * ((L + 1) ^ 2 * (6 * a * (L + 1) ^ (3 * J))) := by
      simp only [sum_const, Nat.nsmul_eq_mul]
    _ ≤ (4 * radius L J + 2) * ((L + 1) ^ 2 * (6 * a * (L + 1) ^ (3 * J))) :=
      Nat.mul_le_mul_right _ (parameters_card ha hb)
    _ ≤ (14 * (L + 1) ^ (J + 1)) * ((L + 1) ^ 2 * (6 * a * (L + 1) ^ (3 * J))) :=
      Nat.mul_le_mul_right _ (radius_budget L J)
    _ = 84 * a * ((L + 1) ^ (J + 1) * (L + 1) ^ 2 * (L + 1) ^ (3 * J)) := by ring
    _ = _ := by rw [hpower]

theorem families_card {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N L J : ℕ) :
    (families N L a b J).card ≤ 84 * a * (L + 1) ^ (4 * J + 3) := card_image_le.trans (pool_card ha hb N L J)

theorem source_mem_families {N L a b c d x y z t J : ℕ} {h : ℤ}
    (hN : 2 ≤ N) (ha : 0 < a) (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hc : 0 < c) (hd : 0 < d) (hdH : d ≤ (L + 1) ^ J) (hh : |h| ≤ ((L + 1) ^ J : ℕ))
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t) (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hnear : Near N a b (radius L J) t)
    (hsize : a * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) :
    {x, y, z} ∈ families N L a b J := by
  have hxpos : 0 < x := by have hh := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have hh := (mem_Ico.mp hy).1; omega
  have hzpool := DyadicTargetCount.actual_target_mem_pool (by omega : 0 < N)
    hx hy hz hc hd hdH hh i j hbaseX hbaseY htarget hsize
  have hsrc := (ActualDyadicInterior.source_parameter_bounds (by omega : 0 < N) hx i hbaseX).2
  have hsrcN : a * t ≤ 2 * N + (L + 1) := by exact_mod_cast hsrc
  have hmul : t ≤ a * t := by simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ a by omega)
  have htN : t < 3 * N := by omega
  have hp : (⟨t, ((i, j), z)⟩ : AlignedTripleParameterPool.Code L) ∈ pool N L a b J :=
    mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_range.mpr htN, hnear⟩, mem_product.mpr ⟨mem_univ _, hzpool⟩⟩
  have hxf : a * t + 1 - i.val = x := by rw [startCompleteVertexLabel_eq_offset hxpos] at hbaseX; omega
  have hyf : b * t + 1 - j.val = y := by rw [startCompleteVertexLabel_eq_offset hypos] at hbaseY; omega
  apply mem_image.mpr
  refine ⟨⟨t, ((i, j), z)⟩, hp, ?_⟩
  change {a * t + 1 - i.val, b * t + 1 - j.val, z} = {x, y, z}
  rw [hxf, hyf]

end PaperP1.EndpointAlignedTriplePool
