module

public import PaperP1.Arithmetic.DyadicTargetCount
public import PaperP1.Arithmetic.EnlargedSourceTargetGeometry
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # A literal target pool over enlarged sources, including sources with no exact unit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedAlignedTriplePool

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.EnlargedSourceTargetGeometry

abbrev Code (L : ℕ) := Σ _t : ℕ, (Fin (L + 1) × ℤ) × ℕ

def displacements (a b L : ℕ) : Finset ℤ :=
  Icc (-((sourceScale a b * (L + 1) : ℕ) : ℤ)) ((sourceScale a b * (L + 1) : ℕ) : ℤ)

def poolFor (parameters : Finset ℕ) (L a b J : ℕ) : Finset (Code L) :=
  parameters.sigma fun t ↦ ((univ : Finset (Fin (L + 1))) ×ˢ displacements a b L) ×ˢ
    DyadicTargetCount.pool a ((L + 1) ^ J) t

def pool (N L a b J : ℕ) : Finset (Code L) := poolFor (range (3 * N)) L a b J

def family (a b : ℕ) {L : ℕ} (p : Code L) : Finset ℕ :=
  {a * p.1 + 1 - p.2.1.1.val, ((b : ℤ) * p.1 + p.2.1.2).toNat, p.2.2}

def families (N L a b J : ℕ) : Finset (Finset ℕ) := (pool N L a b J).image (family a b)

theorem displacements_card (a b L : ℕ) :
    (displacements a b L).card = 2 * sourceScale a b * (L + 1) + 1 := by
  have h := DyadicEndpointPairs.integer_interval_card 0 (sourceScale a b * (L + 1))
  simpa only [displacements, Nat.cast_zero, zero_sub, zero_add, Nat.mul_assoc] using h

theorem poolFor_card (parameters : Finset ℕ) (L a b J : ℕ) :
    (poolFor parameters L a b J).card ≤
      parameters.card * (6 * a * (2 * sourceScale a b + 1) * (L + 1) ^ (3 * J + 2)) := by
  have hH : 1 ≤ (L + 1) ^ J := Nat.one_le_pow _ _ (by omega)
  have hdisp : (displacements a b L).card ≤ (2 * sourceScale a b + 1) * (L + 1) := by
    rw [displacements_card]
    nlinarith only [show 1 ≤ L + 1 by omega]
  calc
    _ = ∑ t ∈ parameters, ((L + 1) * (displacements a b L).card) *
        (DyadicTargetCount.pool a ((L + 1) ^ J) t).card := by
      rw [poolFor, card_sigma]
      apply sum_congr rfl
      intro t _
      rw [card_product, card_product, card_univ, Fintype.card_fin]
    _ ≤ ∑ _t ∈ parameters, ((L + 1) * ((2 * sourceScale a b + 1) * (L + 1))) *
        (6 * a * (L + 1) ^ (3 * J)) := by
      apply sum_le_sum
      intro t _
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hdisp) (DyadicTargetCount.pool_card_polynomial hH le_rfl)
    _ = parameters.card * (((L + 1) * ((2 * sourceScale a b + 1) * (L + 1))) *
        (6 * a * (L + 1) ^ (3 * J))) := by simp only [sum_const, Nat.nsmul_eq_mul]
    _ = _ := by rw [pow_add, pow_two]; ring

theorem pool_card (N L a b J : ℕ) :
    (pool N L a b J).card ≤ 18 * a * (2 * sourceScale a b + 1) * N * (L + 1) ^ (3 * J + 2) := by
  have h := poolFor_card (range (3 * N)) L a b J
  rw [card_range] at h
  unfold pool
  nlinarith only [h]

theorem families_card (N L a b J : ℕ) :
    (families N L a b J).card ≤ 18 * a * (2 * sourceScale a b + 1) * N * (L + 1) ^ (3 * J + 2) :=
  card_image_le.trans (pool_card N L a b J)

theorem source_parameter_lt {N L a x t : ℕ} (ha : 0 < a) (hx : x ∈ dyadicBlock N)
    (i : Fin (L + 1)) (hbase : startCompleteVertexLabel x L i = a * t) (hLN : L + 1 < N) : t < 3 * N := by
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hlabel := mem_Ico.mp ((NormalizedWindowSets.values_eq_interval hxpos).symm ▸
    (NormalizedWindowSets.mem_values.mpr ⟨i, rfl⟩))
  have hmul : t ≤ a * t := by simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ a by omega)
  have hxy := mem_Ico.mp hx
  omega

theorem source_mem_poolFor {N L a b c d x y z t J : ℕ} {h : ℤ} {parameters : Finset ℕ}
    (htmem : t ∈ parameters) (hN : 0 < N) (ha : 0 < a)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hc : 0 < c) (hd : 0 < d) (hdH : d ≤ (L + 1) ^ J) (hh : |h| ≤ ((L + 1) ^ J : ℕ))
    (hgeom : EnlargedPairGeometry.Geometric a b x y L)
    (i : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : (a * sourceScale a b) * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) :
    ∃ p ∈ poolFor parameters L a b J, p.1 = t ∧ family a b p = {x, y, z} := by
  have hxpos : 0 < x := hN.trans_le (mem_Ico.mp hx).1
  have hcH := numerator_bound hN ha hx hy hz hgeom i hbaseX hdH hh htarget hsize
  have hzpool := DyadicTargetCount.mem_pool hc hd hcH hdH hh htarget
  let v : ℤ := (y : ℤ) - (b : ℤ) * t
  have hv : v ∈ displacements a b L := by
    apply mem_Icc.mpr
    have hh := virtual_y_bound ha hxpos hgeom i hbaseX
    rw [abs_sub_comm] at hh
    simpa only [v, Nat.cast_mul] using abs_le.mp hh
  have hxf : a * t + 1 - i.val = x := by
    rw [startCompleteVertexLabel_eq_offset hxpos] at hbaseX
    omega
  have hyf : ((b : ℤ) * t + v).toNat = y := by simp only [v, add_sub_cancel, Int.toNat_natCast]
  refine ⟨⟨t, ((i, v), z)⟩,
    mem_sigma.mpr ⟨htmem, mem_product.mpr ⟨mem_product.mpr ⟨mem_univ _, hv⟩, hzpool⟩⟩, rfl, ?_⟩
  change {a * t + 1 - i.val, ((b : ℤ) * t + v).toNat, z} = {x, y, z}
  rw [hxf, hyf]

theorem source_mem_families {N L a b c d x y z t J : ℕ} {h : ℤ}
    (hN : 0 < N) (ha : 0 < a)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hc : 0 < c) (hd : 0 < d) (hdH : d ≤ (L + 1) ^ J) (hh : |h| ≤ ((L + 1) ^ J : ℕ))
    (hgeom : EnlargedPairGeometry.Geometric a b x y L)
    (i : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : (a * sourceScale a b) * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) :
    {x, y, z} ∈ families N L a b J := by
  have htN := source_parameter_lt ha hx i hbaseX (show L + 1 < N by omega)
  obtain ⟨p, hp, _hpt, hpf⟩ := source_mem_poolFor (mem_range.mpr htN) hN ha hx hy hz hc hd hdH hh
    hgeom i hbaseX htarget hsize
  exact mem_image.mpr ⟨p, hp, hpf⟩

end PaperP1.EnlargedAlignedTriplePool
