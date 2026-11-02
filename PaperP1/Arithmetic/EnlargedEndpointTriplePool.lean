module

public import PaperP1.Arithmetic.EnlargedAlignedTriplePool
public import PaperP1.Arithmetic.EndpointAlignedTriplePool

/-! # Endpoint parameters for enlarged sources still have only polynomially many literal codes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedEndpointTriplePool

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.EnlargedSourceTargetGeometry

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def radius (a b L J : ℕ) : ℕ := sourceScale a b * (L + 1) + 2 * (L + 1) ^ J

def pool (N L a b J : ℕ) : Finset (EnlargedAlignedTriplePool.Code L) :=
  EnlargedAlignedTriplePool.poolFor (EndpointAlignedTriplePool.parameters N a b (radius a b L J)) L a b J

def families (N L a b J : ℕ) : Finset (Finset ℕ) :=
  (pool N L a b J).image (EnlargedAlignedTriplePool.family a b)

theorem radius_budget (a b L J : ℕ) :
    4 * radius a b L J + 2 ≤ (4 * sourceScale a b + 10) * (L + 1) ^ (J + 1) := by
  have hB : L + 1 ≤ (L + 1) ^ (J + 1) := le_self_pow (by omega) (by omega)
  have hH : (L + 1) ^ J ≤ (L + 1) ^ (J + 1) := by
    rw [pow_succ]
    simpa only [mul_one] using Nat.mul_le_mul_left ((L + 1) ^ J) (show 1 ≤ L + 1 by omega)
  have hDB := Nat.mul_le_mul_left (sourceScale a b) hB
  unfold radius
  nlinarith only [hB, hH, hDB]

theorem pool_card {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N L J : ℕ) :
    (pool N L a b J).card ≤
      6 * a * (2 * sourceScale a b + 1) * (4 * sourceScale a b + 10) * (L + 1) ^ (4 * J + 3) := by
  have hpower : (L + 1) ^ (J + 1) * (L + 1) ^ (3 * J + 2) = (L + 1) ^ (4 * J + 3) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ (EndpointAlignedTriplePool.parameters N a b (radius a b L J)).card *
        (6 * a * (2 * sourceScale a b + 1) * (L + 1) ^ (3 * J + 2)) :=
      EnlargedAlignedTriplePool.poolFor_card _ L a b J
    _ ≤ (4 * radius a b L J + 2) *
        (6 * a * (2 * sourceScale a b + 1) * (L + 1) ^ (3 * J + 2)) :=
      Nat.mul_le_mul_right _ (EndpointAlignedTriplePool.parameters_card ha hb)
    _ ≤ ((4 * sourceScale a b + 10) * (L + 1) ^ (J + 1)) *
        (6 * a * (2 * sourceScale a b + 1) * (L + 1) ^ (3 * J + 2)) :=
      Nat.mul_le_mul_right _ (radius_budget a b L J)
    _ = 6 * a * (2 * sourceScale a b + 1) * (4 * sourceScale a b + 10) *
        ((L + 1) ^ (J + 1) * (L + 1) ^ (3 * J + 2)) := by ring
    _ = _ := by rw [hpower]

theorem families_card {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N L J : ℕ) :
    (families N L a b J).card ≤
      6 * a * (2 * sourceScale a b + 1) * (4 * sourceScale a b + 10) * (L + 1) ^ (4 * J + 3) :=
  card_image_le.trans (pool_card ha hb N L J)

theorem source_mem_families {N L a b c d x y z t J : ℕ} {h : ℤ}
    (hN : 0 < N) (ha : 0 < a) (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hc : 0 < c) (hd : 0 < d) (hdH : d ≤ (L + 1) ^ J) (hh : |h| ≤ ((L + 1) ^ J : ℕ))
    (hgeom : EnlargedPairGeometry.Geometric a b x y L)
    (i : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hnear : EndpointAlignedTriplePool.Near N a b (radius a b L J) t)
    (hsize : (a * sourceScale a b) * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) :
    {x, y, z} ∈ families N L a b J := by
  have htN := EnlargedAlignedTriplePool.source_parameter_lt ha hx i hbaseX (show L + 1 < N by omega)
  have htmem : t ∈ EndpointAlignedTriplePool.parameters N a b (radius a b L J) :=
    mem_filter.mpr ⟨mem_range.mpr htN, hnear⟩
  obtain ⟨p, hp, _hpt, hpf⟩ := EnlargedAlignedTriplePool.source_mem_poolFor htmem hN ha hx hy hz hc hd hdH hh
    hgeom i hbaseX htarget hsize
  exact mem_image.mpr ⟨p, hp, hpf⟩

end PaperP1.EnlargedEndpointTriplePool
