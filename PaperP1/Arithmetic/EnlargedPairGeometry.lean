module

public import PaperP1.Arithmetic.NormalizedPairGeometry

/-! # The manuscript's enlarged alignment, including pairs with no exact unit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedPairGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

def Geometric (a b x y L : ℕ) : Prop :=
  |(b : ℤ) * x - (a : ℤ) * y| ≤ ((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ)

def radius (b L : ℕ) : ℕ := 3 * (b * (L + 1))

def base (b x L : ℕ) : ℕ := b * x - radius b L

theorem geometric_swap (a b x y L : ℕ) : Geometric a b x y L ↔ Geometric b a y x L := by
  unfold Geometric
  rw [abs_sub_comm, Nat.add_comm a b]

theorem union_swap (a b x y L : ℕ) :
    NormalizedWindowSets.union a b x y L = NormalizedWindowSets.union b a y x L := by
  exact Finset.union_comm _ _

theorem offset_abs {L : ℕ} (i : Fin (L + 1)) : |offset i| ≤ ((L + 1 : ℕ) : ℤ) := by
  unfold offset
  have hi := i.isLt
  apply abs_le.mpr
  omega

theorem union_abs_bound {a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hgeom : Geometric a b x y L) (n : ℕ) (hn : n ∈ NormalizedWindowSets.union a b x y L) :
    |(n : ℤ) - ((b * x : ℕ) : ℤ)| ≤ (radius b L : ℕ) := by
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
    obtain ⟨i, rfl⟩ := mem_values.mp hv
    have heq : ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) - ((b * x : ℕ) : ℤ) = (b : ℤ) * offset i := by
      push_cast
      rw [label_cast hx]
      ring
    rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b)]
    have hbound := mul_le_mul_of_nonneg_left (offset_abs i) (Nat.cast_nonneg (α := ℤ) b)
    push_cast at hbound
    dsimp [radius]
    nlinarith only [hbound, mul_nonneg (Nat.cast_nonneg (α := ℤ) b) (Nat.cast_nonneg (α := ℤ) (L + 1))]
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
    obtain ⟨j, rfl⟩ := mem_values.mp hv
    have heq : ((a * startCompleteVertexLabel y L j : ℕ) : ℤ) - ((b * x : ℕ) : ℤ) =
        -((b : ℤ) * x - (a : ℤ) * y) + (a : ℤ) * offset j := by
      push_cast
      rw [label_cast hy]
      ring
    rw [heq]
    calc
      _ ≤ |-((b : ℤ) * x - (a : ℤ) * y)| + |(a : ℤ) * offset j| := abs_add_le _ _
      _ = |(b : ℤ) * x - (a : ℤ) * y| + (a : ℤ) * |offset j| := by
        rw [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) a)]
      _ ≤ ((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) + (a : ℤ) * ((L + 1 : ℕ) : ℤ) :=
        add_le_add hgeom (mul_le_mul_of_nonneg_left (offset_abs j) (Nat.cast_nonneg (α := ℤ) a))
      _ ≤ (radius b L : ℕ) := by
        have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
        have hmul := mul_le_mul_of_nonneg_right habZ (Nat.cast_nonneg (α := ℤ) (L + 1))
        dsimp [radius]
        push_cast at hmul
        nlinarith only [hmul]

theorem interval_bounds {a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hgeom : Geometric a b x y L) (hbase : radius b L ≤ b * x)
    (n : ℕ) (hn : n ∈ NormalizedWindowSets.union a b x y L) :
    base b x L ≤ n ∧ n ≤ base b x L + 2 * radius b L := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (union_abs_bound hab hx hy hgeom n hn)
  have hloN : b * x ≤ n + radius b L := by
    have h : ((b * x : ℕ) : ℤ) ≤ (n : ℤ) + radius b L := by linarith only [hlo]
    exact_mod_cast h
  have hhiN : n ≤ b * x + radius b L := by
    have h : (n : ℤ) ≤ ((b * x : ℕ) : ℤ) + radius b L := by linarith only [hhi]
    exact_mod_cast h
  have hcancel := Nat.sub_add_cancel hbase
  unfold base
  omega

theorem base_geometry {N b x L : ℕ} (hb : 0 < b) (hxN : N ≤ x) (hlarge : 8 * radius b L + 8 ≤ N) :
    radius b L ≤ b * x ∧ N ≤ 2 * base b x L ∧ 4 * radius b L ≤ base b x L := by
  have hxA : x ≤ b * x := by simpa only [one_mul] using Nat.mul_le_mul_right x (show 1 ≤ b by omega)
  have hNA := hxN.trans hxA
  unfold base
  omega

theorem radius_height {b L : ℕ} (hheight : b ≤ (L + 1) ^ 3) : radius b L ≤ 3 * (L + 1) ^ 4 := by
  have h := Nat.mul_le_mul_right (L + 1) hheight
  have heq : (L + 1) ^ 3 * (L + 1) = (L + 1) ^ 4 := by ring
  unfold radius
  nlinarith only [h, heq]

theorem logarithmic_width {b L : ℕ} (hB : 2 ≤ L + 1) (hb : 0 < b) (hheight : b ≤ (L + 1) ^ 3) :
    Real.log (64 * ((2 * radius b L : ℕ) : ℝ)) ≤ 13 * Real.log ((L + 1 : ℕ) : ℝ) := by
  have hwidth := Nat.mul_le_mul_left 128 (radius_height hheight)
  have hpow : 384 ≤ (L + 1) ^ 9 := by
    have h := Nat.pow_le_pow_left hB 9
    norm_num at h
    omega
  have hmul := Nat.mul_le_mul_right ((L + 1) ^ 4) hpow
  have heq : (L + 1) ^ 9 * (L + 1) ^ 4 = (L + 1) ^ 13 := by rw [← pow_add]
  have hbound : 64 * (2 * radius b L) ≤ (L + 1) ^ 13 := by nlinarith only [hwidth, hmul, heq]
  have hRpos : 0 < radius b L := by unfold radius; positivity
  have hlog := Real.log_le_log (by positivity : 0 < 64 * ((2 * radius b L : ℕ) : ℝ))
    (by exact_mod_cast hbound : 64 * ((2 * radius b L : ℕ) : ℝ) ≤ (((L + 1 : ℕ) : ℝ) ^ 13))
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

end PaperP1.EnlargedPairGeometry
