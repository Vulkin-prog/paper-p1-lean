module

public import PaperP1.Arithmetic.ScaledTargetValues
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Geometry of the true combined source/target value set for bounded affine data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TargetUnionGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.ScaledTargetValues PaperP1.NormalizedPairGeometry PaperP1.TwoProgressionPrimeRows

def anchor (b c x L : ℕ) (i : Fin (L + 1)) : ℕ := c * (b * startCompleteVertexLabel x L i)

def radius (a b H L : ℕ) : ℕ := 4 * (a * b * (H * (L + 1)))

def base (a b c H x L : ℕ) (i : Fin (L + 1)) : ℕ := anchor b c x L i - radius a b H L

theorem old_radius {a b c H L : ℕ} (hc : c ≤ 2 * a * H) : c * (b * L) ≤ radius a b H L := by
  have hmul := Nat.mul_le_mul_right (b * L) hc
  have hL := Nat.mul_le_mul_left (a * b * H) (show L ≤ L + 1 by omega)
  unfold radius
  nlinarith only [hmul, hL]

theorem new_radius {a b d H L : ℕ} (hd : d ≤ H) :
    a * b * H + a * b * d * (L + 1) ≤ radius a b H L := by
  have hmul := Nat.mul_le_mul_left (a * b * (L + 1)) hd
  have hL := Nat.mul_le_mul_left (a * b * H) (show 1 ≤ L + 1 by omega)
  have hnonneg : 0 ≤ a * b * H * (L + 1) := Nat.zero_le _
  unfold radius
  nlinarith only [hmul, hL, hnonneg]

theorem all_abs_bound {a b c d H x y z L t : ℕ} (hab : a ≤ b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hcH : c ≤ 2 * a * H) (hdH : d ≤ H)
    (i j : Fin (L + 1)) (h : ℤ) (hh : |h| ≤ H)
    (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (n : ℕ) (hn : n ∈ allValues a b c d x y z L) :
    |(n : ℤ) - (anchor b c x L i : ℕ)| ≤ (radius a b H L : ℕ) := by
  have hunit : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j := by
    rw [hbaseX, hbaseY]
    ring
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    have hbounds := union_bounds hab hx hy i j hunit m hm
    have hloN : b * startCompleteVertexLabel x L i ≤ m + b * L := by omega
    have hloZ : ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) ≤ (m : ℤ) + ((b * L : ℕ) : ℤ) := by
      exact_mod_cast hloN
    have hhiZ : (m : ℤ) ≤ ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) + ((b * L : ℕ) : ℤ) := by
      exact_mod_cast hbounds.2
    have habs : |(m : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ)| ≤ ((b * L : ℕ) : ℤ) :=
      abs_le.mpr ⟨by linarith only [hloZ], by linarith only [hhiZ]⟩
    have heq : ((c * m : ℕ) : ℤ) - (anchor b c x L i : ℕ) =
        (c : ℤ) * ((m : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ)) := by
      dsimp [anchor]
      ring
    rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) c)]
    have hmul := mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg (α := ℤ) c)
    have hr : ((c * (b * L) : ℕ) : ℤ) ≤ (radius a b H L : ℕ) := by exact_mod_cast old_radius hcH
    exact hmul.trans (by simpa only [Nat.cast_mul] using hr)
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
    obtain ⟨k, rfl⟩ := mem_values.mp hv
    have hbaseXZ : (startCompleteVertexLabel x L i : ℤ) = (a : ℤ) * t := by exact_mod_cast hbaseX
    have heq : ((a * b * d * startCompleteVertexLabel z L k : ℕ) : ℤ) - (anchor b c x L i : ℕ) =
        (a : ℤ) * b * h + (a : ℤ) * b * d * NormalizedUnitCount.offset k := by
      dsimp [anchor]
      rw [hbaseXZ, NormalizedUnitCount.label_cast hz]
      have hmul := congrArg (fun w : ℤ ↦ (a : ℤ) * b * w) htarget
      nlinarith only [hmul]
    rw [heq]
    calc
      _ ≤ |(a : ℤ) * b * h| + |(a : ℤ) * b * d * NormalizedUnitCount.offset k| := abs_add_le _ _
      _ = (a : ℤ) * b * |h| + (a : ℤ) * b * d * |NormalizedUnitCount.offset k| := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) a),
          abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b), abs_of_nonneg (Nat.cast_nonneg (α := ℤ) d)]
      _ ≤ (a : ℤ) * b * H + (a : ℤ) * b * d * ((L + 1 : ℕ) : ℤ) :=
        add_le_add (mul_le_mul_of_nonneg_left hh (by positivity))
          (mul_le_mul_of_nonneg_left (EnlargedPairGeometry.offset_abs k) (by positivity))
      _ ≤ (radius a b H L : ℕ) := by exact_mod_cast new_radius (a := a) (b := b) (L := L) hdH

theorem interval_bounds {a b c d H x y z L t : ℕ} (hab : a ≤ b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hcH : c ≤ 2 * a * H) (hdH : d ≤ H)
    (i j : Fin (L + 1)) (h : ℤ) (hh : |h| ≤ H)
    (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) (hrad : radius a b H L ≤ anchor b c x L i)
    (n : ℕ) (hn : n ∈ allValues a b c d x y z L) :
    base a b c H x L i ≤ n ∧ n ≤ base a b c H x L i + 2 * radius a b H L := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (all_abs_bound hab hx hy hz hcH hdH i j h hh hbaseX hbaseY htarget n hn)
  have hloN : anchor b c x L i ≤ n + radius a b H L := by
    have h : ((anchor b c x L i : ℕ) : ℤ) ≤ (n : ℤ) + radius a b H L := by linarith only [hlo]
    exact_mod_cast h
  have hhiN : n ≤ anchor b c x L i + radius a b H L := by
    have h : (n : ℤ) ≤ ((anchor b c x L i : ℕ) : ℤ) + radius a b H L := by linarith only [hhi]
    exact_mod_cast h
  have hcancel := Nat.sub_add_cancel hrad
  unfold base
  omega

theorem base_geometry {N a b c H x L : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hxN : N ≤ x) (hlarge : 8 * radius a b H L + 8 ≤ N) (i : Fin (L + 1)) :
    radius a b H L ≤ anchor b c x L i ∧ N ≤ 2 * base a b c H x L i ∧
      4 * radius a b H L ≤ base a b c H x L i := by
  have hx : 0 < x := by omega
  have hlabel : N - 1 ≤ startCompleteVertexLabel x L i := by
    have hmem := mem_Ico.mp ((values_eq_interval hx).symm ▸ (mem_values.mpr ⟨i, rfl⟩))
    omega
  have hbmul : startCompleteVertexLabel x L i ≤ b * startCompleteVertexLabel x L i := by
    simpa only [one_mul] using Nat.mul_le_mul_right (startCompleteVertexLabel x L i) (show 1 ≤ b by omega)
  have hcmul : b * startCompleteVertexLabel x L i ≤ anchor b c x L i := by
    simpa only [anchor, one_mul] using Nat.mul_le_mul_right (b * startCompleteVertexLabel x L i) (show 1 ≤ c by omega)
  have hNA := hlabel.trans (hbmul.trans hcmul)
  unfold base
  omega

theorem two_progressions {a b c d x y z L : ℕ} (hab : a ≤ b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (i j : Fin (L + 1))
    (hunit : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j)
    (hanchor : b * L ≤ b * startCompleteVertexLabel x L i) :
    allValues a b c d x y z L ⊆
      progression c (b * startCompleteVertexLabel x L i - b * L) (2 * b * L) ∪
        progression (a * b * d) (z - 1) L := by
  intro n hn
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    have hbounds := union_bounds hab hx hy i j hunit m hm
    apply mem_union.mpr
    apply Or.inl
    apply mem_image.mpr
    refine ⟨m, mem_Icc.mpr ⟨hbounds.1, ?_⟩, rfl⟩
    have hcancel := Nat.sub_add_cancel hanchor
    have heq : b * startCompleteVertexLabel x L i + b * L =
        (b * startCompleteVertexLabel x L i - b * L) + 2 * b * L := by nlinarith only [hcancel]
    rw [← heq]
    exact hbounds.2
  · apply mem_union.mpr
    apply Or.inr
    rwa [newValues, normalized_progression hz] at hn

theorem radius_polynomial {a b H L J : ℕ} (hH : H ≤ (L + 1) ^ J) :
    radius a b H L ≤ 4 * a * b * (L + 1) ^ (J + 1) := by
  have hmul := Nat.mul_le_mul_right (L + 1) hH
  rw [← pow_succ] at hmul
  have hscale := Nat.mul_le_mul_left (4 * a * b) hmul
  unfold radius
  nlinarith only [hscale]

theorem coefficient_product {a b c d H B J : ℕ} (hcH : c ≤ 2 * a * H)
    (hdH : d ≤ H) (hH : H ≤ B ^ J) (hB : 2 * a * a * b ≤ B) :
    c * (a * b * d) ≤ B ^ (2 * J + 1) := by
  have hc : c ≤ 2 * a * B ^ J := hcH.trans (Nat.mul_le_mul_left (2 * a) hH)
  have hd : d ≤ B ^ J := hdH.trans hH
  calc
    _ ≤ (2 * a * B ^ J) * (a * b * B ^ J) := Nat.mul_le_mul hc (Nat.mul_le_mul_left (a * b) hd)
    _ = (2 * a * a * b) * (B ^ J * B ^ J) := by ring
    _ = (2 * a * a * b) * B ^ (2 * J) := by rw [← pow_add]; congr 2; omega
    _ ≤ B * B ^ (2 * J) := Nat.mul_le_mul_right _ hB
    _ = B ^ (2 * J + 1) := by rw [pow_succ]; ring

theorem logarithmic_width {a b H L J : ℕ} (ha : 0 < a) (hb : 0 < b) (hHpos : 0 < H)
    (hH : H ≤ (L + 1) ^ J) (hB : 512 * a * b ≤ L + 1) :
    Real.log (64 * ((2 * radius a b H L : ℕ) : ℝ)) ≤
      ((J + 2 : ℕ) : ℝ) * Real.log ((L + 1 : ℕ) : ℝ) := by
  have hr := Nat.mul_le_mul_left 128 (radius_polynomial hH (a := a) (b := b))
  have hmul := Nat.mul_le_mul_right ((L + 1) ^ (J + 1)) hB
  have hpow : (L + 1) * (L + 1) ^ (J + 1) = (L + 1) ^ (J + 2) := by
    rw [pow_succ ((L + 1) : ℕ) (J + 1)]
    ring
  have hbound : 64 * (2 * radius a b H L) ≤ (L + 1) ^ (J + 2) := by
    nlinarith only [hr, hmul, hpow]
  have hradpos : 0 < radius a b H L := by unfold radius; positivity
  have hlog := Real.log_le_log (by positivity : 0 < 64 * ((2 * radius a b H L : ℕ) : ℝ))
    (by exact_mod_cast hbound : 64 * ((2 * radius a b H L : ℕ) : ℝ) ≤ (((L + 1 : ℕ) : ℝ) ^ (J + 2)))
  simpa only [Real.log_pow] using hlog

theorem source_primes_subset {a b c d H : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a * b).primeFactors ⊆ exceptionalPrimes H c (a * b * d) := by
  intro p hp
  apply mem_union.mpr
  apply Or.inr
  apply Nat.mem_primeFactors.mpr
  refine ⟨Nat.prime_of_mem_primeFactors hp, ?_, (Nat.mul_pos hc (Nat.mul_pos (Nat.mul_pos ha hb) hd)).ne'⟩
  exact (Nat.dvd_of_mem_primeFactors hp).trans ⟨c * d, by ring⟩

end PaperP1.TargetUnionGeometry
