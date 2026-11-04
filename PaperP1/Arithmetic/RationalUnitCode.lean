module

public import PaperP1.Algebra.FiberEvenCode
public import PaperP1.Arithmetic.ExactUnitGeometric
public import PaperP1.Arithmetic.SmallExactUnitAlignment
public import PaperP1.Arithmetic.BoundedHeightChannelUniqueness

/-! # The global rational even-unit code from all actual window ratios

The code is defined before selecting a slope. Each rational-ratio fiber
has even parity. A distant aligned pair has at most one repeated fiber,
so its dimension is the exact unit count minus one, including zero units.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalUnitCode

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.EnlargedPairGeometry

local instance rationalUnitCodePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def ratio (x y L : ℕ) (u : Fin (L + 1) × Fin (L + 1)) : ℚ :=
  (startCompleteVertexLabel x L u.1 : ℚ) / (startCompleteVertexLabel y L u.2 : ℚ)

def code (x y L : ℕ) : Submodule F₂ ((Fin (L + 1) × Fin (L + 1)) → F₂) :=
  PaperP1.FiberEvenCode.code (ratio x y L)

def nullity (x y L : ℕ) : ℕ := Module.finrank F₂ (code x y L)

def weight (x y L : ℕ) : ℝ := (2 ^ nullity x y L : ℝ) - 1

theorem label_positive {x L : ℕ} (hx : 2 ≤ x) (i : Fin (L + 1)) : 0 < startCompleteVertexLabel x L i := by
  rw [startCompleteVertexLabel_eq_offset (by omega : 0 < x)]
  omega

theorem ratio_eq_iff {x y L : ℕ} (hy : 2 ≤ y) (u v : Fin (L + 1) × Fin (L + 1)) :
    ratio x y L u = ratio x y L v ↔
      startCompleteVertexLabel x L u.1 * startCompleteVertexLabel y L v.2 =
        startCompleteVertexLabel x L v.1 * startCompleteVertexLabel y L u.2 := by
  have hu : (startCompleteVertexLabel y L u.2 : ℚ) ≠ 0 := by exact_mod_cast (label_positive hy u.2).ne'
  have hv : (startCompleteVertexLabel y L v.2 : ℚ) ≠ 0 := by exact_mod_cast (label_positive hy v.2).ne'
  rw [ratio, ratio, div_eq_div_iff hu hv]
  exact_mod_cast (Iff.rfl :
    startCompleteVertexLabel x L u.1 * startCompleteVertexLabel y L v.2 =
      startCompleteVertexLabel x L v.1 * startCompleteVertexLabel y L u.2 ↔ _)

theorem fiber_eq_units {a b x y L : ℕ} (hb : 0 < b) (hy : 2 ≤ y) :
    PaperP1.FiberEvenCode.fiber (ratio x y L) ((a : ℚ) / b) = units a b x y L := by
  ext u
  simp only [PaperP1.FiberEvenCode.fiber, mem_filter, mem_univ, true_and, mem_units]
  have hu : (startCompleteVertexLabel y L u.2 : ℚ) ≠ 0 := by exact_mod_cast (label_positive hy u.2).ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [ratio, div_eq_div_iff hu hbQ]
  constructor
  · intro h
    have hh : startCompleteVertexLabel x L u.1 * b = a * startCompleteVertexLabel y L u.2 := by exact_mod_cast h
    simpa only [mul_comm b] using hh
  · intro h
    have hh : startCompleteVertexLabel x L u.1 * b = a * startCompleteVertexLabel y L u.2 := by
      simpa only [mul_comm b] using h
    exact_mod_cast hh

theorem single_repeated_fiber {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hL : 0 < L) (hx : L + 1 < x) (hy : L + 1 < y)
    (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3)
    (hlarge : 4 * (L + 1) ^ 7 < y) (hg : Geometric a b x y L) :
    ∀ u, ratio x y L u ≠ (a : ℚ) / b → ∀ v, ratio x y L v = ratio x y L u → v = u := by
  intro u hur v hvu
  by_contra hne
  have hy2 : 2 ≤ y := by omega
  have hcross := (ratio_eq_iff hy2 u v).mp hvu.symm
  obtain ⟨c, d, hc, hd, hcd, hcB, hdB, hu, _hv⟩ := PaperP1.SmallExactUnitAlignment.two_units x y L hx hy
    u.1 v.1 u.2 v.2 (Ne.symm hne) hcross
  have hheight : 2 * (L + 1) ≤ (L + 1) ^ 3 := by
    have hB : 2 ≤ L + 1 := by omega
    have hh := Nat.mul_le_mul_right (L + 1) hB
    have hsq : L + 1 ≤ (L + 1) ^ 2 := le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 2 ≠ 0)
    have hm := Nat.mul_le_mul_left (L + 1) hsq
    nlinarith only [hh, hm]
  have hgeom := PaperP1.ExactUnitGeometric.of_unit (by omega : 0 < x) (by omega : 0 < y) hu
  have hlarge' : 4 * ((L + 1) ^ 3) ^ 2 * (L + 1) < y := by
    have he : 4 * ((L + 1) ^ 3) ^ 2 * (L + 1) = 4 * (L + 1) ^ 7 := by ring
    rw [he]
    exact hlarge
  obtain ⟨hac, hbd⟩ := PaperP1.BoundedHeightChannelUniqueness.unique ha hab hcd haB hbB
    (hcB.trans hheight) (hdB.trans hheight) hlarge' hg hgeom
  subst c
  subst d
  have hmem : u ∈ PaperP1.FiberEvenCode.fiber (ratio x y L) ((a : ℚ) / b) := by
    rw [fiber_eq_units hb hy2]
    exact hu
  exact hur (PaperP1.FiberEvenCode.mem_fiber.mp hmem)

theorem nullity_eq_units {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hL : 0 < L) (hx : L + 1 < x) (hy : L + 1 < y)
    (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3)
    (hlarge : 4 * (L + 1) ^ 7 < y) (hg : Geometric a b x y L) :
    nullity x y L = (units a b x y L).card - 1 := by
  unfold nullity code
  rw [PaperP1.FiberEvenCode.finrank_eq_fiber ((a : ℚ) / b)
    (single_repeated_fiber ha hb hab hL hx hy haB hbB hlarge hg), fiber_eq_units hb (by omega : 2 ≤ y)]

theorem weight_nonneg (x y L : ℕ) : 0 ≤ weight x y L :=
  sub_nonneg.mpr (one_le_pow₀ (by norm_num))

end PaperP1.RationalUnitCode
