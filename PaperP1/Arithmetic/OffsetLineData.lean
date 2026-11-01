module

public import PaperP1.Algebra.IntegralLine
public import PaperP1.Arithmetic.TwoPointSquareClasses
public import PaperP1.Arithmetic.SaturationPrimes

/-! # Actual offset points and their primitive line direction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLineData

open Finset PaperP1.IntegralLine PaperP1.PrimitiveTripleDirection PaperP1.SaturationPrimes
  PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoPointSquareClasses

variable {P : Finset ℕ} {L : ℕ}

def point (u : P → Fin 3 → Fin (L + 1)) (p : P) (i : Fin 3) : ℤ := (u p i).val - 1

def values (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1)) (p : P) (i : Fin 3) : ℤ :=
  (X i : ℤ) + point u p i

def points (u : P → Fin 3 → Fin (L + 1)) : Finset (Fin 3 → ℤ) := univ.image (point u)

theorem values_eq_vertex (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (p : P) (i : Fin 3) (hx : 0 < X i) : values X u p i = (startCompleteVertexLabel (X i) L (u p i) : ℤ) := by
  rw [PaperP1.Arithmetic.startCompleteVertexLabel_eq_offset hx]
  unfold values point
  omega

theorem values_eq_natural (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (p : P) (i : Fin 3) (hx : 0 < X i) : values X u p i = (value (X i) (u p i) : ℤ) := by
  unfold values point value
  omega

theorem point_difference_bound (u : P → Fin 3 → Fin (L + 1)) (a b : P) (i : Fin 3) :
    (point u b i - point u a i).natAbs ≤ L + 1 := by
  have ha := (u a i).isLt
  have hb := (u b i).isLt
  have habs : |point u b i - point u a i| ≤ ((L + 1 : ℕ) : ℤ) := by
    apply abs_le.mpr
    unfold point
    omega
  rw [← Int.natCast_natAbs] at habs
  exact_mod_cast habs

theorem exists_direction (u : P → Fin 3 → Fin (L + 1)) (hcol : Collinear (point u))
    (hsize : 1 < (points u).card) :
    ∃ a b : P, point u a ≠ point u b ∧ ∃ d : Fin 3 → ℤ,
      Primitive d ∧ height d ≤ L + 1 ∧
        ∀ p : P, ∃ t : ℤ, ∀ i, point u p i = point u a i + t * d i := by
  obtain ⟨v, hv, w, hw, hvw⟩ := one_lt_card.mp hsize
  obtain ⟨a, _, rfl⟩ := mem_image.mp hv
  obtain ⟨b, _, rfl⟩ := mem_image.mp hw
  obtain ⟨d, hd, ⟨g, hg, hfactor⟩, hparam⟩ := exists_primitive_line (point u a) (point u b) hvw
  refine ⟨a, b, hvw, d, hd, ?_, ?_⟩
  · exact height_le_of_factor (fun i ↦ point u b i - point u a i) d g (L + 1) hg hfactor
      (point_difference_bound u a b)
  · exact fun p ↦ hparam (point u p) (hcol a b p)

theorem values_parametrize (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1)) (a p : P)
    (d : Fin 3 → ℤ) (t : ℤ) (ht : ∀ i, point u p i = point u a i + t * d i) :
    ∀ i, values X u p i = values X u a i + t * d i := by
  intro i
  unfold values
  rw [ht i]
  ring

theorem cross_constant (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1)) (a p : P)
    (d : Fin 3 → ℤ) (t : ℤ) (ht : ∀ i, point u p i = point u a i + t * d i) (i j : Fin 3) :
    d i * values X u p j - d j * values X u p i = d i * values X u a j - d j * values X u a i := by
  rw [values_parametrize X u a p d t ht i, values_parametrize X u a p d t ht j]
  ring

theorem exists_nonzero_cross (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (hx : ∀ i, 2 ≤ X i) (hinj : Function.Injective (PaperP1.Arithmetic.evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (PaperP1.Arithmetic.squareClassSpace (X 0) L)
      (PaperP1.Arithmetic.squareClassSpace (X 1) L))
    (a b : P) (hab : point u a ≠ point u b) (d : Fin 3 → ℤ) (hd : Primitive d)
    (hparam : ∀ p : P, ∃ t : ℤ, ∀ i, point u p i = point u a i + t * d i) :
    ∃ i j : Fin 3, d i * values X u a j - d j * values X u a i ≠ 0 := by
  by_contra hnot
  have hzero (i j : Fin 3) : d i * values X u a j = d j * values X u a i := by
    by_contra h
    exact hnot ⟨i, j, sub_ne_zero.mpr h⟩
  have hvpos (i : Fin 3) : 0 < values X u a i := by
    unfold values point
    have h := hx i
    omega
  have hd0 : d 0 ≠ 0 := by
    intro hz
    apply primitive_ne_zero d hd
    funext i
    have h := hzero i 0
    rw [hz, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (hvpos 0).ne'
  obtain ⟨t, ht⟩ := hparam b
  have ht0 : t ≠ 0 := by
    intro hz
    apply hab
    funext i
    have h := ht i
    rw [hz, zero_mul, add_zero] at h
    exact h.symm
  have hu : u a 0 ≠ u b 0 := by
    intro h
    have hpoint : point u b 0 = point u a 0 := by simp only [point, h]
    have hmul : t * d 0 = 0 := by linarith [ht 0]
    exact mul_ne_zero ht0 hd0 hmul
  have hcross : values X u a 0 * values X u b 1 = values X u b 0 * values X u a 1 := by
    rw [values_parametrize X u a b d t ht 0, values_parametrize X u a b d t ht 1]
    have h := congrArg (fun z : ℤ ↦ t * z) (hzero 0 1)
    nlinarith
  have hNat : startCompleteVertexLabel (X 0) L (u a 0) * startCompleteVertexLabel (X 1) L (u b 1) =
      startCompleteVertexLabel (X 0) L (u b 0) * startCompleteVertexLabel (X 1) L (u a 1) := by
    simp only [values_eq_vertex X u a 0 (by have h := hx 0; omega),
      values_eq_vertex X u a 1 (by have h := hx 1; omega),
      values_eq_vertex X u b 0 (by have h := hx 0; omega),
      values_eq_vertex X u b 1 (by have h := hx 1; omega)] at hcross
    exact_mod_cast hcross
  exact no_proportional_pairs (X 0) (X 1) L (hx 0) (hx 1) hinj hdirect
    (u a 0) (u b 0) (u a 1) (u b 1) hu hNat

end PaperP1.OffsetLineData
