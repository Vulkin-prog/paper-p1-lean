module

public import PaperP1.Diophantine.PrimitiveHomogeneousZeros
public import PaperP1.Diophantine.BidegreeOneFibreCount
public import PaperP1.Diophantine.IntegerLinearFibres

/-! # The degree-zero-in-(u,v) auxiliary case with the actual lattice step -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ZeroDegreeLinearFibres

open Finset PaperP1.PrimitiveDirections PaperP1.BidegreeOneFibreCount

def coefficient₁ (c₁ : ℕ) (v : Pair) : ℕ := c₁ * (v 0).natAbs ^ 2
def coefficient₂ (c₂ : ℕ) (v : Pair) : ℕ := c₂ * (v 1).natAbs ^ 2

structure Valid (c₁ c₂ : ℕ) (h : ℤ) (s : Point) : Prop where
  first_pos : ∀ i, 0 < s.1 i
  second_pos : ∀ i, 0 < s.2 i
  primitive : (s.1 0).natAbs.Coprime (s.1 1).natAbs
  equation : (c₂ : ℤ) * s.1 1 ^ 2 * s.2 0 - (c₁ : ℤ) * s.1 0 ^ 2 * s.2 1 = h

def encode (s : Point) : ℤ × ℤ := (s.2 1, s.2 0)

theorem encode_injective_on_fibre (S : Finset Point) (t : Pair) :
    Set.InjOn encode (↑(S.filter fun s ↦ s.1 = t) : Set Point) := by
  intro x hx y hy hxy
  have hx1 := (mem_filter.mp hx).2
  have hy1 := (mem_filter.mp hy).2
  apply Prod.ext (hx1.trans hy1.symm)
  funext i
  fin_cases i
  · exact congrArg Prod.snd hxy
  · exact congrArg Prod.fst hxy

theorem linear_fibre_count (c₁ c₂ : ℕ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h : ℤ) (hh : h ≠ 0) (N C₀ C₁ : ℝ) (hN : 0 ≤ N) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (S : Finset Point) (hS : ∀ s ∈ S, Valid c₁ c₂ h s)
    (hheight : ∀ s ∈ S, (coefficient₁ c₁ s.1 : ℝ) * s.2 1 ≤ C₁ * N)
    (hproduct : ∀ s ∈ S, N ≤ C₀ * (coefficient₁ c₁ s.1 : ℝ) * coefficient₂ c₂ s.1)
    (t : Pair) (ht : t ∈ S.image Prod.fst) :
    ((S.filter fun s ↦ s.1 = t).card : ℝ) ≤ C₀ * C₁ * h.natAbs + 1 := by
  obtain ⟨s₀, hs₀, rfl⟩ := mem_image.mp ht
  have hv := hS s₀ hs₀
  let A := coefficient₁ c₁ s₀.1
  let B := coefficient₂ c₂ s₀.1
  have hA : 0 < A := Nat.mul_pos hc₁ (pow_pos (Int.natAbs_pos.mpr (hv.first_pos 0).ne') 2)
  have hB : 0 < B := Nat.mul_pos hc₂ (pow_pos (Int.natAbs_pos.mpr (hv.first_pos 1).ne') 2)
  have hAcast : (A : ℤ) = (c₁ : ℤ) * s₀.1 0 ^ 2 := by
    simp only [A, coefficient₁, Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs,
      abs_of_pos (hv.first_pos 0)]
  have hBcast : (B : ℤ) = (c₂ : ℤ) * s₀.1 1 ^ 2 := by
    simp only [B, coefficient₂, Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs,
      abs_of_pos (hv.first_pos 1)]
  classical
  have hcard := card_image_iff.mpr (encode_injective_on_fibre S s₀.1)
  rw [← hcard]
  apply PaperP1.IntegerLinearFibres.weighted_height_count A B hA hB h hh N C₀ C₁ hN hC₀ hC₁
    (hproduct s₀ hs₀)
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hz
    have hsf := (mem_filter.mp hs).1
    have hst := (mem_filter.mp hs).2
    unfold PaperP1.IntegerLinearFibres.Equation encode
    rw [hAcast, hBcast]
    have heq := (hS s hsf).equation
    rw [hst] at heq
    exact heq
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hz
    exact (hS s (mem_filter.mp hs).1).second_pos 1
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hz
    have hb := hheight s (mem_filter.mp hs).1
    rw [(mem_filter.mp hs).2] at hb
    exact hb

theorem auxiliary_zero_count (k : ℕ) (c₁ c₂ : ℕ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h : ℤ) (hh : h ≠ 0) (N C₀ C₁ : ℝ) (hN : 0 ≤ N) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (F : MvPolynomial (Fin 2) ℤ) (hF : F.IsHomogeneous k) (hF0 : F ≠ 0)
    (S : Finset Point) (hS : ∀ s ∈ S, Valid c₁ c₂ h s)
    (hzero : ∀ s ∈ S, MvPolynomial.eval s.1 F = 0)
    (hheight : ∀ s ∈ S, (coefficient₁ c₁ s.1 : ℝ) * s.2 1 ≤ C₁ * N)
    (hproduct : ∀ s ∈ S, N ≤ C₀ * (coefficient₁ c₁ s.1 : ℝ) * coefficient₂ c₂ s.1) :
    (S.card : ℝ) ≤ 2 * (k + 1) * (C₀ * C₁ * h.natAbs + 1) := by
  have hprojection : (S.image Prod.fst).card ≤ 2 * (k + 1) := by
    apply PaperP1.PrimitiveHomogeneousZeros.primitive_card F hF hF0
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      exact (hS s hs).primitive
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      exact hzero s hs
  calc
    (S.card : ℝ) = ∑ t ∈ S.image Prod.fst, ((S.filter fun s ↦ s.1 = t).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_image Prod.fst S
    _ ≤ ∑ _t ∈ S.image Prod.fst, (C₀ * C₁ * h.natAbs + 1) := by
      apply sum_le_sum
      intro t ht
      exact linear_fibre_count c₁ c₂ hc₁ hc₂ h hh N C₀ C₁ hN hC₀ hC₁ S hS hheight hproduct t ht
    _ = ((S.image Prod.fst).card : ℝ) * (C₀ * C₁ * h.natAbs + 1) := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hprojection

end PaperP1.ZeroDegreeLinearFibres
