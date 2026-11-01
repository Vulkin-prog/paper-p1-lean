module

public import PaperP1.Affine.StartCharacterSpace
public import PaperP1.Affine.Characters

/-! # The affine character of an even true-window selection is its predecessor coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StartVertexSign

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

local instance startVertexSignPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem vertex_bit {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L)
    (hstart : startSystem M x L ω = startRhs L) (v : Fin (L + 1)) :
    valueBit ω (startCompleteVertexLabel x L v) = valueBit ω x + if v = 0 then 1 else 0 := by
  by_cases hv : v = 0
  · subst v
    have hrow : valueBit ω (x - 1) + valueBit ω x = 1 := by
      simpa using congrFun hstart (⟨0, hL⟩ : Fin L)
    have hself : valueBit ω x + valueBit ω x = 0 := (add_eq_zero_iff_eq _ _).mpr rfl
    have hsum := congrArg (fun z : F₂ ↦ z + valueBit ω x) hrow
    have hpred : valueBit ω (x - 1) = 1 + valueBit ω x := by
      simpa only [add_assoc, hself, add_zero] using hsum
    change valueBit ω (x - 1) = valueBit ω x + if (0 : Fin (L + 1)) = 0 then 1 else 0
    rw [ite_eq_left rfl]
    exact hpred.trans (add_comm _ _)
  · have hv0 : v.val ≠ 0 := fun h ↦ hv (Fin.ext h)
    rw [startCompleteVertexLabel, ite_eq_right hv0, ite_eq_right hv, add_zero]
    by_cases hv1 : v.val = 1
    · simp only [hv1, Nat.sub_self, Nat.add_zero]
    · have hi : v.val - 1 < L := by have := v.isLt; omega
      have hne : v.val - 1 ≠ 0 := by omega
      have hrow := congrFun hstart (⟨v.val - 1, hi⟩ : Fin L)
      simp only [startSystem_apply, startRhs_apply, ite_eq_right hne] at hrow
      exact ((add_eq_zero_iff_eq _ _).mp hrow).symm

theorem zero_sum_shift {ι : Type*} [Fintype ι] (w f : ι → F₂) (c : F₂) (hw : ∑ i, w i = 0) :
    (∑ i, w i * (c + f i)) = ∑ i, w i * f i := by
  simp_rw [mul_add]
  rw [sum_add_distrib, ← sum_mul, hw, zero_mul, zero_add]

theorem even_parity_evaluation {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L)
    (hstart : startSystem M x L ω = startRhs L) (w : Fin (L + 1) → F₂) (hw : ∑ v, w v = 0) :
    parityPairing M (vertexParityMap x L w) ω = w 0 := by
  rw [parityPairing_vertexParityMap]
  simp_rw [vertex_bit ω hL hstart]
  rw [zero_sum_shift w (fun v ↦ if v = 0 then 1 else 0) (valueBit ω x) hw]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]

theorem even_real_character {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L)
    (hstart : startSystem M x L ω = startRhs L) (w : Fin (L + 1) → F₂) (hw : ∑ v, w v = 0) :
    realCharacter (parityPairing M (vertexParityMap x L w)) ω = (binarySign (w 0) : ℝ) := by
  rw [realCharacter, even_parity_evaluation ω hL hstart w hw]

end PaperP1.StartVertexSign
