module

public import PaperP1.Algebra.HyperellipticWeightedMonomials
public import Mathlib.Data.Fintype.Sum

/-! # Exact finite indices, dimensions and distinct product weights for quadratic polynomial functions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticMonomialIndex

open HyperellipticWeightedMonomials

abbrev Index (d L : ℕ) := Fin (L / 2 + 1) ⊕ Fin (if d ≤ L then (L - d) / 2 + 1 else 0)

def embed (d L : ℕ) : Index d L → ℕ ⊕ ℕ := Sum.map Fin.val Fin.val

theorem embed_injective (d L : ℕ) : Function.Injective (embed d L) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (Fin.ext (Sum.inl.inj hij))
  · change Sum.inl (i : ℕ) = Sum.inr (j : ℕ) at hij
    exact False.elim (Sum.inl_ne_inr hij)
  · change Sum.inr (i : ℕ) = Sum.inl (j : ℕ) at hij
    exact False.elim (Sum.inr_ne_inl hij)
  · exact congrArg Sum.inr (Fin.ext (Sum.inr.inj hij))

theorem weight_le (d L : ℕ) (i : Index d L) : weight d (embed d L i) ≤ L := by
  rcases i with i | j
  · change 2 * (i : ℕ) ≤ L
    have hi := i.isLt
    omega
  · change d + 2 * (j : ℕ) ≤ L
    by_cases hd : d ≤ L
    · have hj : (j : ℕ) < (L - d) / 2 + 1 := by simpa only [ite_eq_left hd] using j.isLt
      omega
    · have hj : (j : ℕ) < 0 := by simpa only [ite_eq_right hd] using j.isLt
      omega

theorem weight_injective (d L : ℕ) (hodd : Odd d) :
    Function.Injective (fun i : Index d L ↦ weight d (embed d L i)) :=
  (HyperellipticWeightedMonomials.weight_injective d hodd).comp (embed_injective d L)

theorem cardinality (d L : ℕ) : Fintype.card (Index d L) =
    (L / 2 + 1) + (if d ≤ L then (L - d) / 2 + 1 else 0) := by
  simp only [Index, Fintype.card_sum, Fintype.card_fin]

theorem cardinality_odd (g L : ℕ) (hL : 2 * g + 1 ≤ L) :
    Fintype.card (Index (2 * g + 1) L) = L + 1 - g := by
  rw [cardinality, ite_eq_left hL]
  omega

theorem exists_index (d L : ℕ) (i : ℕ ⊕ ℕ) (hi : weight d i ≤ L) :
    ∃ j : Index d L, embed d L j = i := by
  rcases i with i | i
  · have hbound : i < L / 2 + 1 := by change 2 * i ≤ L at hi; omega
    exact ⟨Sum.inl ⟨i, hbound⟩, rfl⟩
  · have hsmall : d ≤ L := by change d + 2 * i ≤ L at hi; omega
    have hbound : i < (if d ≤ L then (L - d) / 2 + 1 else 0) := by
      rw [ite_eq_left hsmall]
      change d + 2 * i ≤ L at hi
      omega
    exact ⟨Sum.inr ⟨i, hbound⟩, rfl⟩

theorem product_weight_injective (d A B p : ℕ) (hodd : Odd d) (hA : A < p) :
    Function.Injective (fun ij : Index d A × Index d B ↦
      weight d (embed d A ij.1) + p * weight d (embed d B ij.2)) := by
  intro i j he
  change weight d (embed d A i.1) + p * weight d (embed d B i.2) =
    weight d (embed d A j.1) + p * weight d (embed d B j.2) at he
  have hi := weight_le d A i.1
  have hj := weight_le d A j.1
  have hm : weight d (embed d A i.1) % p = weight d (embed d A j.1) % p := by
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
      using congrArg (fun n : ℕ ↦ n % p) he
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hi hA), Nat.mod_eq_of_lt (lt_of_le_of_lt hj hA)] at hm
  have hfst := weight_injective d A hodd hm
  have hrest : p * weight d (embed d B i.2) = p * weight d (embed d B j.2) := by
    rw [hfst] at he
    exact Nat.add_left_cancel he
  have hp : p ≠ 0 := by omega
  have hsnd := weight_injective d B hodd (mul_left_cancel₀ hp hrest)
  exact Prod.ext hfst hsnd

end PaperP1.HyperellipticMonomialIndex
