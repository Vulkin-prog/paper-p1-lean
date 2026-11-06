module

public import PaperP1.Arithmetic.SplitProductInversion
public import PaperP1.Arithmetic.HyperellipticOddDegreeCharacterEstimate

/-! # Uniform relative cancellation for every nonempty split product of bounded degree

The even-degree case uses the actual inversion bijection and its exact missing
point correction. No cancellation premise is assumed in either parity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitProductCharacterEstimate

open Polynomial Finset SplitProductInversion
open scoped Classical

theorem uniform_absolute (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ S : Finset (ZMod p), S.Nonempty → S.card ≤ D →
        |((∑ x : ZMod p, quadraticChar (ZMod p) ((linearProduct S).eval x) : ℤ) : ℝ)| ≤ η * p := by
  have hhalf : 0 < η / 2 := by positivity
  obtain ⟨K, hK⟩ := PaperP1.HyperellipticOddDegreeCharacterEstimate.uniform_absolute D (η/2) hhalf
  obtain ⟨L, hL⟩ := exists_nat_ge (2 / η)
  refine ⟨max K L, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro S hS hD
  have hdec : (fun a b : ZMod p ↦ Classical.propDecidable (a = b)) = ZMod.decidableEq p :=
    Subsingleton.elim _ _
  have hLp : (L : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show L ≤ p by omega)
  have herror : 1 ≤ (η / 2) * (p : ℝ) := by
    have ht := (div_le_iff₀ hη).mp (hL.trans hLp)
    nlinarith only [ht]
  by_cases ho : Odd S.card
  · have hb := hK p hp (by omega) (linearProduct S)
      (by rw [linear_degree]; exact ho) (by rw [linear_degree]; exact hD)
    exact hb.trans (by nlinarith only [mul_nonneg (le_of_lt hη) (Nat.cast_nonneg p)])
  · have heven : Even S.card := Nat.not_odd_iff_even.mp ho
    obtain ⟨a, ha⟩ := hS
    have hpos : 0 < S.card := card_pos.mpr ⟨a, ha⟩
    have hodd : Odd (invertedProduct S a).natDegree := by
      rw [inverted_degree S a ha]
      obtain ⟨k, hk⟩ := heven
      exact ⟨k-1, by omega⟩
    have hdegree : (invertedProduct S a).natDegree ≤ D := by
      rw [inverted_degree S a ha]
      omega
    have hb := hK p hp (by omega) (invertedProduct S a) hodd hdegree
    have he := character_sum_inversion S a ha heven
    rw [hdec] at he
    have heR : ((∑ x : ZMod p, quadraticChar (ZMod p) ((linearProduct S).eval x) : ℤ) : ℝ) =
        ((∑ t : ZMod p, quadraticChar (ZMod p) ((invertedProduct S a).eval t) : ℤ) : ℝ) - 1 := by
      exact_mod_cast he
    rw [heR]
    calc
      _ ≤ |((∑ t : ZMod p, quadraticChar (ZMod p) ((invertedProduct S a).eval t) : ℤ) : ℝ)| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ (η/2) * p + 1 := by rw [abs_one]; linarith only [hb]
      _ ≤ η * p := by nlinarith only [herror]

end PaperP1.SplitProductCharacterEstimate
