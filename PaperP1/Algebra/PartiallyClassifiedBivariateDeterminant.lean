module

public import PaperP1.Algebra.ClassifiedBivariateDeterminant

/-! # Selected smooth classes give a determinant divisor while all other columns remain in the matrix -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PartiallyClassifiedBivariateDeterminant

open MvPolynomial Finset

variable {R ι χ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype χ] [DecidableEq χ]

theorem congruent_polynomial_dvd (p : R) (P : χ → ι → MvPolynomial (Fin 2) R)
    (b : ι → Option χ) (L : χ → ℕ) (x y : ι → R) (A : Matrix ι ι R)
    (hx : ∀ j c, b j = some c → p ∣ x j) (hy : ∀ j c, b j = some c → p ∣ y j)
    (hA : ∀ i j c, b j = some c →
      p ^ (∑ c, (L c * Fintype.card {j // b j = some c} - (L c + 2).choose 3)) ∣
        A i j - eval ![x j, y j] (P c i)) :
    p ^ (∑ c, (L c * Fintype.card {j // b j = some c} - (L c + 2).choose 3)) ∣ A.det := by
  classical
  let b' : ι → χ ⊕ ι := fun j ↦ (b j).elim (Sum.inr j) Sum.inl
  let L' : χ ⊕ ι → ℕ := Sum.elim L (fun _ ↦ 0)
  let P' : χ ⊕ ι → ι → MvPolynomial (Fin 2) R :=
    Sum.elim P (fun j i ↦ C (A i j))
  let x' : ι → R := fun j ↦ (b j).elim 0 (fun _ ↦ x j)
  let y' : ι → R := fun j ↦ (b j).elim 0 (fun _ ↦ y j)
  have he : (∑ c, (L' c * Fintype.card {j // b' j = c} - (L' c + 2).choose 3)) =
      ∑ c, (L c * Fintype.card {j // b j = some c} - (L c + 2).choose 3) := by
    rw [Fintype.sum_sum_type]
    have hz : (∑ j : ι, (L' (Sum.inr j) * Fintype.card {k // b' k = Sum.inr j} -
        (L' (Sum.inr j) + 2).choose 3)) = 0 := by simp [L']
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro c _
    have hc : Fintype.card {j // b' j = Sum.inl c} = Fintype.card {j // b j = some c} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro j
      cases hb : b j <;> simp [b', hb]
    change L c * _ - (L c + 2).choose 3 = _
    rw [hc]
  have hx' (j : ι) : p ∣ x' j := by
    cases hb : b j with
    | none => simp [x', hb]
    | some c => simpa only [x', hb, Option.elim_some] using hx j c hb
  have hy' (j : ι) : p ∣ y' j := by
    cases hb : b j with
    | none => simp [y', hb]
    | some c => simpa only [y', hb, Option.elim_some] using hy j c hb
  have hA' (i j : ι) :
      p ^ (∑ c, (L' c * Fintype.card {j // b' j = c} - (L' c + 2).choose 3)) ∣
        A i j - eval ![x' j, y' j] (P' (b' j) i) := by
    rw [he]
    cases hb : b j with
    | none => simp [P', b', hb]
    | some c => simpa only [P', b', hb, Option.elim_some, Sum.elim_inl, x', y'] using hA i j c hb
  rw [← he]
  exact ClassifiedBivariateDeterminant.congruent_polynomial_dvd p P' b' L' x' y' hx' hy' A hA'

end PaperP1.PartiallyClassifiedBivariateDeterminant
