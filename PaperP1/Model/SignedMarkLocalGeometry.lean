module

public import PaperP1.Model.SignedExactWords
public import Mathlib.Data.Fin.Embedding

/-! # Exact signed runs exclude interior starts and determine their unique type -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedMarkLocalGeometry

open PaperP1.Arithmetic PaperP1.Model PaperP1.SignedExactWords

theorem add_self (s : F₂) : s + s = 0 := by
  revert s
  decide

theorem ordered_gap {g : ℕ → F₂} {j k L e f : ℕ} {s t : F₂}
    (hjk : j < k) (ha : SignedExactMark g (j + 1) L e s)
    (hb : SignedExactMark g (k + 1) L f t) : j + (L + e) ≤ k := by
  by_contra h
  have hlow : g k = g (j + 1) := by
    have hh := ha.1.2 (k - j - 1) (by omega)
    have he : j + 1 + (k - j - 1) = k := by omega
    simpa only [he] using hh
  have hhigh : g (k + 1) = g (j + 1) := by
    have hh := ha.1.2 (k - j) (by omega)
    have he : j + 1 + (k - j) = k + 1 := by omega
    simpa only [he] using hh
  have hh := hb.1.1
  simp only [Nat.add_sub_cancel, hlow, hhigh, add_self] at hh
  exact zero_ne_one hh

theorem type_unique {g : ℕ → F₂} {x L e f : ℕ} {s t : F₂}
    (ha : SignedExactMark g x L e s) (hb : SignedExactMark g x L f t) :
    e = f ∧ s = t := by
  have hnot {e f : ℕ} {s t : F₂} (he : e < f)
      (ha : SignedExactMark g x L e s) (hb : SignedExactMark g x L f t) : False := by
    have hh := ha.2.1
    rw [hb.1.2 (L + e) (by omega), add_self] at hh
    exact zero_ne_one hh
  exact ⟨by rcases lt_trichotomy e f with h | h | h
            · exact False.elim (hnot h ha hb)
            · exact h
            · exact False.elim (hnot h hb ha), ha.2.2.symm.trans hb.2.2⟩

def trimmedPositions {j k S T B : ℕ} (hjk : j ≤ k) (hsep : j + S ≤ k + 2)
    (hnear : k < j + B) (hS : S ≤ B) (hT : T + 2 ≤ B) :
    Fin S ⊕ Fin T ↪ Fin (2 * B) where
  toFun := Sum.elim (fun i ↦ ⟨i.val, by have := i.isLt; omega⟩)
    (fun i ↦ ⟨k - j + 2 + i.val, by have := i.isLt; omega⟩)
  inj' := by
    intro u v he
    have hv := congrArg Fin.val he
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Fin.ext hv)
      | inr v => have := u.isLt; dsimp at hv; omega
    | inr u =>
      cases v with
      | inl v => have := v.isLt; dsimp at hv; omega
      | inr v => apply congrArg Sum.inr; apply Fin.ext; dsimp at hv; omega

theorem trimmed_value {j k S T B : ℕ} (hjk : j ≤ k) (hsep : j + S ≤ k + 2)
    (hnear : k < j + B) (hS : S ≤ B) (hT : T + 2 ≤ B) (i : Fin S ⊕ Fin T) :
    j + (trimmedPositions hjk hsep hnear hS hT i).val =
      Sum.elim (fun i : Fin S ↦ j + i.val) (fun i : Fin T ↦ k + 2 + i.val) i := by
  cases i with
  | inl i => rfl
  | inr i => dsimp [trimmedPositions]; omega

end PaperP1.SignedMarkLocalGeometry
