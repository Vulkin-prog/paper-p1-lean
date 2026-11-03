module

public import PaperP1.Algebra.HomogeneousMonomialCount
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Basic.Finite.Sigma

/-! # Reindexing an actual weighted homogeneous basis in a Veronese algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedVeronesePieceIndex

abbrev BaseIndex (D : ℕ) := Σ m : ℕ, {d : Fin 3 →₀ ℕ // d.degree = m * D}

abbrev PieceIndex {κ : Type*} (D : ℕ) (w : κ → ℕ) (n : ℕ) :=
  {i : BaseIndex D × κ // i.1.1 + w i.2 = n}

def pieceEquivAll {κ : Type*} (D : ℕ) (w : κ → ℕ) (n : ℕ) :
    PieceIndex D w n ≃
      Σ j : {j : κ // w j ≤ n}, {d : Fin 3 →₀ ℕ // d.degree = (n - w j.1) * D} where
  toFun i := ⟨⟨i.1.2, by have h := i.property; omega⟩, ⟨i.1.1.2.1, by
    have h := i.property
    have hm : i.1.1.1 = n - w i.1.2 := by omega
    simpa only [hm] using i.1.1.2.property⟩⟩
  invFun j := ⟨(⟨n - w j.1.1, j.2⟩, j.1.1), Nat.sub_add_cancel j.1.property⟩
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · apply Sigma.subtype_ext
      · dsimp
        have h := i.property
        omega
      · rfl
    · rfl
  right_inv j := Sigma.subtype_ext rfl rfl

theorem piece_finite_all {κ : Type*} [Finite κ] (D : ℕ) (w : κ → ℕ) (n : ℕ) :
    Finite (PieceIndex D w n) := by
  have (j : {j : κ // w j ≤ n}) :
      Finite {d : Fin 3 →₀ ℕ // d.degree = (n - w j.1) * D} :=
    HomogeneousMonomialCount.exponent_finite (Fin 3) _
  exact Finite.of_equiv
    (Σ j : {j : κ // w j ≤ n}, {d : Fin 3 →₀ ℕ // d.degree = (n - w j.1) * D})
    (pieceEquivAll D w n).symm

theorem piece_card_all {κ : Type*} [Fintype κ] (D : ℕ) (w : κ → ℕ) (n : ℕ) :
    Nat.card (PieceIndex D w n) =
      ∑ j : {j : κ // w j ≤ n}, ((n - w j.1) * D + 2).choose 2 := by
  classical
  have (j : {j : κ // w j ≤ n}) :
      Finite {d : Fin 3 →₀ ℕ // d.degree = (n - w j.1) * D} :=
    HomogeneousMonomialCount.exponent_finite (Fin 3) _
  rw [Nat.card_congr (pieceEquivAll D w n), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun _ _ ↦ HomogeneousMonomialCount.ternary_exponent_card _)

def pieceEquiv {κ : Type*} (D : ℕ) (w : κ → ℕ) (n : ℕ) (hw : ∀ j, w j ≤ n) :
    PieceIndex D w n ≃ Σ j : κ, {d : Fin 3 →₀ ℕ // d.degree = (n - w j) * D} where
  toFun i := ⟨i.1.2, ⟨i.1.1.2.1, by
    have h := i.property
    have hm : i.1.1.1 = n - w i.1.2 := by omega
    simpa only [hm] using i.1.1.2.property⟩⟩
  invFun j := ⟨(⟨n - w j.1, j.2⟩, j.1), Nat.sub_add_cancel (hw j.1)⟩
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · apply Sigma.subtype_ext
      · dsimp
        have h := i.property
        omega
      · rfl
    · rfl
  right_inv j := Sigma.subtype_ext rfl rfl

theorem piece_finite {κ : Type*} [Finite κ] (D : ℕ) (w : κ → ℕ) (n : ℕ)
    (hw : ∀ j, w j ≤ n) : Finite (PieceIndex D w n) := by
  have (j : κ) : Finite {d : Fin 3 →₀ ℕ // d.degree = (n - w j) * D} :=
    HomogeneousMonomialCount.exponent_finite (Fin 3) _
  exact Finite.of_equiv (Σ j : κ, {d : Fin 3 →₀ ℕ // d.degree = (n - w j) * D})
    (pieceEquiv D w n hw).symm

theorem piece_card {κ : Type*} [Fintype κ] (D : ℕ) (w : κ → ℕ) (n : ℕ)
    (hw : ∀ j, w j ≤ n) :
    Nat.card (PieceIndex D w n) = ∑ j : κ, ((n - w j) * D + 2).choose 2 := by
  have (j : κ) : Finite {d : Fin 3 →₀ ℕ // d.degree = (n - w j) * D} :=
    HomogeneousMonomialCount.exponent_finite (Fin 3) _
  rw [Nat.card_congr (pieceEquiv D w n hw), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun _ _ ↦ HomogeneousMonomialCount.ternary_exponent_card _)

end PaperP1.WeightedVeronesePieceIndex
