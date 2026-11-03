module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Sym.NatCard

/-! # Counting literal homogeneous monomials by symmetric powers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousMonomialCount

def exponentEquivSym (σ : Type*) (n : ℕ) : {d : σ →₀ ℕ // d.degree = n} ≃ Sym σ n := by
  classical
  exact
    { toFun := fun d ↦ ⟨Finsupp.toMultiset d.1, (Finsupp.card_toMultiset d.1).trans d.property⟩
      invFun := fun m ↦ ⟨Multiset.toFinsupp m.1, by
        calc
          (Multiset.toFinsupp m.1).degree =
              (Finsupp.toMultiset (Multiset.toFinsupp m.1)).card :=
            (Finsupp.card_toMultiset _).symm
          _ = n := by simpa only [Multiset.toFinsupp_toMultiset] using m.property⟩
      left_inv := fun d ↦ Subtype.ext (Multiset.toFinsupp.apply_symm_apply d.1)
      right_inv := fun m ↦ Subtype.ext (Multiset.toFinsupp.symm_apply_apply m.1) }

theorem exponent_finite (σ : Type*) [Finite σ] (n : ℕ) :
    Finite {d : σ →₀ ℕ // d.degree = n} :=
  Finite.of_equiv (Sym σ n) (exponentEquivSym σ n).symm

theorem exponent_card (σ : Type*) (n : ℕ) :
    Nat.card {d : σ →₀ ℕ // d.degree = n} = (Nat.card σ + n - 1).choose n := by
  rw [Nat.card_congr (exponentEquivSym σ n), Sym.natCard_sym_eq_choose]

theorem ternary_exponent_card (n : ℕ) :
    Nat.card {d : Fin 3 →₀ ℕ // d.degree = n} = (n + 2).choose 2 := by
  rw [exponent_card]
  simp only [Nat.card_fin]
  have h : 3 + n - 1 = n + 2 := by omega
  rw [h, ← Nat.choose_symm (show n ≤ n + 2 by omega)]
  congr 1
  omega

end PaperP1.HomogeneousMonomialCount
