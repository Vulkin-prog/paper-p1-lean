/-
Copyright (c) 2026 the paper-p1-lean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
The ordered lexicographic construction uses the monomial-order and finite-support
APIs of Mathlib at 9d581dfff2e41de989072ea63abf3daf69311520.
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Monoid.Prod

/-! # A genuine monomial order comparing a selected natural weight before lexicographic order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedMonomialOrder

variable {σ : Type*} [LinearOrder σ]

def Syn (_w : σ → ℕ) := σ →₀ ℕ

instance synAddCommMonoid (w : σ → ℕ) : AddCommMonoid (Syn w) :=
  inferInstanceAs (AddCommMonoid (σ →₀ ℕ))

def key (w : σ → ℕ) (x : σ →₀ ℕ) : Lex (ℕ × Lex (σ →₀ ℕ)) :=
  toLex (Finsupp.weight w x, toLex x)

omit [LinearOrder σ] in
theorem key_add (w : σ → ℕ) (x y : σ →₀ ℕ) : key w (x + y) = key w x + key w y := by
  change toLex (Finsupp.weight w ((x : σ →₀ ℕ) + (y : σ →₀ ℕ)),
    toLex ((x : σ →₀ ℕ) + (y : σ →₀ ℕ))) =
      toLex (Finsupp.weight w x + Finsupp.weight w y, toLex x + toLex y)
  rw [(Finsupp.weight w).map_add x y, toLex_add]

instance synLinearOrder (w : σ → ℕ) : LinearOrder (Syn w) :=
  LinearOrder.lift' (key w) (by
    intro x y h
    exact congrArg (fun p : Lex (ℕ × Lex (σ →₀ ℕ)) ↦ ofLex (ofLex p).2) h)

instance synIsOrderedAddMonoid (w : σ → ℕ) : IsOrderedAddMonoid (Syn w) where
  add_le_add_left a b h c := by
    change key w a ≤ key w b at h
    change key w (a + c) ≤ key w (b + c)
    calc
      key w (a + c) = key w a + key w c := key_add w a c
      _ ≤ key w b + key w c := add_le_add h le_rfl
      _ = key w (b + c) := (key_add w b c).symm

instance synWellFoundedLT [WellFoundedGT σ] (w : σ → ℕ) : WellFoundedLT (Syn w) :=
  InvImage.wf (key w) wellFounded_lt

def order [WellFoundedGT σ] (w : σ → ℕ) : MonomialOrder σ where
  syn := Syn w
  toSyn := { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl }
  toSyn_monotone a b h := by
    change key w a ≤ key w b
    apply Prod.Lex.toLex_le_toLex'.mpr
    refine ⟨?_, fun _ ↦ Finsupp.toLex_monotone h⟩
    calc
      Finsupp.weight w a ≤ Finsupp.weight w a + Finsupp.weight w (b - a) := Nat.le_add_right _ _
      _ = Finsupp.weight w b := by rw [← map_add, add_tsub_cancel_of_le h]

theorem weight_le_of_le [WellFoundedGT σ] (w : σ → ℕ) (a b : σ →₀ ℕ)
    (h : (order w).toSyn a ≤ (order w).toSyn b) : Finsupp.weight w a ≤ Finsupp.weight w b := by
  change key w a ≤ key w b at h
  exact (Prod.Lex.toLex_le_toLex'.mp h).1

theorem lt_of_weight_lt [WellFoundedGT σ] (w : σ → ℕ) (a b : σ →₀ ℕ)
    (h : Finsupp.weight w a < Finsupp.weight w b) : (order w).toSyn a < (order w).toSyn b := by
  change key w a < key w b
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

theorem leading_weight_ge [WellFoundedGT σ] {R : Type*} [CommSemiring R]
    (w : σ → ℕ) (P : MvPolynomial σ R) (r : σ →₀ ℕ) (hr : r ∈ P.support) :
    Finsupp.weight w r ≤ Finsupp.weight w ((order w).degree P) :=
  weight_le_of_le w r _ ((order w).le_degree hr)

end PaperP1.WeightedMonomialOrder
