module

public import PaperP1.Algebra.HomogeneousSplitRadicalData
public import Mathlib.Data.List.OfFn

/-! # The actual homogeneous radicand list constructed from an integer root system -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryRootSystemData

open PaperP1.HomogeneousSplitRadicalData

def radicands (k D : ℕ) (d : Fin k → ℤ) (I : Fin k → Finset ℤ) (j : Fin k → ℤ) :
    List (PolynomialRing ℚ) :=
  List.ofFn fun i ↦ radicand (d i : ℚ) (2 * D - ((I i).card + 1)) (I i) {j i}

theorem length (k D : ℕ) (d : Fin k → ℤ) (I : Fin k → Finset ℤ) (j : Fin k → ℤ) :
    (radicands k D d I j).length = k := List.length_ofFn

def indexEquiv (k D : ℕ) (d : Fin k → ℤ) (I : Fin k → Finset ℤ) (j : Fin k → ℤ) :
    Fin (radicands k D d I j).length ≃ Fin k := finCongr (length k D d I j)

theorem get (k D : ℕ) (d : Fin k → ℤ) (I : Fin k → Finset ℤ) (j : Fin k → ℤ)
    (i : Fin (radicands k D d I j).length) :
    (radicands k D d I j).get i =
      radicand (d (indexEquiv k D d I j i) : ℚ)
        (2 * D - ((I (indexEquiv k D d I j i)).card + ({j (indexEquiv k D d I j i)} : Finset ℤ).card))
        (I (indexEquiv k D d I j i)) {j (indexEquiv k D d I j i)} := by
  have hget := List.get_ofFn
    (fun t : Fin k ↦ radicand (d t : ℚ) (2 * D - ((I t).card + 1)) (I t) {j t}) i
  have heq : Fin.cast (length k D d I j) i = indexEquiv k D d I j i := by
    apply Fin.ext
    rfl
  simp only [Finset.card_singleton]
  rw [← heq]
  exact hget

end PaperP1.OrdinaryRootSystemData
