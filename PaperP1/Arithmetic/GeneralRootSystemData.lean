module

public import PaperP1.Algebra.HomogeneousSplitRadicalData
public import Mathlib.Data.List.OfFn

/-! # The actual homogeneous radicand list of a general split-product integer system -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralRootSystemData

open PaperP1.HomogeneousSplitRadicalData

def radicands (k D : ℕ) (d : Fin k → ℤ) (I J : Fin k → Finset ℤ) : List (PolynomialRing ℚ) :=
  List.ofFn fun i ↦ radicand (d i : ℚ) (2 * D - ((I i).card + (J i).card)) (I i) (J i)

theorem length (k D : ℕ) (d : Fin k → ℤ) (I J : Fin k → Finset ℤ) : (radicands k D d I J).length = k :=
  List.length_ofFn

def indexEquiv (k D : ℕ) (d : Fin k → ℤ) (I J : Fin k → Finset ℤ) :
    Fin (radicands k D d I J).length ≃ Fin k := finCongr (length k D d I J)

theorem get (k D : ℕ) (d : Fin k → ℤ) (I J : Fin k → Finset ℤ)
    (i : Fin (radicands k D d I J).length) :
    (radicands k D d I J).get i = radicand (d (indexEquiv k D d I J i) : ℚ)
      (2 * D - ((I (indexEquiv k D d I J i)).card + (J (indexEquiv k D d I J i)).card))
      (I (indexEquiv k D d I J i)) (J (indexEquiv k D d I J i)) := by
  have hget := List.get_ofFn
    (fun t : Fin k ↦ radicand (d t : ℚ) (2 * D - ((I t).card + (J t).card)) (I t) (J t)) i
  have heq : Fin.cast (length k D d I J) i = indexEquiv k D d I J i := by
    apply Fin.ext
    rfl
  rw [← heq]
  exact hget

end PaperP1.GeneralRootSystemData
