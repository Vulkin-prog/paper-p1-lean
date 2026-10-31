module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.FieldTheory.Separable
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-
Adapted from PaperC/Algebra/RungeSplitProduct.lean, by Vulkin-prog, Apache-2.0.
Source commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 85ecd7bca6da10b0d0b319e08f1d20ba271a0886. Upstream lemma numbers refer to Paper C.
-/

@[expose] public section

/-!
# A split product with distinct roots is not a square

The first algebraic observation in Paper C, Lemma 3.1, is that

`∏ i, (T + γ i)`

cannot be the square of a polynomial when the shifts `γ i` are distinct and
the index type is nonempty.  We prove the more general field-valued statement
using separability.
-/

namespace PaperP1.RungeSplitProduct

open Polynomial
open scoped BigOperators

variable {F ι : Type*} [Field F] [Fintype ι]

/-- The monic polynomial with the displayed roots. -/
noncomputable def splitProduct (root : ι → F) : F[X] :=
  ∏ i, (X - C (root i))

@[simp]
theorem natDegree_splitProduct (root : ι → F) :
    (splitProduct root).natDegree = Fintype.card ι := by
  classical
  simp [splitProduct]

theorem splitProduct_separable_iff (root : ι → F) :
    (splitProduct root).Separable ↔ Function.Injective root := by
  classical
  simpa [splitProduct] using
    (Polynomial.separable_prod_X_sub_C_iff (F := F) (f := root))

/--
A nonempty product of distinct linear factors is not a polynomial square.
The paper applies this with `root i = -γ i` over `ℚ`.
-/
theorem splitProduct_not_isSquare
    [Nonempty ι] (root : ι → F) (hinjective : Function.Injective root) :
    ¬ ∃ q : F[X], splitProduct root = q ^ 2 := by
  classical
  rintro ⟨q, hq⟩
  have hseparable : (splitProduct root).Separable :=
    (splitProduct_separable_iff root).2 hinjective
  have hqNotUnit : ¬ IsUnit q := by
    intro hqUnit
    have hpUnit : IsUnit (splitProduct root) := by
      rw [hq]
      exact hqUnit.pow 2
    have hdegreeZero := Polynomial.natDegree_eq_zero_of_isUnit hpUnit
    rw [natDegree_splitProduct] at hdegreeZero
    have hcardPositive : 0 < Fintype.card ι := Fintype.card_pos
    omega
  have hpowSeparable : (q ^ 2).Separable := by
    rw [← hq]
    exact hseparable
  have hpower :=
    Polynomial.Separable.of_pow
      (f := q) hqNotUnit (n := 2) (by norm_num) hpowSeparable
  norm_num at hpower

end PaperP1.RungeSplitProduct

