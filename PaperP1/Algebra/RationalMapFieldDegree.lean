module

public import PaperP1.Algebra.RationalInterpolationUniqueness
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! # The actual rational-function subfield degree of a reduced polynomial quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalMapFieldDegree

open Polynomial

variable {F : Type*} [Field F]

def quotient (p q : F[X]) : RatFunc F :=
  algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q

theorem reduced_degrees (p q : F[X]) (hq : q ≠ 0) (hcop : IsCoprime p q) :
    max (quotient p q).num.natDegree (quotient p q).denom.natDegree = max p.natDegree q.natDegree := by
  let f := quotient p q
  have hn : f.num.natDegree ≤ p.natDegree := by
    by_cases hp : p = 0
    · simp only [f, quotient, hp, map_zero, zero_div, RatFunc.num_zero, natDegree_zero, le_refl]
    · exact natDegree_le_of_dvd (RatFunc.num_div_dvd p hq) hp
  have hd : f.denom.natDegree ≤ q.natDegree := natDegree_le_of_dvd (RatFunc.denom_div_dvd p q) hq
  have hcross : p * f.denom = f.num * q := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl |>.symm
  obtain ⟨δ, hnum, hden⟩ := RationalInterpolationUniqueness.common_factor_constant
    (max p.natDegree q.natDegree) p q f.num f.denom hq hcop rfl
    (hn.trans (le_max_left _ _)) (hd.trans (le_max_right _ _)) hcross
  have hδ : δ ≠ 0 := by
    intro hz
    exact f.denom_ne_zero (hden.trans (by rw [hz, C_0, zero_mul]))
  change max f.num.natDegree f.denom.natDegree = _
  rw [hnum, hden, natDegree_C_mul hδ, natDegree_C_mul hδ]

theorem extension_rank (p q : F[X]) (hq : q ≠ 0) (hcop : IsCoprime p q) :
    Module.finrank (IntermediateField.adjoin F {quotient p q}) (RatFunc F) = max p.natDegree q.natDegree :=
  (RatFunc.finrank_eq_max_natDegree (quotient p q)).trans (reduced_degrees p q hq hcop)

end PaperP1.RationalMapFieldDegree
