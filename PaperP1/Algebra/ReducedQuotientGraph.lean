module

public import PaperP1.Algebra.RationalMapFieldDegree

/-! # Canonical reduction preserves actual graph points and cannot increase either degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedQuotientGraph

open Polynomial PaperP1.RationalMapFieldDegree

variable {F : Type*} [Field F]

theorem numerator_degree_le (p q : F[X]) (hq : q ≠ 0) : (quotient p q).num.natDegree ≤ p.natDegree := by
  by_cases hp : p = 0
  · simp only [quotient, hp, map_zero, zero_div, RatFunc.num_zero, natDegree_zero, le_refl]
  · exact natDegree_le_of_dvd (RatFunc.num_div_dvd p hq) hp

theorem denominator_degree_le (p q : F[X]) (hq : q ≠ 0) : (quotient p q).denom.natDegree ≤ q.natDegree :=
  natDegree_le_of_dvd (RatFunc.denom_div_dvd p q) hq

theorem degree_le (p q : F[X]) (hq : q ≠ 0) :
    max (quotient p q).num.natDegree (quotient p q).denom.natDegree ≤ max p.natDegree q.natDegree :=
  max_le_max (numerator_degree_le p q hq) (denominator_degree_le p q hq)

theorem point_equation (p q : F[X]) (hq : q ≠ 0) (x y : F) (hqeval : q.eval x ≠ 0)
    (hpoint : p.eval x = y * q.eval x) : (quotient p q).num.eval x = y * (quotient p q).denom.eval x := by
  let f := quotient p q
  have hcross : f.num * q = p * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl
  have h := congrArg (fun P : F[X] ↦ P.eval x) hcross
  simp only [eval_mul] at h
  apply mul_right_cancel₀ hqeval
  calc
    f.num.eval x * q.eval x = p.eval x * f.denom.eval x := h
    _ = (y * f.denom.eval x) * q.eval x := by rw [hpoint]; ring

end PaperP1.ReducedQuotientGraph
