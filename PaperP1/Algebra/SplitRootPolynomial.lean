module

public import Mathlib.FieldTheory.Separable

/-! # Squarefree products of nonzero scalar multiples of distinct linear factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRootPolynomial

open Finset Polynomial

variable {V K : Type*} [Field K]

def factor (r a : V → K) (v : V) : K[X] := C (a v) * (X - C (r v))

def polynomial (r a : V → K) (S : Finset V) : K[X] := ∏ v ∈ S, factor r a v

theorem polynomial_factor (r a : V → K) (S : Finset V) :
    polynomial r a S = C (∏ v ∈ S, a v) * ∏ v ∈ S, (X - C (r v)) := by
  unfold polynomial factor
  rw [prod_mul_distrib, ← map_prod]

theorem polynomial_squarefree (r a : V → K) (S : Finset V)
    (ha : ∀ v ∈ S, a v ≠ 0) (hinj : Set.InjOn r (S : Set V)) :
    Squarefree (polynomial r a S) := by
  have hmonic : Squarefree (∏ v ∈ S, (X - C (r v))) :=
    (Polynomial.separable_prod_X_sub_C_iff'.mpr (fun v hv w hw h ↦ hinj hv hw h)).squarefree
  have hunit : IsUnit (C (∏ v ∈ S, a v) : K[X]) :=
    Polynomial.isUnit_C.mpr (Ne.isUnit (prod_ne_zero_iff.mpr ha))
  rw [polynomial_factor]
  intro p hp
  exact hmonic p (hunit.dvd_mul_left.mp hp)

theorem isRoot_iff (r a : V → K) (S : Finset V) (ha : ∀ v ∈ S, a v ≠ 0) (t : K) :
    Polynomial.IsRoot (polynomial r a S) t ↔ ∃ v ∈ S, r v = t := by
  classical
  change eval t (polynomial r a S) = 0 ↔ _
  simp only [polynomial, Polynomial.eval_prod, factor, eval_mul, eval_C, eval_sub, eval_X,
    prod_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hzero⟩
    have hsub : t - r v = 0 := (mul_eq_zero.mp hzero).resolve_left (ha v hv)
    exact ⟨v, hv, (sub_eq_zero.mp hsub).symm⟩
  · rintro ⟨v, hv, hroot⟩
    exact ⟨v, hv, by rw [hroot, sub_self, mul_zero]⟩

end PaperP1.SplitRootPolynomial
