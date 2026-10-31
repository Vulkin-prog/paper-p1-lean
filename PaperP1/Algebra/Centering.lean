module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Tactic.Ring.Basic

/-!
# The finite algebraic centering transform

The inclusion-exclusion formula used in the proof of manuscript label
`p1:alg:compatible` (article, Section 4) is meaningful for arbitrary coefficients
`q`, before constructing the random multiplicative model. Here `p` is a family
of proposed marginals and `q A` is a proposed joint moment.

This module proves only the empty, singleton and two-site algebraic formulas.
It does not identify these coefficients with expectations or prove the
manuscript's probability, Fourier or asymptotic statements. In particular,
no independence or equality of the marginals is assumed.
-/

@[expose] public section

open scoped BigOperators

namespace PaperP1.Algebra

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Finite centering with heterogeneous marginal parameters. -/
def centeredCoefficient (p : ι → R) (q : Finset ι → R) (I : Finset ι) : R :=
  ∑ A ∈ I.powerset, (-1 : R) ^ (I.card - A.card) * q A * ∏ x ∈ I \ A, p x

@[simp]
theorem centeredCoefficient_empty (p : ι → R) (q : Finset ι → R) :
    centeredCoefficient p q ∅ = q ∅ := by
  simp [centeredCoefficient]

theorem centeredCoefficient_singleton (p : ι → R) (q : Finset ι → R) (x : ι) :
    centeredCoefficient p q {x} = q {x} - q ∅ * p x := by
  have hpow : ({x} : Finset ι).powerset = {∅, {x}} := by
    ext A
    simp [Finset.subset_singleton_iff]
  simp [centeredCoefficient, hpow]
  ring1

/-- Actual normalized singleton moments give zero singleton coefficients. -/
theorem centeredCoefficient_singleton_eq_zero
    (p : ι → R) (q : Finset ι → R) (x : ι)
    (h_empty : q ∅ = 1) (h_singleton : q {x} = p x) :
    centeredCoefficient p q {x} = 0 := by
  rw [centeredCoefficient_singleton, h_empty, h_singleton]
  ring1

theorem centeredCoefficient_pair (p : ι → R) (q : Finset ι → R)
    {x y : ι} (hxy : x ≠ y) :
    centeredCoefficient p q {x, y} =
      q {x, y} - q {x} * p y - q {y} * p x + q ∅ * p x * p y := by
  have hpow : ({y} : Finset ι).powerset = {∅, {y}} := by
    ext A
    simp [Finset.subset_singleton_iff]
  rw [centeredCoefficient, Finset.sum_powerset_insert (by simpa using hxy)]
  simp [hpow, hxy, Finset.sdiff_singleton_eq_erase, Finset.sdiff_insert,
    Finset.erase_insert_of_ne]
  ring1

/-- Under the marginal identities, the two-site coefficient is the covariance. -/
theorem centeredCoefficient_pair_eq_covariance
    (p : ι → R) (q : Finset ι → R) {x y : ι} (hxy : x ≠ y)
    (h_empty : q ∅ = 1) (hx : q {x} = p x) (hy : q {y} = p y) :
    centeredCoefficient p q {x, y} = q {x, y} - p x * p y := by
  rw [centeredCoefficient_pair p q hxy, h_empty, hx, hy]
  ring1

end PaperP1.Algebra
