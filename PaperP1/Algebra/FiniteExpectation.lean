module

public import PaperP1.Algebra.Centering
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Weighted finite expectations and the centered product expansion

All weights and all centered variables may be dependent. The algebraic identity
does not require equal marginals, positivity, or normalization. A probability
interpretation will impose positivity and total weight one separately.
-/

@[expose] public section

open scoped BigOperators

namespace PaperP1.Algebra

variable {Ω ι R A : Type*} [Fintype Ω]

section Semiring
variable [CommSemiring R]

/-- Weighted finite expectation; normalization is an explicit premise when needed. -/
def finiteExpectation (w : Ω → R) (X : Ω → R) : R := ∑ ω, w ω * X ω

theorem finiteExpectation_const (w : Ω → R) (c : R) :
    finiteExpectation w (fun _ => c) = (∑ ω, w ω) * c := by
  simp [finiteExpectation, Finset.sum_mul]

theorem finiteExpectation_add (w : Ω → R) (X Y : Ω → R) :
    finiteExpectation w (fun ω => X ω + Y ω) =
      finiteExpectation w X + finiteExpectation w Y := by
  simp [finiteExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteExpectation_mul_const (w : Ω → R) (X : Ω → R) (c : R) :
    finiteExpectation w (fun ω => X ω * c) = finiteExpectation w X * c := by
  simp [finiteExpectation, Finset.sum_mul, mul_assoc]

theorem finiteExpectation_const_mul (w : Ω → R) (c : R) (X : Ω → R) :
    finiteExpectation w (fun ω => c * X ω) = c * finiteExpectation w X := by
  simp only [mul_comm c, finiteExpectation_mul_const]

theorem finiteExpectation_sum {κ : Type*} (w : Ω → R) (s : Finset κ)
    (X : κ → Ω → R) :
    finiteExpectation w (fun ω => ∑ i ∈ s, X i ω) =
      ∑ i ∈ s, finiteExpectation w (X i) := by
  simp only [finiteExpectation, Finset.mul_sum]
  exact Finset.sum_comm

end Semiring

section Ring
variable [CommRing R]

theorem finiteExpectation_sub (w : Ω → R) (X Y : Ω → R) :
    finiteExpectation w (fun ω => X ω - Y ω) =
      finiteExpectation w X - finiteExpectation w Y := by
  simp [finiteExpectation, mul_sub, Finset.sum_sub_distrib]

/-- The exact mean is the centering parameter, with normalization explicit. -/
theorem finiteExpectation_centered_eq_zero (w : Ω → R) (X : Ω → R)
    (h_mass : ∑ ω, w ω = 1) :
    finiteExpectation w (fun ω => X ω - finiteExpectation w X) = 0 := by
  rw [finiteExpectation_sub, finiteExpectation_const, h_mass, one_mul, sub_self]

/-- Centered moments of a finite dependent family. -/
def centeredMoment (w : Ω → R) (J : ι → Ω → R) (p : ι → R) (I : Finset ι) : R :=
  finiteExpectation w (fun ω => ∏ x ∈ I, (J x ω - p x))

theorem centeredMoment_empty (w : Ω → R) (J : ι → Ω → R) (p : ι → R)
    (h_mass : ∑ ω, w ω = 1) : centeredMoment w J p ∅ = 1 := by
  simp [centeredMoment, finiteExpectation, h_mass]

theorem centeredMoment_singleton_eq_zero (w : Ω → R) (J : ι → Ω → R) (x : ι)
    (h_mass : ∑ ω, w ω = 1) :
    centeredMoment w J (fun i => finiteExpectation w (J i)) {x} = 0 := by
  simpa [centeredMoment] using finiteExpectation_centered_eq_zero w (J x) h_mass

/-- Pointwise inclusion-exclusion with the complementary-cardinality sign. -/
theorem centered_product_inclusion_exclusion [DecidableEq ι]
    (J p : ι → R) (I : Finset ι) :
    (∏ x ∈ I, (J x - p x)) =
      ∑ A ∈ I.powerset, (-1 : R) ^ (I.card - A.card) *
        (∏ x ∈ A, J x) * ∏ x ∈ I \ A, p x := by
  simp only [sub_eq_add_neg]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.prod_neg, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hA)]
  ring1

/-- Actual centered moments equal the algebraic centering transform of joint moments.

This also holds for non-normalized signed weights; all normalization and positivity
premises belong to the separate probability interpretation.
-/
theorem centeredMoment_eq_centeredCoefficient [DecidableEq ι]
    (w : Ω → R) (J : ι → Ω → R) (p : ι → R) (I : Finset ι) :
    centeredMoment w J p I = centeredCoefficient p
      (fun A => finiteExpectation w (fun ω => ∏ x ∈ A, J x ω)) I := by
  unfold centeredMoment centeredCoefficient finiteExpectation
  simp_rw [centered_product_inclusion_exclusion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring1

end Ring

section ProductExpansion
variable [DecidableEq ι] [CommSemiring R] [CommSemiring A]

/-- Finite expansion of a weighted product around arbitrary deterministic factors.

`φ` transports the scalar coefficients into the commutative target semiring.
In the signed-law application the target is the convolution ring of finitely
supported measures and `t` is the difference of the atoms at one and zero.
-/
theorem finite_weighted_product_expansion (G : Finset ι) (φ : R →+* A)
    (w : Ω → R) (b : ι → A) (Y : ι → Ω → R) (t : A) :
    (∑ ω, φ (w ω) * ∏ x ∈ G, (b x + φ (Y x ω) * t)) =
      ∑ I ∈ G.powerset,
        φ (finiteExpectation w (fun ω => ∏ x ∈ I, Y x ω)) *
          t ^ I.card * ∏ x ∈ G \ I, b x := by
  classical
  calc
    (∑ ω, φ (w ω) * ∏ x ∈ G, (b x + φ (Y x ω) * t)) =
        ∑ ω, ∑ I ∈ G.powerset,
          φ (w ω * ∏ x ∈ I, Y x ω) * t ^ I.card * ∏ x ∈ G \ I, b x := by
      apply Finset.sum_congr rfl
      intro ω _
      have hprod : (∏ x ∈ G, (b x + φ (Y x ω) * t)) =
          ∏ x ∈ G, (φ (Y x ω) * t + b x) := by
        apply Finset.prod_congr rfl
        intro x _
        exact add_comm _ _
      rw [hprod, Finset.prod_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, map_mul]
      ring1
    _ = ∑ I ∈ G.powerset,
        φ (finiteExpectation w (fun ω => ∏ x ∈ I, Y x ω)) *
          t ^ I.card * ∏ x ∈ G \ I, b x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I _
      simp only [finiteExpectation, map_sum, Finset.sum_mul]

end ProductExpansion

end PaperP1.Algebra
