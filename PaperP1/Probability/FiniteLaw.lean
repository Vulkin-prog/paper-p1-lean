module

public import PaperP1.Algebra.FiniteExpectation
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sets

/-!
# Exact finite count laws

`SignedLaw R` is the convolution ring of finitely supported sequences on the
nonnegative integers, implemented by `AddMonoidAlgebra R ℕ`. Its coefficient
at `k` is the signed mass of the singleton `{k}`; multiplication is convolution.

For finite weighted samples the law is constructed from the actual count.
The centered Bernoulli identity is then proved for arbitrary dependence and
heterogeneous marginal parameters, rather than assumed as an interface.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω ι R : Type*} [Fintype Ω] [CommRing R]

abbrev SignedLaw (R : Type*) [Semiring R] := AddMonoidAlgebra R ℕ

/-- Scalar coefficients enter the convolution ring at the zero atom. -/
def scalar : R →+* SignedLaw R := AddMonoidAlgebra.singleZeroRingHom

/-- Unit mass at a nonnegative integer. -/
def atom (n : ℕ) : SignedLaw R := AddMonoidAlgebra.single n 1

/-- The first forward difference `δ₁ - δ₀`. -/
def forwardDifference : SignedLaw R := atom 1 - atom 0

/-- A Bernoulli reference with its own marginal parameter. -/
def bernoulli (p : R) : SignedLaw R := atom 0 + scalar p * forwardDifference

/-- The scalar value of a Boolean indicator. -/
def indicatorValue (b : Bool) : R := if b then 1 else 0

/-- The count of active indicators on a finite ground set. -/
def indicatorCount (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ x ∈ G, (J x ω).toNat

/-- The exact pushforward of the supplied finite weights by the count. -/
def countLaw (G : Finset ι) (w : Ω → R) (J : ι → Ω → Bool) : SignedLaw R :=
  ∑ ω, scalar (w ω) * atom (indicatorCount G J ω)

@[simp]
theorem scalar_apply (r : R) : scalar r = AddMonoidAlgebra.single 0 r := rfl

@[simp]
theorem atom_zero : (atom 0 : SignedLaw R) = 1 := rfl

theorem scalar_mul_atom (r : R) (n : ℕ) :
    scalar r * atom n = AddMonoidAlgebra.single n r := by
  simp [scalar_apply, atom]

theorem atom_sum (G : Finset ι) (n : ι → ℕ) :
    (∏ x ∈ G, (atom (n x) : SignedLaw R)) = atom (∑ x ∈ G, n x) := by
  simp [atom, AddMonoidAlgebra.prod_single]

theorem atom_indicator (b : Bool) (p : R) :
    atom b.toNat = bernoulli p + scalar (indicatorValue b - p) *
      (forwardDifference : SignedLaw R) := by
  cases b <;> simp only [indicatorValue, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false,
    Bool.toNat_true, bernoulli, forwardDifference, map_sub, map_one, map_zero] <;> ring1

theorem atom_indicator_uncentered (b : Bool) :
    atom b.toNat = 1 + scalar (indicatorValue b) * (forwardDifference : SignedLaw R) := by
  simpa only [bernoulli, map_zero, zero_mul, add_zero, atom_zero, sub_zero] using
    atom_indicator b (0 : R)

omit [Fintype Ω] in
theorem count_atom_product (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    (∏ x ∈ G, (1 + (forwardDifference : SignedLaw R) * scalar (indicatorValue (J x ω)))) =
      atom (indicatorCount G J ω) := by
  rw [indicatorCount, ← atom_sum]
  apply Finset.prod_congr rfl
  intro x _
  rw [atom_indicator_uncentered]
  ring1

omit [Fintype Ω] in
theorem indicatorCount_le_card (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    indicatorCount G J ω ≤ G.card := by
  unfold indicatorCount
  calc
    (∑ x ∈ G, (J x ω).toNat) ≤ ∑ _x ∈ G, 1 := by
      apply Finset.sum_le_sum
      intro x _
      cases J x ω <;> decide
    _ = G.card := by simp

omit [Fintype Ω] in
/-- Reindex a finite set by its finite subtype, preserving the actual count. -/
theorem indicatorCount_subtype (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    indicatorCount (Finset.univ : Finset G) (fun x : G => J x.1) ω = indicatorCount G J ω := by
  classical
  unfold indicatorCount
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach G (fun x => (J x ω).toNat)

/-- Coefficients are the actual weighted probabilities of each count event. -/
theorem countLaw_coeff (G : Finset ι) (w : Ω → R) (J : ι → Ω → Bool) (k : ℕ) :
    (countLaw G w J).coeff k =
      ∑ ω, if indicatorCount G J ω = k then w ω else 0 := by
  classical
  unfold countLaw
  simp_rw [scalar_mul_atom]
  simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply]

/-- The finite law has no mass above the number of sites. -/
theorem countLaw_coeff_eq_zero_of_card_lt (G : Finset ι) (w : Ω → R)
    (J : ι → Ω → Bool) {k : ℕ} (hk : G.card < k) :
    (countLaw G w J).coeff k = 0 := by
  rw [countLaw_coeff]
  apply Finset.sum_eq_zero
  intro ω _
  have hne : indicatorCount G J ω ≠ k := ne_of_lt (lt_of_le_of_lt (indicatorCount_le_card G J ω) hk)
  simp [hne]

/-- Total mass, summed over an explicit finite interval containing the support. -/
theorem countLaw_sum_coeff (G : Finset ι) (w : Ω → R) (J : ι → Ω → Bool) :
    (∑ k ∈ Finset.range (G.card + 1), (countLaw G w J).coeff k) = ∑ ω, w ω := by
  classical
  simp_rw [countLaw_coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  have hm : indicatorCount G J ω ∈ Finset.range (G.card + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (indicatorCount_le_card G J ω))
  simp [hm]

/-- The two Bernoulli atoms, with complementary and active marginal masses. -/
theorem bernoulli_convex_combination (p : R) :
    bernoulli p = scalar (1 - p) * atom 0 + scalar p * atom 1 := by
  simp only [bernoulli, forwardDifference, map_sub, map_one]
  ring1

theorem bernoulli_coeff (p : R) (k : ℕ) :
    (bernoulli p).coeff k =
      (if 0 = k then 1 - p else 0) + (if 1 = k then p else 0) := by
  classical
  rw [bernoulli_convex_combination, scalar_mul_atom, scalar_mul_atom]
  simp [AddMonoidAlgebra.coeff_add, Finsupp.single_apply]
  split_ifs <;> simp_all

theorem bernoulli_sum_coeff (p : R) :
    (∑ k ∈ Finset.range 2, (bernoulli p).coeff k) = 1 := by
  simp [Finset.sum_range_succ, bernoulli_coeff]

/-- Exact centered Bernoulli expansion of the constructed count law.

This is the finite-law version of article Proposition 4.1. No independence,
equal-marginal or positivity premise is needed for the algebraic equality.
Under normalized probability weights and exact marginal parameters the empty
coefficient is one and all singleton coefficients vanish, by the moment lemmas.
-/
theorem centered_countLaw_expansion [DecidableEq ι] (G : Finset ι)
    (w : Ω → R) (J : ι → Ω → Bool) (p : ι → R) :
    countLaw G w J = ∑ I ∈ G.powerset,
      scalar (centeredMoment w (fun x ω => indicatorValue (J x ω)) p I) *
        forwardDifference ^ I.card * ∏ x ∈ G \ I, bernoulli (p x) := by
  calc
    countLaw G w J = ∑ ω, scalar (w ω) *
        ∏ x ∈ G, (bernoulli (p x) +
          scalar (indicatorValue (J x ω) - p x) * forwardDifference) := by
      unfold countLaw
      apply Finset.sum_congr rfl
      intro ω _
      rw [indicatorCount, ← atom_sum]
      congr 1
      apply Finset.prod_congr rfl
      intro x _
      exact atom_indicator (J x ω) (p x)
    _ = _ := by
      simpa [centeredMoment] using finite_weighted_product_expansion G scalar w
        (fun x => bernoulli (p x))
        (fun x ω => indicatorValue (J x ω) - p x) forwardDifference

section Positivity

/-- An actual finite probability space, with positivity and mass recorded. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  total_weight : ∑ ω, weight ω = 1

def exactMarginal (P : FiniteProbability Ω) (J : ι → Ω → Bool) (x : ι) : ℝ :=
  finiteExpectation P.weight (fun ω => indicatorValue (J x ω))

theorem exactMarginal_nonneg (P : FiniteProbability Ω) (J : ι → Ω → Bool) (x : ι) :
    0 ≤ exactMarginal P J x := by
  unfold exactMarginal finiteExpectation
  apply Finset.sum_nonneg
  intro ω _
  cases h : J x ω <;> simp [indicatorValue, h, P.weight_nonneg]

theorem exactMarginal_le_one (P : FiniteProbability Ω) (J : ι → Ω → Bool) (x : ι) :
    exactMarginal P J x ≤ 1 := by
  rw [← P.total_weight]
  unfold exactMarginal finiteExpectation
  apply Finset.sum_le_sum
  intro ω _
  cases h : J x ω <;> simp [indicatorValue, h, P.weight_nonneg]

theorem bernoulli_coeff_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (k : ℕ) :
    0 ≤ (bernoulli p).coeff k := by
  rw [bernoulli_coeff]
  apply add_nonneg
  · split_ifs
    · exact sub_nonneg.mpr h1
    · exact le_rfl
  · split_ifs
    · exact h0
    · exact le_rfl

theorem countLaw_coeff_nonneg (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool)
    (hw : ∀ ω, 0 ≤ w ω) (k : ℕ) : 0 ≤ (countLaw G w J).coeff k := by
  rw [countLaw_coeff]
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_rfl

end Positivity

end PaperP1.Probability
