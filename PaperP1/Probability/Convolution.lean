module

public import PaperP1.Probability.FiniteLaw
public import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Mass and positivity in the finite convolution ring

Probability status means coefficientwise nonnegativity and total mass one.
The mass functional is evaluation of the monoid algebra at one, proved below
to be the sum of the coefficients. This does not assume an approximation bound.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω ι R : Type*} [Fintype Ω] [CommRing R]

/-- The augmentation homomorphism: total mass is multiplicative under convolution. -/
def totalMass : SignedLaw R →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R)
    (1 : Multiplicative ℕ →* R) (fun _ _ => Commute.all _ _)

@[simp]
theorem totalMass_single (n : ℕ) (r : R) :
    totalMass (AddMonoidAlgebra.single n r) = r := by
  simp [totalMass]

/-- The augmentation is the ordinary finite sum of signed singleton masses. -/
theorem totalMass_eq_sum_coeff (ν : SignedLaw R) :
    totalMass ν = ν.coeff.sum (fun _ r => r) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
  simp only [Finsupp.sum, map_sum, totalMass_single]

@[simp]
theorem totalMass_atom (n : ℕ) : totalMass (atom n : SignedLaw R) = 1 := by
  simp [atom]

@[simp]
theorem totalMass_scalar (r : R) : totalMass (scalar r) = r := by simp

@[simp]
theorem totalMass_forwardDifference : totalMass (forwardDifference : SignedLaw R) = 0 := by
  simp [forwardDifference]

@[simp]
theorem totalMass_bernoulli (p : R) : totalMass (bernoulli p) = 1 := by
  simp [bernoulli]

theorem totalMass_countLaw (G : Finset ι) (w : Ω → R) (J : ι → Ω → Bool) :
    totalMass (countLaw G w J) = ∑ ω, w ω := by
  simp [countLaw, map_sum]

theorem totalMass_bernoulli_product (G : Finset ι) (p : ι → R) :
    totalMass (∏ x ∈ G, bernoulli (p x)) = 1 := by
  simp [map_prod]

/-- A finitely supported real probability law. -/
def IsProbability (ν : SignedLaw ℝ) : Prop :=
  (∀ k, 0 ≤ ν.coeff k) ∧ totalMass ν = 1

theorem countLaw_isProbability (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) : IsProbability (countLaw G P.weight J) := by
  exact ⟨countLaw_coeff_nonneg G P.weight J P.weight_nonneg,
    (totalMass_countLaw G P.weight J).trans P.total_weight⟩

/-- Convolution preserves coefficientwise nonnegativity. -/
theorem convolution_coeff_nonneg {μ ν : SignedLaw ℝ}
    (hμ : ∀ k, 0 ≤ μ.coeff k) (hν : ∀ k, 0 ≤ ν.coeff k) (k : ℕ) :
    0 ≤ (μ * ν).coeff k := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  unfold Finsupp.sum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  dsimp only
  split_ifs
  · exact mul_nonneg (hμ i) (hν j)
  · exact le_rfl

theorem convolution_isProbability {μ ν : SignedLaw ℝ}
    (hμ : IsProbability μ) (hν : IsProbability ν) : IsProbability (μ * ν) := by
  refine ⟨convolution_coeff_nonneg hμ.1 hν.1, ?_⟩
  rw [map_mul, hμ.2, hν.2, one_mul]

theorem atom_isProbability (n : ℕ) : IsProbability (atom n : SignedLaw ℝ) := by
  constructor
  · intro k
    simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> simp
  · exact totalMass_atom n

theorem bernoulli_isProbability {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbability (bernoulli p) :=
  ⟨bernoulli_coeff_nonneg h0 h1, totalMass_bernoulli p⟩

/-- Complementary Bernoulli convolution products really are probabilities. -/
theorem bernoulli_product_isProbability (G : Finset ι) (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) : IsProbability (∏ x ∈ G, bernoulli (p x)) := by
  classical
  induction G using Finset.induction_on with
  | empty => simpa using atom_isProbability 0
  | @insert x G hx ih =>
    rw [Finset.prod_insert hx]
    exact convolution_isProbability (bernoulli_isProbability (hp x).1 (hp x).2) ih

theorem exactMarginal_reference_isProbability (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) : IsProbability (∏ x ∈ G, bernoulli (exactMarginal P J x)) := by
  apply bernoulli_product_isProbability
  intro x
  exact ⟨exactMarginal_nonneg P J x, exactMarginal_le_one P J x⟩

/-- Complete finite-probability version of the centered Bernoulli expansion.

The equality uses the actual count law. The accompanying conclusions certify
the empty coefficient, vanishing singleton terms, and positivity/normalization
of every complementary deterministic convolution product. Dependence among
the indicators is arbitrary. The model-specific cylinder identification is a
separate obligation in the manuscript alignment ledger.
-/
theorem finite_centered_bernoulli_expansion [DecidableEq ι] (G : Finset ι)
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) :
    (countLaw G P.weight J = ∑ I ∈ G.powerset,
      scalar (centeredMoment P.weight (fun x ω => indicatorValue (J x ω))
        (exactMarginal P J) I) * forwardDifference ^ I.card *
          ∏ x ∈ G \ I, bernoulli (exactMarginal P J x)) ∧
    centeredMoment P.weight (fun x ω => indicatorValue (J x ω)) (exactMarginal P J) ∅ = 1 ∧
    (∀ x, centeredMoment P.weight (fun i ω => indicatorValue (J i ω))
      (exactMarginal P J) {x} = 0) ∧
    (∀ I : Finset ι, IsProbability (∏ x ∈ G \ I, bernoulli (exactMarginal P J x))) := by
  refine ⟨centered_countLaw_expansion G P.weight J (exactMarginal P J),
    centeredMoment_empty _ _ _ P.total_weight, ?_, ?_⟩
  · intro x
    exact centeredMoment_singleton_eq_zero P.weight
      (fun i ω => indicatorValue (J i ω)) x P.total_weight
  · intro I
    exact exactMarginal_reference_isProbability (G \ I) P J

end PaperP1.Probability
