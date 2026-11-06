module

public import PaperP1.Algebra.HyperellipticFiniteCoordinates
public import PaperP1.Algebra.HyperellipticProductIndependence
public import PaperP1.Algebra.FiniteFunctionLinearKernel

/-! # The actual finite linear tangent-constraint map and its literal polynomial kernel identities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticAuxiliaryConstraints

open Polynomial HyperellipticPolynomialAlgebra HyperellipticPoleDegree HyperellipticWeightedMonomials
open HyperellipticMonomialIndex HyperellipticFiniteCoordinates HyperellipticTangentDegree
open HyperellipticTangentDerivation DerivationPowerEvaluation
open scoped QuadraticAlgebra Classical

abbrev PairIndex (d A B : ℕ) := Index d A × Index d B

abbrev ConstraintIndex (d A B m : ℕ) := Σ r : Fin m, Index d (A + B + r.val * (d - 2))

variable {F : Type*} [Field F]

def combination {ι : Type*} [Fintype ι] (f : F[X]) (z : ι → CurveRing f) :
    (ι → F) →ₗ[F] CurveRing f where
  toFun c := ∑ i, c i • z i
  map_add' c e := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t c := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

def rawConstraint (f : F[X]) (A B r : ℕ) : (PairIndex f.natDegree A B → F) →ₗ[F] CurveRing f :=
  combination f (fun ij ↦ iter (tangent f) r (vector f (embed f.natDegree A ij.1)) *
    vector f (embed f.natDegree B ij.2))

def constraintMap (f : F[X]) (A B m : ℕ) :
    (PairIndex f.natDegree A B → F) →ₗ[F] (ConstraintIndex f.natDegree A B m → F) :=
  LinearMap.pi (fun j ↦ (coefficient f (A + B + j.1.val * (f.natDegree - 2)) j.2).comp
    (rawConstraint f A B j.1.val))

def candidate (f : F[X]) (A B p : ℕ) : (PairIndex f.natDegree A B → F) →ₗ[F] CurveRing f :=
  combination f (fun ij ↦ vector f (embed f.natDegree A ij.1) *
    vector f (embed f.natDegree B ij.2) ^ p)

theorem raw_degree_bound (f : F[X]) (hodd : Odd f.natDegree) (A B r : ℕ)
    (c : PairIndex f.natDegree A B → F) :
    poleDegree f (rawConstraint f A B r c) ≤ A + B + r * (f.natDegree - 2) := by
  have hd : 1 ≤ f.natDegree := by obtain ⟨g, hg⟩ := hodd; omega
  change poleDegree f (∑ ij, c ij •
    (iter (tangent f) r (vector f (embed f.natDegree A ij.1)) *
      vector f (embed f.natDegree B ij.2))) ≤ _
  apply sum_bound f hodd
  intro ij _
  apply (smul_bound f (c ij) _).trans
  have ha : poleDegree f (vector f (embed f.natDegree A ij.1)) ≤ A := by
    rw [vector_degree f hodd]
    exact weight_le _ _ _
  have hb : poleDegree f (vector f (embed f.natDegree B ij.2)) ≤ B := by
    rw [vector_degree f hodd]
    exact weight_le _ _ _
  have hiter := iterate_bound f hodd hd A _ ha r
  have hmul := mul_bound f hodd (iter (tangent f) r (vector f (embed f.natDegree A ij.1)))
    (vector f (embed f.natDegree B ij.2))
  omega

theorem identities_of_kernel (f : F[X]) (hodd : Odd f.natDegree) (A B m : ℕ)
    (c : PairIndex f.natDegree A B → F) (hc : constraintMap f A B m c = 0) (r : Fin m) :
    rawConstraint f A B r.val c = 0 := by
  apply zero_of_coefficients f hodd (A + B + r.val * (f.natDegree - 2)) _
    (raw_degree_bound f hodd A B r.val c)
  intro i
  exact congrFun hc ⟨r, i⟩

theorem candidate_degree_bound (f : F[X]) (hodd : Odd f.natDegree) (A B p : ℕ)
    (c : PairIndex f.natDegree A B → F) : poleDegree f (candidate f A B p c) ≤ A + p * B := by
  change poleDegree f (∑ ij, c ij •
    (vector f (embed f.natDegree A ij.1) * vector f (embed f.natDegree B ij.2) ^ p)) ≤ _
  apply sum_bound f hodd
  intro ij _
  apply (smul_bound f (c ij) _).trans
  rw [product_power_degree f hodd]
  exact Nat.add_le_add (weight_le _ _ _) (Nat.mul_le_mul_left p (weight_le _ _ _))

theorem candidate_ne_zero (f : F[X]) (hodd : Odd f.natDegree) (A B p : ℕ) (hA : A < p)
    (c : PairIndex f.natDegree A B → F) (hc : c ≠ 0) : candidate f A B p c ≠ 0 :=
  HyperellipticProductIndependence.nonzero_linear_combination f hodd A B p hA c hc

theorem target_cardinality (d A B m : ℕ) : Fintype.card (ConstraintIndex d A B m) =
    ∑ r : Fin m, Fintype.card (Index d (A + B + r.val * (d - 2))) := by
  exact Fintype.card_sigma

theorem exists_nonzero_tensor (f : F[X]) (A B m : ℕ)
    (hdim : (∑ r : Fin m, Fintype.card (Index f.natDegree (A + B + r.val * (f.natDegree - 2)))) <
      Fintype.card (Index f.natDegree A) * Fintype.card (Index f.natDegree B)) :
    ∃ c : PairIndex f.natDegree A B → F, c ≠ 0 ∧ constraintMap f A B m c = 0 := by
  apply FiniteFunctionLinearKernel.exists_nonzero_kernel
  simpa only [target_cardinality, PairIndex, Fintype.card_prod] using hdim

end PaperP1.HyperellipticAuxiliaryConstraints
