module

public import PaperP1.Algebra.HyperellipticAuxiliaryConstraints
public import PaperP1.Algebra.FiniteFieldDerivationFrobenius
public import PaperP1.Arithmetic.HyperellipticStepanovPointBound

/-! # An actual nonzero tangent auxiliary exists under the explicit finite numerical dimension inequality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticTangentAuxiliary

open Polynomial HyperellipticPolynomialAlgebra HyperellipticPoleDegree HyperellipticWeightedMonomials
open HyperellipticMonomialIndex HyperellipticAuxiliaryConstraints
open HyperellipticTangentDerivation DerivationPowerEvaluation
open scoped QuadraticAlgebra Classical

variable {F : Type*} [Field F]

def evaluationAlgHom (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x) : CurveRing f →ₐ[F] F where
  toRingHom := evaluation f x y hy
  commutes' c := by
    change evaluation f x y hy (algebraMap F[X] (CurveRing f) (C c)) = c
    rw [evaluation_base, eval_C]

variable [Fintype F]

theorem exists_auxiliary (f : F[X]) (hodd : Odd f.natDegree) (A B m : ℕ) (hA : A < Fintype.card F)
    (hdim : (∑ r : Fin m, Fintype.card (Index f.natDegree (A + B + r.val * (f.natDegree - 2)))) <
      Fintype.card (Index f.natDegree A) * Fintype.card (Index f.natDegree B)) :
    ∃ z : CurveRing f, z ≠ 0 ∧ poleDegree f z ≤ A + Fintype.card F * B ∧
      ∀ (x y : F) (hy : y ^ 2 = f.eval x), ∀ r < m,
        evaluation f x y hy (iter (tangent f) r z) = 0 := by
  obtain ⟨c, hc, hkernel⟩ := exists_nonzero_tensor f A B m hdim
  refine ⟨candidate f A B (Fintype.card F) c,
    candidate_ne_zero f hodd A B (Fintype.card F) hA c hc,
    candidate_degree_bound f hodd A B (Fintype.card F) c, ?_⟩
  intro x y hy r hr
  let ε := evaluationAlgHom f x y hy
  have hid := identities_of_kernel f hodd A B m c hkernel ⟨r, hr⟩
  have he := FiniteFieldDerivationFrobenius.evaluation_sum_identity (tangent f) ε c
    (fun ij ↦ vector f (embed f.natDegree A ij.1))
    (fun ij ↦ vector f (embed f.natDegree B ij.2)) r
  change ε (iter (tangent f) r (candidate f A B (Fintype.card F) c)) = ε (rawConstraint f A B r c) at he
  rw [hid, map_zero] at he
  exact he

theorem point_bound_of_dimension (p : ℕ) [CharP F p] (hp : p.Prime) (hchar : ringChar F ≠ 2)
    (f : F[X]) (hodd : Odd f.natDegree) (A B m : ℕ) (hA : A < Fintype.card F)
    (hm0 : 0 < m) (hm : m ≤ p)
    (hdim : (∑ r : Fin m, Fintype.card (Index f.natDegree (A + B + r.val * (f.natDegree - 2)))) <
      Fintype.card (Index f.natDegree A) * Fintype.card (Index f.natDegree B)) :
    ((HyperellipticFiniteFieldPoints.points f).card : ℝ) ≤
      ((A + Fintype.card F * B : ℕ) : ℝ) / m + f.natDegree := by
  obtain ⟨z, hz, hL, hv⟩ := exists_auxiliary f hodd A B m hA hdim
  exact HyperellipticStepanovPointBound.upper_bound p hp hchar f hodd z hz m hm0 hm
    (A + Fintype.card F * B) hL hv

end PaperP1.HyperellipticTangentAuxiliary
