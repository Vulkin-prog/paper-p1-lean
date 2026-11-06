module

public import PaperP1.Arithmetic.FiniteFieldMultivariateZeroBound
public import PaperP1.Algebra.PolynomialCoefficientResultantDegree
public import PaperP1.Algebra.MonicResultantSpecialization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.CharP.Algebra

/-! # Unconditional O_d(q) counts for actual monic hypersurface critical loci in characteristic greater than degree -/

set_option autoImplicit false

@[expose] public noncomputable section
namespace PaperP1.MonicCriticalPointCount
open Polynomial Finset
open scoped Classical
open PolynomialCoefficientResultantDegree MonicResultantSpecialization

section Count
variable {F : Type*} [Field F] [Fintype F]

theorem common_points_card (P Q : (MvPolynomial (Fin 2) F)[X]) (hmonic : P.Monic)
    (hpos : 0 < P.natDegree) (hres : P.resultant Q ≠ 0)
    (S : Finset ((Fin 2 → F) × F))
    (hS : ∀ v ∈ S, P.eval₂ (MvPolynomial.eval v.1) v.2 = 0 ∧
      Q.eval₂ (MvPolynomial.eval v.1) v.2 = 0) :
    S.card ≤ (P.resultant Q).totalDegree * P.natDegree * Fintype.card F := by
  have hbase : (S.image Prod.fst).card ≤ (P.resultant Q).totalDegree * Fintype.card F := by
    simpa only [Nat.reduceSub, pow_one] using FiniteFieldMultivariateZeroBound.cardinality 2 (by decide) (P.resultant Q) hres
      (S.image Prod.fst) (by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
        exact common_base_zero P Q hpos (MvPolynomial.eval w.1) w.2 (hS w hw).1 (hS w hw).2)
  have hfibre (x : Fin 2 → F) : (S.filter fun v ↦ v.1 = x).card ≤ P.natDegree := by
    let T := S.filter fun v ↦ v.1 = x
    have hinj : Set.InjOn (fun v : (Fin 2 → F) × F ↦ v.2) (T : Set _) := by
      intro v hv w hw he
      exact Prod.ext ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm) he
    rw [← card_image_of_injOn hinj]
    apply monic_fibre_card P hmonic (MvPolynomial.eval x)
    intro z hz
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    obtain ⟨hvS, hvx⟩ := mem_filter.mp hv
    simpa only [hvx] using (hS v hvS).1
  calc
    S.card = ∑ x ∈ S.image Prod.fst, (S.filter fun v ↦ v.1 = x).card := card_eq_sum_card_image _ _
    _ ≤ ∑ _x ∈ S.image Prod.fst, P.natDegree := sum_le_sum (fun x _ ↦ hfibre x)
    _ = (S.image Prod.fst).card * P.natDegree := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ ((P.resultant Q).totalDegree * Fintype.card F) * P.natDegree := Nat.mul_le_mul_right _ hbase
    _ = _ := by ring

theorem critical_points_card_from_resultant (P : (MvPolynomial (Fin 2) F)[X]) (hmonic : P.Monic)
    (hpos : 0 < P.natDegree) (hres : P.resultant P.derivative ≠ 0)
    (D : ℕ) (hcoef : ∀ i, (P.coeff i).totalDegree ≤ D)
    (S : Finset ((Fin 2 → F) × F))
    (hS : ∀ v ∈ S, P.eval₂ (MvPolynomial.eval v.1) v.2 = 0 ∧
      P.derivative.eval₂ (MvPolynomial.eval v.1) v.2 = 0) :
    S.card ≤ 2 * P.natDegree^2 * D * Fintype.card F := by
  calc
    _ ≤ (P.resultant P.derivative).totalDegree * P.natDegree * Fintype.card F :=
      common_points_card P P.derivative hmonic hpos hres S hS
    _ ≤ (2 * P.natDegree * D) * P.natDegree * Fintype.card F :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (derivative_resultant_degree P D hcoef))
    _ = _ := by ring

variable (p : ℕ) [CharP F p]

theorem critical_points_card (P : (MvPolynomial (Fin 2) F)[X]) (hmonic : P.Monic)
    (hP : Irreducible P) (hpos : 0 < P.natDegree) (hlt : P.natDegree < p)
    (D : ℕ) (hcoef : ∀ i, (P.coeff i).totalDegree ≤ D)
    (S : Finset ((Fin 2 → F) × F))
    (hS : ∀ v ∈ S, P.eval₂ (MvPolynomial.eval v.1) v.2 = 0 ∧
      P.derivative.eval₂ (MvPolynomial.eval v.1) v.2 = 0) :
    S.card ≤ 2 * P.natDegree^2 * D * Fintype.card F := by
  let : CharP (MvPolynomial (Fin 2) F) p :=
    charP_of_injective_ringHom (f := MvPolynomial.C) (MvPolynomial.C_injective (Fin 2) F) p
  exact critical_points_card_from_resultant P hmonic hpos
    (derivative_resultant_nonzero p P hmonic hP hpos hlt) D hcoef S hS

theorem critical_points_card_degree_cap (P : (MvPolynomial (Fin 2) F)[X]) (hmonic : P.Monic)
    (hP : Irreducible P) (hpos : 0 < P.natDegree) (d : ℕ) (hdegree : P.natDegree ≤ d)
    (hlt : d < p) (hcoef : ∀ i, (P.coeff i).totalDegree ≤ d)
    (S : Finset ((Fin 2 → F) × F))
    (hS : ∀ v ∈ S, P.eval₂ (MvPolynomial.eval v.1) v.2 = 0 ∧
      P.derivative.eval₂ (MvPolynomial.eval v.1) v.2 = 0) :
    S.card ≤ 2 * d^3 * Fintype.card F := by
  calc
    _ ≤ 2 * P.natDegree^2 * d * Fintype.card F :=
      critical_points_card p P hmonic hP hpos (hdegree.trans_lt hlt) d hcoef S hS
    _ ≤ 2 * d^2 * d * Fintype.card F :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hdegree 2)))
    _ = _ := by ring
end Count
end PaperP1.MonicCriticalPointCount
