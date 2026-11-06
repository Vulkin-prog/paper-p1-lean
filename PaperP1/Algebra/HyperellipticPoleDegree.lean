module

public import PaperP1.Algebra.HyperellipticOddDegreeNorm
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Actual norm degree gives a finite polynomial-function filtration -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticPoleDegree

open Polynomial HyperellipticPolynomialAlgebra
open scoped QuadraticAlgebra Classical

variable {F : Type*} [Field F]

def poleDegree (f : F[X]) (z : CurveRing f) : ℕ := (QuadraticAlgebra.norm z).natDegree

theorem zero_degree (f : F[X]) : poleDegree f 0 = 0 := by simp [poleDegree]

theorem coordinates_iff (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f) (L : ℕ) :
    poleDegree f z ≤ L ↔ 2 * z.re.natDegree ≤ L ∧ (z.im = 0 ∨ f.natDegree + 2 * z.im.natDegree ≤ L) := by
  rw [poleDegree, PaperP1.HyperellipticOddDegreeNorm.norm_natDegree f hodd z]
  by_cases hz : z.im = 0 <;> simp [hz]

theorem neg_degree (f : F[X]) (z : CurveRing f) : poleDegree f (-z) = poleDegree f z := by
  rw [poleDegree, QuadraticAlgebra.norm_neg]
  rfl

theorem smul_degree (f : F[X]) (c : F) (hc : c ≠ 0) (z : CurveRing f) :
    poleDegree f (c • z) = poleDegree f z := by
  rw [poleDegree, QuadraticAlgebra.norm_smul, smul_eq_C_mul, natDegree_C_mul (pow_ne_zero 2 hc)]
  rfl

theorem smul_bound (f : F[X]) (c : F) (z : CurveRing f) :
    poleDegree f (c • z) ≤ poleDegree f z := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, zero_degree]
    exact Nat.zero_le _
  · exact le_of_eq (smul_degree f c hc z)

theorem add_bound (f : F[X]) (hodd : Odd f.natDegree) (L : ℕ) (z w : CurveRing f)
    (hz : poleDegree f z ≤ L) (hw : poleDegree f w ≤ L) : poleDegree f (z + w) ≤ L := by
  obtain ⟨hzA, hzB⟩ := (coordinates_iff f hodd z L).mp hz
  obtain ⟨hwA, hwB⟩ := (coordinates_iff f hodd w L).mp hw
  apply (coordinates_iff f hodd (z + w) L).mpr
  constructor
  · change 2 * (z.re + w.re).natDegree ≤ L
    have hh := Polynomial.natDegree_add_le z.re w.re
    omega
  · change z.im + w.im = 0 ∨ f.natDegree + 2 * (z.im + w.im).natDegree ≤ L
    rcases hzB with hz0 | hzD
    · rw [hz0, zero_add]
      exact hwB
    · rcases hwB with hw0 | hwD
      · rw [hw0, add_zero]
        exact Or.inr hzD
      · right
        have hh := Polynomial.natDegree_add_le z.im w.im
        omega

theorem add_degree_le (f : F[X]) (hodd : Odd f.natDegree) (z w : CurveRing f) :
    poleDegree f (z + w) ≤ max (poleDegree f z) (poleDegree f w) :=
  add_bound f hodd _ z w (le_max_left _ _) (le_max_right _ _)

theorem mul_degree (f : F[X]) (hodd : Odd f.natDegree) (z w : CurveRing f) (hz : z ≠ 0) (hw : w ≠ 0) :
    poleDegree f (z * w) = poleDegree f z + poleDegree f w :=
  PaperP1.HyperellipticOddDegreeNorm.norm_natDegree_mul f hodd z w hz hw

theorem mul_bound (f : F[X]) (hodd : Odd f.natDegree) (z w : CurveRing f) :
    poleDegree f (z * w) ≤ poleDegree f z + poleDegree f w := by
  by_cases hz : z = 0
  · rw [hz, zero_mul, zero_degree]
    exact Nat.zero_le _
  · by_cases hw : w = 0
    · rw [hw, mul_zero, zero_degree]
      exact Nat.zero_le _
    · exact le_of_eq (mul_degree f hodd z w hz hw)

theorem sum_bound {ι : Type*} (f : F[X]) (hodd : Odd f.natDegree) (L : ℕ)
    (S : Finset ι) (z : ι → CurveRing f) (h : ∀ i ∈ S, poleDegree f (z i) ≤ L) :
    poleDegree f (∑ i ∈ S, z i) ≤ L := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_degree, Nat.zero_le]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact add_bound f hodd L _ _ (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

theorem one_degree (f : F[X]) : poleDegree f 1 = 0 := by simp [poleDegree]

theorem pow_degree (f : F[X]) (z : CurveRing f) (n : ℕ) :
    poleDegree f (z ^ n) = n * poleDegree f z := by
  rw [poleDegree, map_pow, Polynomial.natDegree_pow]
  rfl


end PaperP1.HyperellipticPoleDegree
