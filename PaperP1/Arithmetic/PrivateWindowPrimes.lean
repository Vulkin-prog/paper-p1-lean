module

public import PaperP1.Arithmetic.DefectivePredicate
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.Field.ZMod

/-!
# Large primes are private in a short interval

The elementary distance lemma is adapted from
`PaperC/LinearAlgebra/PrivatePivots.lean`, commit
`b9fa9ba490f201b408a302a86f1594ee620b228b`, Git blob
`899c4303e63e4f631b7aa9a1d8acb96b01792249`, Apache-2.0.
Only this elementary lemma is reused; no graph or private-prime hypothesis
from the later Paper C applications is imported.
-/

@[expose] public section

namespace PaperP1.PrivateWindowPrimes

open PaperP1.Arithmetic

local instance privateWindowPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- Distinct multiples of `p` cannot be at distance less than `p`. -/
theorem not_dvd_of_dvd_and_dist_lt
    {a b p Y : ℕ} (hpa : p ∣ a) (hab : a ≠ b)
    (hpY : Y < p) (hdist : Nat.dist a b < Y) :
    ¬p ∣ b := by
  intro hpb
  obtain ⟨ka, hka⟩ := hpa
  obtain ⟨kb, hkb⟩ := hpb
  have hpdist : p ∣ Nat.dist a b := by
    refine ⟨Nat.dist ka kb, ?_⟩
    calc
      Nat.dist a b = Nat.dist (p * ka) (p * kb) := by rw [hka, hkb]
      _ = p * Nat.dist ka kb := Nat.dist_mul_left p ka kb
  have hpos : 0 < Nat.dist a b := Nat.dist_pos_of_ne hab
  have hple : p ≤ Nat.dist a b := Nat.le_of_dvd hpos hpdist
  omega

theorem not_dvd_other_vertex {U B p : ℕ} (hp : B < p)
    (i j : Fin B) (hij : i ≠ j) (hi : p ∣ U + i.val) :
    ¬p ∣ U + j.val := by
  apply not_dvd_of_dvd_and_dist_lt hi ?_ hp ?_
  · intro h
    apply hij
    apply Fin.ext
    omega
  · rw [Nat.dist_add_add_left]
    have hi := i.isLt
    have hj := j.isLt
    rw [Nat.dist]
    omega

/-- A nonzero prime-parity coordinate at one vertex is zero at every other
vertex when its prime is larger than the window length. -/
theorem parity_other_vertex_zero {U B p : ℕ} (hp : B < p)
    (i j : Fin B) (hij : i ≠ j) (hi : parityVec (U + i.val) p ≠ 0) :
    parityVec (U + j.val) p = 0 := by
  have hpi : p ∣ U + i.val := by
    by_contra hnot
    apply hi
    simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnot]
  have hpj := not_dvd_other_vertex hp i j hij hpi
  simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hpj]

/-- In a vanishing parity relation, a nondefective vertex has zero
coefficient. This statement does not assume evenness of the relation. -/
theorem coefficient_zero_of_not_defective {U B : ℕ} (w : Fin B → F₂)
    (hrelation : ∑ i, w i • parityVec (U + i.val) = 0)
    (i : Fin B) (hi : ¬DefectivePredicate.HDefective B (U + i.val)) :
    w i = 0 := by
  classical
  simp only [DefectivePredicate.HDefective, not_forall] at hi
  obtain ⟨p, hp, hBp, hparity⟩ := hi
  have hcoord := congrArg (fun v : ℕ →₀ F₂ ↦ v p) hrelation
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.zero_apply] at hcoord
  have hsum : (∑ j : Fin B, w j * parityVec (U + j.val) p) =
      w i * parityVec (U + i.val) p := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [parity_other_vertex_zero hBp i j hji.symm hparity, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  rw [hsum] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_right hparity

end PaperP1.PrivateWindowPrimes
