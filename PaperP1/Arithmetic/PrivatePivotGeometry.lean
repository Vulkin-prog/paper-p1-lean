/-
Adapted from Vulkin-prog/paper-c-lean, PaperCPrel8/PivotGeometry.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0,
Git blob d62a795146c734a441aa24e628a297267ca970d4.
Changes: pinned Lean 4.36 modules, existing P1 parity model and namespaces.
-/
module

public import PaperP1.Arithmetic.OddPrimePivot
public import PaperP1.Model.PrivateValueSystem

/-! # Largest odd-valuation pivots are actual private prime coordinates

No exponent-one valuation assumption is needed. The prime two is included;
"odd" refers to the valuation. A pivot at least the word length is private.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivatePivotGeometry

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.OddPrimePivot PaperP1.DefectivePredicate

theorem pivot_mem_support {n : ℕ} (h : 1 < largestOddPrime n) :
    largestOddPrime n ∈ oddPrimeSupport n := by
  have hs : (oddPrimeSupport n).Nonempty := by
    by_contra he
    have he := Finset.not_nonempty_iff_eq_empty.mp he
    simp [largestOddPrime, he] at h
  have hm := Finset.sup_mem_of_nonempty (f := id) hs
  have he : largestOddPrime n = (oddPrimeSupport n).sup id := by
    unfold largestOddPrime at *
    omega
  rw [he]
  simpa using hm

theorem pivot_spec {n : ℕ} (h : 1 < largestOddPrime n) :
    (largestOddPrime n).Prime ∧ largestOddPrime n ∣ n ∧
      parityVec n (largestOddPrime n) = 1 := by
  have hm := pivot_mem_support h
  have hf : largestOddPrime n ∈ n.factorization.support := Finsupp.support_mapRange hm
  refine ⟨Nat.prime_of_mem_primeFactors hf, Nat.dvd_of_mem_primeFactors hf, ?_⟩
  have ho := oddFactorization_apply_eq_one_of_mem hm
  change n.factorization (largestOddPrime n) % 2 = 1 at ho
  rw [parityVec_apply, ← ZMod.natCast_mod (n.factorization (largestOddPrime n)) 2, ho]
  rfl

theorem private_divisor {j B p : ℕ} (hp : B ≤ p) (a b : Fin B)
    (ha : p ∣ j + a.val) (hb : p ∣ j + b.val) : a = b := by
  apply Fin.ext
  have he := ha.modEq_zero_nat.trans hb.modEq_zero_nat.symm
  have he := (Nat.ModEq.refl j).add_left_cancel he
  exact he.eq_of_lt_of_lt (a.isLt.trans_le hp) (b.isLt.trans_le hp)

theorem pivot_off_diagonal {j B : ℕ} (a b : Fin B)
    (h1 : 1 < largestOddPrime (j + a.val))
    (hB : B ≤ largestOddPrime (j + a.val)) (hne : b ≠ a) :
    parityVec (j + b.val) (largestOddPrime (j + a.val)) = 0 := by
  have hd := (pivot_spec h1).2.1
  have hn : ¬largestOddPrime (j + a.val) ∣ j + b.val := by
    intro hb
    exact hne (private_divisor hB b a hb hd)
  simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hn]

theorem pivot_injective {j B : ℕ}
    (h1 : ∀ a : Fin B, 1 < largestOddPrime (j + a.val))
    (hB : ∀ a : Fin B, B ≤ largestOddPrime (j + a.val)) :
    Function.Injective (fun a : Fin B ↦ largestOddPrime (j + a.val)) := by
  intro a b he
  apply private_divisor (hB a) a b (pivot_spec (h1 a)).2.1
  change largestOddPrime (j + a.val) = largestOddPrime (j + b.val) at he
  rw [he]
  exact (pivot_spec (h1 b)).2.1

def cylinderPivot {M j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1)
    (h1 : ∀ a : Fin B, 1 < largestOddPrime (j + a.val)) (a : Fin B) : PrimeUpTo M :=
  ⟨⟨largestOddPrime (j + a.val), by
    have hp := Nat.le_of_dvd (by omega : 0 < j + a.val) (pivot_spec (h1 a)).2.1
    have ha := a.isLt
    omega⟩, (pivot_spec (h1 a)).1⟩

theorem cylinderPivot_basis {M j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1)
    (h1 : ∀ a : Fin B, 1 < largestOddPrime (j + a.val))
    (hB : ∀ a : Fin B, B ≤ largestOddPrime (j + a.val)) (a : Fin B) :
    valueSystem M (fun i : Fin B ↦ j + i.val)
      (Pi.single (cylinderPivot hj hM h1 a) 1) = Pi.single a 1 := by
  apply valueSystem_prime_basis
  · exact (pivot_spec (h1 a)).2.2
  · intro b hb
    exact pivot_off_diagonal a b (h1 a) (hB a) hb

end PaperP1.PrivatePivotGeometry
