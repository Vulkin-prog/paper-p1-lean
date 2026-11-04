module

public import PaperP1.Model.AnchoredPrivateValues
public import PaperP1.Arithmetic.PrivatePivotGeometry

/-! # Private pivots away from any arithmetic anchor

All nonanchor pivots are actual largest odd-valuation primes. The anchor
may be defective or a square. Only its value is preserved; no private
coordinate or positivity assumption about its own pivot is made.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredWindowPivots

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePivotGeometry PaperP1.OddPrimePivot PaperP1.AnchoredPrivateValues

def pivots {M j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1) (anchor : Fin B)
    (h1 : ∀ i : Free anchor, 1 < largestOddPrime (j + i.val.val))
    (i : Free anchor) : PrimeUpTo M :=
  ⟨⟨largestOddPrime (j + i.val.val), by
    have hp := Nat.le_of_dvd (by omega : 0 < j + i.val.val) (pivot_spec (h1 i)).2.1
    have hi := i.val.isLt
    omega⟩, (pivot_spec (h1 i)).1⟩

theorem basis {M j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1) (anchor : Fin B)
    (h1 : ∀ i : Free anchor, 1 < largestOddPrime (j + i.val.val))
    (hB : ∀ i : Free anchor, B ≤ largestOddPrime (j + i.val.val)) (i : Free anchor) :
    valueSystem M (relativeValues (fun k : Fin B ↦ j + k.val) anchor)
      (Pi.single (pivots hj hM anchor h1 i) 1) = Pi.single i 1 := by
  apply relative_prime_basis _ anchor (fun k ↦ by omega)
  · intro k
    exact (pivot_spec (h1 k)).2.2
  · intro k l hne
    exact pivot_off_diagonal k.val l (h1 k) (hB k) hne

theorem not_dvd_anchor {M j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1) (anchor : Fin B)
    (h1 : ∀ i : Free anchor, 1 < largestOddPrime (j + i.val.val))
    (hB : ∀ i : Free anchor, B ≤ largestOddPrime (j + i.val.val)) (i : Free anchor) :
    ¬(pivots hj hM anchor h1 i).val.val ∣ j + anchor.val := by
  intro h
  have he := private_divisor (hB i) i.val anchor (pivot_spec (h1 i)).2.1 h
  exact i.property he

theorem injective {M j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1) (anchor : Fin B)
    (h1 : ∀ i : Free anchor, 1 < largestOddPrime (j + i.val.val))
    (hB : ∀ i : Free anchor, B ≤ largestOddPrime (j + i.val.val)) :
    Function.Injective (pivots hj hM anchor h1) := by
  intro i k he
  apply Subtype.ext
  apply private_divisor (hB i) i.val k.val (pivot_spec (h1 i)).2.1
  have hval := congrArg (fun p : PrimeUpTo M ↦ p.val.val) he
  change largestOddPrime (j + i.val.val) = largestOddPrime (j + k.val.val) at hval
  rw [hval]
  exact (pivot_spec (h1 k)).2.1

end PaperP1.AnchoredWindowPivots
