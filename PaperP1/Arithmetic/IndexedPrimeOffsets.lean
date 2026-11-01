module

public import PaperP1.Arithmetic.OffsetLinePrimeProduct
public import PaperP1.Arithmetic.OffsetLinePopulation

/-! # Indexed distinct primes and their actual offset assignments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndexedPrimeOffsets

open Finset PaperP1.OffsetLinePopulation PaperP1.OffsetLineData PaperP1.OffsetLinePrimeProduct
  PaperP1.IntegralLine PaperP1.Arithmetic PaperP1.SaturationPrimes

variable {I : Type*} [Fintype I]

def primeSet (p : I → ℕ) : Finset ℕ := univ.image p

def indexEquiv (p : I → ℕ) (hp : Function.Injective p) : I ≃ primeSet p :=
  Equiv.ofBijective (fun i ↦ ⟨p i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩) ⟨
    fun _ _ h ↦ hp (congrArg Subtype.val h),
    fun q ↦ by
      obtain ⟨i, _, hi⟩ := mem_image.mp q.property
      exact ⟨i, Subtype.ext hi⟩⟩

def offsets {L : ℕ} (p : I → ℕ) (hp : Function.Injective p)
    (u : I → Fin 3 → Fin (L + 1)) (q : primeSet p) : Fin 3 → Fin (L + 1) :=
  u ((indexEquiv p hp).symm q)

theorem indexEquiv_val (p : I → ℕ) (hp : Function.Injective p) (i : I) :
    (indexEquiv p hp i).val = p i := rfl

theorem indexEquiv_symm_val (p : I → ℕ) (hp : Function.Injective p) (q : primeSet p) :
    p ((indexEquiv p hp).symm q) = q.val := by
  have h := congrArg Subtype.val ((indexEquiv p hp).apply_symm_apply q)
  simpa only [indexEquiv_val] using h

theorem primeSet_prod (p : I → ℕ) (hp : Function.Injective p) : (primeSet p).prod id = ∏ i, p i := by
  unfold primeSet
  exact prod_image (fun _ _ _ _ h ↦ hp h)

theorem primeSet_prime (p : I → ℕ) (hprime : ∀ i, Nat.Prime (p i)) : ∀ q ∈ primeSet p, Nat.Prime q := by
  intro q hq
  obtain ⟨i, _, rfl⟩ := mem_image.mp hq
  exact hprime i

theorem offsets_divisibility {L : ℕ} (p : I → ℕ) (hp : Function.Injective p)
    (X : Fin 3 → ℕ) (u : I → Fin 3 → Fin (L + 1))
    (hdiv : ∀ i, ∀ j, p i ∣ value (X j) (u i j)) :
    ∀ q : primeSet p, ∀ j, q.val ∣ value (X j) (offsets p hp u q j) := by
  intro q j
  have h := hdiv ((indexEquiv p hp).symm q) j
  rw [indexEquiv_symm_val p hp q] at h
  exact h

theorem offsets_collinear {L : ℕ} (p : I → ℕ) (hp : Function.Injective p)
    (u : I → Fin 3 → Fin (L + 1)) (hcol : Collinear (fun i ↦ offsetVector (u i))) :
    Collinear (point (offsets p hp u)) := by
  intro a b c
  exact hcol ((indexEquiv p hp).symm a) ((indexEquiv p hp).symm b) ((indexEquiv p hp).symm c)

theorem product_le_of_collinear {L N : ℕ} (p : I → ℕ) (hp : Function.Injective p)
    (X : Fin 3 → ℕ) (u : I → Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ j, X j ∈ Ico N (2 * N))
    (hprime : ∀ i, Nat.Prime (p i)) (hdiv : ∀ i j, p i ∣ value (X j) (u i j))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hcol : Collinear (fun i ↦ offsetVector (u i))) : (∏ i, p i) ≤ 6 * N * (L + 1) := by
  rw [← primeSet_prod p hp]
  exact product_le_uniform X (offsets p hp u) hN hLN hX (primeSet_prime p hprime)
    (offsets_divisibility p hp X u hdiv) hinj hdirect (offsets_collinear p hp u hcol)

end PaperP1.IndexedPrimeOffsets
