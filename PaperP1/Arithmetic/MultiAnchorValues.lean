module

public import PaperP1.Arithmetic.ModerateAnchors
public import PaperP1.Arithmetic.MultiAnchorPrimeBudget

/-! # Actual distinct anchor values and their squarefree kernel product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorValues

open Finset PaperP1.RankinSmallKernel PaperP1.TruncatedKernelProducts

abbrev Anchor (t r B N : ℕ) := Fin r × (Finset.Ico N (2 * N)) × (Fin t → Fin B)

def value {t r B N : ℕ} (A : Anchor t r B N) (i : Fin t) : ℕ :=
  A.2.1.val - 1 + (A.2.2 i).val

def product {t r B N : ℕ} (Y : ℝ) (A : Anchor t r B N) : ℕ :=
  ∏ i, truncatedKernel Y (value A i)

def primes {t r B N : ℕ} (Y : ℝ) (A : Anchor t r B N) : Finset ℕ :=
  (product Y A).primeFactors

def Good {t r B N : ℕ} (Y T : ℝ) (A : Anchor t r B N) : Prop :=
  Function.Injective A.2.2 ∧ ∀ i, T < (truncatedKernel Y (value A i) : ℝ)

theorem card_anchor (t r B N : ℕ) : Fintype.card (Anchor t r B N) = r * N * B ^ t := by
  simp only [Anchor, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Nat.card_Ico, two_mul, Nat.add_sub_cancel_left]
  ring

theorem value_bounds {t r B N : ℕ} (hN : 2 ≤ N) (hBN : B ≤ N + 1)
    (A : Anchor t r B N) (i : Fin t) : 0 < value A i ∧ value A i ≤ 3 * N := by
  have hc := mem_Ico.mp A.2.1.property
  have hi := (A.2.2 i).isLt
  dsimp [value]
  omega

theorem values_dist_le {t r B N : ℕ} (A : Anchor t r B N) (i j : Fin t) :
    Nat.dist (value A i) (value A j) ≤ B := by
  have hi := (A.2.2 i).isLt
  have hj := (A.2.2 j).isLt
  rcases le_total (value A i) (value A j) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    dsimp [value]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    dsimp [value]
    omega

theorem values_injective {t r B N : ℕ} (A : Anchor t r B N)
    (hA : Function.Injective A.2.2) : Function.Injective (value A) := by
  intro i j hij
  exact hA (Fin.ext (Nat.add_left_cancel hij))

theorem product_squarefree {t r B N : ℕ} (Y : ℝ) (A : Anchor t r B N)
    (hY : (B : ℝ) ≤ Y) (hA : Function.Injective A.2.2) : Squarefree (product Y A) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply Nat.coprime_iff_isRelPrime.mp
    exact kernels_coprime Y _ _ ((values_injective A hA).ne hij)
      ((by exact_mod_cast values_dist_le A i j :
        (Nat.dist (value A i) (value A j) : ℝ) ≤ B).trans hY)
  · intro i _
    exact kernel_squarefree Y (value A i)

theorem product_pos {t r B N : ℕ} (Y : ℝ) (A : Anchor t r B N) : 0 < product Y A := by
  exact prod_pos (fun i _ ↦ kernel_pos Y (value A i))

theorem prime_receiving_value {t r B N p : ℕ} (Y : ℝ) (A : Anchor t r B N)
    (hp : p ∈ primes Y A) : ∃ i : Fin t, p ∈ support Y (value A i) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ ∏ i, truncatedKernel Y (value A i) := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨i, _, hi⟩ := (hpp.prime.dvd_finsetProd_iff
    (fun i ↦ truncatedKernel Y (value A i))).mp hdvd
  exact ⟨i, (prime_dvd_kernel_iff Y _ _ hpp).mp hi⟩

theorem anchor_data {t r B N : ℕ} (ht : 1 ≤ t) (hN : 2 ≤ N)
    (hB : 2 ≤ B) (hBN : B ≤ N + 1) (Y T : ℝ) (hY : (B : ℝ) ≤ Y)
    (hT : 1 ≤ T) (A : Anchor t r B N) (hA : Good Y T A) :
    0 < product Y A ∧ (primes Y A).prod id = product Y A ∧
      product Y A ≤ (3 * N) ^ t ∧ T ^ t < (product Y A : ℝ) ∧
      (primes Y A).card ≤ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y ∧
      ∀ p ∈ primes Y A, Nat.Prime p ∧ Y < (p : ℝ) := by
  have hY1 : 1 < Y := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hprod : (primes Y A).prod id = product Y A :=
    Nat.prod_primeFactors_of_squarefree (product_squarefree Y A hY hA.1)
  have hupper : product Y A ≤ (3 * N) ^ t := by
    calc
      _ ≤ ∏ _i : Fin t, 3 * N := prod_le_prod
        (fun i _ ↦ (kernel_le Y _ (value_bounds hN hBN A i).1).trans
          (value_bounds hN hBN A i).2)
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
  have hlower : T ^ t < (product Y A : ℝ) := by
    have h := prod_lt_prod_of_nonempty₀ (s := (univ : Finset (Fin t)))
      (f := fun _ ↦ T) (g := fun i ↦ (truncatedKernel Y (value A i) : ℝ))
      (fun _ _ ↦ by linarith) (fun i _ ↦ hA.2 i) ⟨⟨0, by omega⟩, mem_univ _⟩
    simpa only [prod_const, card_univ, Fintype.card_fin, product, Nat.cast_prod] using h
  have hprimes : ∀ p ∈ primes Y A, Nat.Prime p ∧ Y < (p : ℝ) := by
    intro p hp
    obtain ⟨i, hi⟩ := prime_receiving_value Y A hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, (mem_filter.mp hi).2⟩
  refine ⟨product_pos Y A, hprod, hupper, hlower, ?_, hprimes⟩
  apply PaperP1.MultiAnchorPrimeBudget.card_le_assignmentExponent _ t N Y hY1 hprimes
  rw [hprod]
  exact hupper

end PaperP1.MultiAnchorValues
