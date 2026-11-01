module

public import PaperP1.Arithmetic.TruncatedKernelProducts
public import PaperP1.Arithmetic.PrimeSubsetCertificates

/-! # The actual primes and divisor witnesses of saturation edges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SaturationPrimes

open Finset PaperP1.RankinSmallKernel PaperP1.TruncatedKernelProducts

def value {B : ℕ} (x : ℕ) (u : Fin B) : ℕ := x - 1 + u.val

def pairProduct {B : ℕ} (Y : ℝ) (x : ℕ) (u v : Fin B) : ℕ :=
  truncatedKernel Y (value x u) * truncatedKernel Y (value x v)

def pairPrimes {B : ℕ} (Y : ℝ) (x : ℕ) (u v : Fin B) : Finset ℕ :=
  (pairProduct Y x u v).primeFactors

def largePrimes (Y : ℝ) (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p : ℕ ↦ Y < (p : ℝ))

def receiverPrimes (B : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ :=
  univ.biUnion (fun u : Fin B ↦ largePrimes Y (value y u))

def Edge (B N : ℕ) (Y : ℝ) (x y : ℕ) : Prop :=
  x ≠ y ∧ ∃ u v : Fin B, u ≠ v ∧ ∃ D : ℕ,
    6 * N * B < D ∧ D ∣ pairProduct Y x u v ∧
      ∀ p ∈ D.primeFactors, ∃ w : Fin B, p ∣ value y w

def outgoing (B N : ℕ) (Y : ℝ) (x : ℕ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter (Edge B N Y x)

def incoming (B N : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter (fun x ↦ Edge B N Y x y)

theorem mem_outgoing (B N : ℕ) (Y : ℝ) (x y : ℕ) :
    y ∈ outgoing B N Y x ↔ y ∈ Ico N (2 * N) ∧ Edge B N Y x y := by
  classical
  exact mem_filter

theorem mem_incoming (B N : ℕ) (Y : ℝ) (x y : ℕ) :
    x ∈ incoming B N Y y ↔ x ∈ Ico N (2 * N) ∧ Edge B N Y x y := by
  classical
  exact mem_filter

theorem value_bounds {B N x : ℕ} (hN : 10 ≤ N) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (u : Fin B) : 0 < value x u ∧ value x u ≤ 3 * N := by
  have hx' := mem_Ico.mp hx
  have hu := u.isLt
  dsimp [value]
  omega

theorem value_dist_le {B : ℕ} (x : ℕ) (u v : Fin B) : Nat.dist (value x u) (value x v) ≤ B := by
  have hu := u.isLt
  have hv := v.isLt
  rcases le_total (value x u) (value x v) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    dsimp [value]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    dsimp [value]
    omega

theorem pair_data {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) (u v : Fin B) (huv : u ≠ v) :
    0 < pairProduct Y x u v ∧ Squarefree (pairProduct Y x u v) ∧
      pairProduct Y x u v ≤ 9 * N ^ 2 ∧
      (pairPrimes Y x u v).card ≤ PaperP1.PrimeProductBudget.assignmentExponent N Y ∧
      ∀ p ∈ pairPrimes Y x u v, Nat.Prime p ∧ Y < (p : ℝ) := by
  have hne : value x u ≠ value x v := by
    intro h
    exact huv (Fin.ext (Nat.add_left_cancel h))
  have hdist : (Nat.dist (value x u) (value x v) : ℝ) ≤ Y :=
    (by exact_mod_cast value_dist_le x u v : (Nat.dist (value x u) (value x v) : ℝ) ≤ B).trans hY
  have hY1 : 1 < Y := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  obtain ⟨hn, hnN⟩ := value_bounds hN hBN hx u
  obtain ⟨hm, hmN⟩ := value_bounds hN hBN hx v
  refine ⟨Nat.mul_pos (kernel_pos Y _) (kernel_pos Y _), kernel_pair_squarefree Y _ _ hne hdist,
    kernel_pair_upper Y _ _ N hn hm hnN hmN,
    kernel_pair_card_le_assignmentExponent Y hY1 _ _ N hn hm hne hdist hnN hmN, ?_⟩
  intro p hp
  exact ⟨Nat.prime_of_mem_primeFactors hp, kernel_pair_prime_above Y _ _ p hp⟩

theorem mem_largePrimes (Y : ℝ) (n p : ℕ) (hn : 0 < n) :
    p ∈ largePrimes Y n ↔ Nat.Prime p ∧ p ∣ n ∧ Y < (p : ℝ) := by
  constructor
  · intro hp
    obtain ⟨hp, habove⟩ := mem_filter.mp hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hpp, hpd, habove⟩
  · rintro ⟨hpp, hpd, habove⟩
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd, by omega⟩, habove⟩

theorem mem_receiverPrimes (B : ℕ) (Y : ℝ) (y p : ℕ) :
    p ∈ receiverPrimes B Y y ↔ ∃ u : Fin B, p ∈ largePrimes Y (value y u) := by
  simp only [receiverPrimes, mem_biUnion, mem_univ, true_and]

theorem receiverPrimes_prime (B : ℕ) (Y : ℝ) (y p : ℕ) (hp : p ∈ receiverPrimes B Y y) : Nat.Prime p := by
  obtain ⟨u, hu⟩ := (mem_receiverPrimes B Y y p).mp hp
  exact Nat.prime_of_mem_primeFactors (mem_filter.mp hu).1

theorem card_largePrimes_le (Y : ℝ) (hY : 1 < Y) (n N : ℕ) (hn : 0 < n) (hnN : n ≤ 3 * N) :
    (largePrimes Y n).card ≤ PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  apply PaperP1.PrimeProductBudget.card_le_assignmentExponent _ N Y hY
  · intro p hp
    have h := (mem_largePrimes Y n p hn).mp hp
    exact ⟨h.1, h.2.2⟩
  · have hdvd : (largePrimes Y n).prod id ∣ n :=
      (prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
    have hN : 1 ≤ N := by omega
    have h := Nat.le_of_dvd hn hdvd
    nlinarith

theorem card_receiverPrimes_le {B N y : ℕ} (hN : 10 ≤ N) (hBN : B ≤ N + 1)
    (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : 1 < Y) :
    (receiverPrimes B Y y).card ≤ B * PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  calc
    _ ≤ ∑ u : Fin B, (largePrimes Y (value y u)).card := card_biUnion_le
    _ ≤ ∑ _u : Fin B, PaperP1.PrimeProductBudget.assignmentExponent N Y := by
      apply sum_le_sum
      intro u _
      obtain ⟨hn, hnN⟩ := value_bounds hN hBN hy u
      exact card_largePrimes_le Y hY _ N hn hnN
    _ = _ := by simp

theorem divisor_data_of_le {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y)
    (u v : Fin B) (huv : u ≠ v) (D : ℕ) (hD : N ≤ D) (hdiv : D ∣ pairProduct Y x u v) :
    D.primeFactors ⊆ pairPrimes Y x u v ∧
      D.primeFactors.card ≤ PaperP1.PrimeProductBudget.assignmentExponent N Y ∧
      D.primeFactors.prod id = D ∧ N ≤ D ∧
      ∀ p ∈ D.primeFactors, Nat.Prime p ∧ Y < (p : ℝ) ∧ (p ∣ value x u ∨ p ∣ value x v) := by
  obtain ⟨hQpos, hQsq, _, hQcard, hQprime⟩ := pair_data hN hB hBN hx Y hY u v huv
  have hsub : D.primeFactors ⊆ pairPrimes Y x u v := Nat.primeFactors_mono hdiv hQpos.ne'
  have hDsquarefree := hQsq.squarefree_of_dvd hdiv
  refine ⟨hsub, (card_le_card hsub).trans hQcard, Nat.prod_primeFactors_of_squarefree hDsquarefree,
    hD, ?_⟩
  intro p hp
  have hpp := (hQprime p (hsub hp)).1
  have hpQ := (Nat.dvd_of_mem_primeFactors hp).trans hdiv
  have hpval : p ∣ value x u ∨ p ∣ value x v := by
    rcases hpp.dvd_mul.mp hpQ with h | h
    · exact Or.inl (h.trans (kernel_dvd Y _))
    · exact Or.inr (h.trans (kernel_dvd Y _))
  exact ⟨hpp, (hQprime p (hsub hp)).2, hpval⟩

theorem divisor_data {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y)
    (u v : Fin B) (huv : u ≠ v) (D : ℕ) (hD : 6 * N * B < D) (hdiv : D ∣ pairProduct Y x u v) :
    D.primeFactors ⊆ pairPrimes Y x u v ∧
      D.primeFactors.card ≤ PaperP1.PrimeProductBudget.assignmentExponent N Y ∧
      D.primeFactors.prod id = D ∧ N ≤ D ∧
      ∀ p ∈ D.primeFactors, Nat.Prime p ∧ Y < (p : ℝ) ∧ (p ∣ value x u ∨ p ∣ value x v) :=
  divisor_data_of_le hN hB hBN hx Y hY u v huv D (by nlinarith) hdiv

end PaperP1.SaturationPrimes
