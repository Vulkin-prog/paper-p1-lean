module

public import PaperP1.Arithmetic.MultiAnchorValues
public import PaperP1.Arithmetic.SaturationPrimes

/-! # Actual saturation edges supported by t distinct anchor values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorSaturation

open Finset PaperP1.RankinSmallKernel PaperP1.TruncatedKernelProducts
open PaperP1.SaturationPrimes (value largePrimes receiverPrimes)

def kernelProduct {t B : ℕ} (Y : ℝ) (x : ℕ) (u : Fin t → Fin B) : ℕ :=
  ∏ i, truncatedKernel Y (value x (u i))

def anchorPrimes {t B : ℕ} (Y : ℝ) (x : ℕ) (u : Fin t → Fin B) : Finset ℕ :=
  (kernelProduct Y x u).primeFactors

def Edge (t B N : ℕ) (Y : ℝ) (x y : ℕ) : Prop :=
  x ≠ y ∧ ∃ u : Fin t → Fin B, Function.Injective u ∧ ∃ D : ℕ,
    6 * N * B < D ∧ D ∣ kernelProduct Y x u ∧
      ∀ p ∈ D.primeFactors, ∃ w : Fin B, p ∣ value y w

def outgoing (t B N : ℕ) (Y : ℝ) (x : ℕ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter (Edge t B N Y x)

def incoming (t B N : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter (fun x ↦ Edge t B N Y x y)

theorem mem_outgoing (t B N : ℕ) (Y : ℝ) (x y : ℕ) :
    y ∈ outgoing t B N Y x ↔ y ∈ Ico N (2 * N) ∧ Edge t B N Y x y := by
  classical
  exact mem_filter

theorem mem_incoming (t B N : ℕ) (Y : ℝ) (x y : ℕ) :
    x ∈ incoming t B N Y y ↔ x ∈ Ico N (2 * N) ∧ Edge t B N Y x y := by
  classical
  exact mem_filter

theorem anchor_data {t B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y)
    (u : Fin t → Fin B) (hu : Function.Injective u) :
    0 < kernelProduct Y x u ∧ Squarefree (kernelProduct Y x u) ∧
      kernelProduct Y x u ≤ (3 * N) ^ t ∧
      (anchorPrimes Y x u).card ≤ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y ∧
      ∀ p ∈ anchorPrimes Y x u,
        Nat.Prime p ∧ Y < (p : ℝ) ∧ ∃ i : Fin t, p ∣ value x (u i) := by
  let A : PaperP1.MultiAnchorValues.Anchor t 1 B N := (0, ⟨x, hx⟩, u)
  have hpos : 0 < kernelProduct Y x u := PaperP1.MultiAnchorValues.product_pos Y A
  have hsq : Squarefree (kernelProduct Y x u) :=
    PaperP1.MultiAnchorValues.product_squarefree Y A hY hu
  have hupper : kernelProduct Y x u ≤ (3 * N) ^ t := by
    calc
      _ ≤ ∏ _i : Fin t, 3 * N := prod_le_prod (fun i _ ↦
        (kernel_le Y _ (PaperP1.SaturationPrimes.value_bounds hN hBN hx (u i)).1).trans
          (PaperP1.SaturationPrimes.value_bounds hN hBN hx (u i)).2)
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
  have hprimes : ∀ p ∈ anchorPrimes Y x u,
      Nat.Prime p ∧ Y < (p : ℝ) ∧ ∃ i : Fin t, p ∣ value x (u i) := by
    intro p hp
    obtain ⟨i, hi⟩ := PaperP1.MultiAnchorValues.prime_receiving_value Y A hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, (mem_filter.mp hi).2,
      i, dvd_of_mem_oddPrimeSupport (mem_filter.mp hi).1⟩
  have hY1 : 1 < Y := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  refine ⟨hpos, hsq, hupper, ?_, hprimes⟩
  apply PaperP1.MultiAnchorPrimeBudget.card_le_assignmentExponent _ t N Y hY1
    (fun p hp ↦ ⟨(hprimes p hp).1, (hprimes p hp).2.1⟩)
  rw [show (anchorPrimes Y x u).prod id = kernelProduct Y x u from
    Nat.prod_primeFactors_of_squarefree hsq]
  exact hupper

theorem divisor_data {t B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y)
    (u : Fin t → Fin B) (hu : Function.Injective u) (D : ℕ)
    (hD : 6 * N * B < D) (hdiv : D ∣ kernelProduct Y x u) :
    D.primeFactors ⊆ anchorPrimes Y x u ∧
      D.primeFactors.card ≤ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y ∧
      D.primeFactors.prod id = D ∧ N ≤ D ∧
      ∀ p ∈ D.primeFactors,
        Nat.Prime p ∧ Y < (p : ℝ) ∧ ∃ i : Fin t, p ∣ value x (u i) := by
  obtain ⟨hpos, hsq, _hupper, hcard, hprimes⟩ := anchor_data hN hB hBN hx Y hY u hu
  have hsub : D.primeFactors ⊆ anchorPrimes Y x u := Nat.primeFactors_mono hdiv hpos.ne'
  refine ⟨hsub, (card_le_card hsub).trans hcard,
    Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hdiv), ?_,
    fun p hp ↦ hprimes p (hsub hp)⟩
  nlinarith

theorem card_largePrimes_le (t : ℕ) (ht : 1 ≤ t) (Y : ℝ) (hY : 1 < Y)
    (n N : ℕ) (hn : 0 < n) (hnN : n ≤ 3 * N) :
    (largePrimes Y n).card ≤ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y := by
  apply PaperP1.MultiAnchorPrimeBudget.card_le_assignmentExponent _ t N Y hY
  · intro p hp
    have h := (PaperP1.SaturationPrimes.mem_largePrimes Y n p hn).mp hp
    exact ⟨h.1, h.2.2⟩
  · have hdvd : (largePrimes Y n).prod id ∣ n :=
      (prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
    calc
      _ ≤ n := Nat.le_of_dvd hn hdvd
      _ ≤ 3 * N := hnN
      _ = (3 * N) ^ 1 := by rw [pow_one]
      _ ≤ (3 * N) ^ t := Nat.pow_le_pow_right (by omega) ht

theorem card_receiverPrimes_le {t B N y : ℕ} (ht : 1 ≤ t) (hN : 10 ≤ N)
    (hBN : B ≤ N + 1) (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : 1 < Y) :
    (receiverPrimes B Y y).card ≤
      B * PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y := by
  calc
    _ ≤ ∑ u : Fin B, (largePrimes Y (value y u)).card := card_biUnion_le
    _ ≤ ∑ _u : Fin B, PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N Y := by
      apply sum_le_sum
      intro u _
      obtain ⟨hn, hnN⟩ := PaperP1.SaturationPrimes.value_bounds hN hBN hy u
      exact card_largePrimes_le t ht Y hY _ N hn hnN
    _ = _ := by simp

end PaperP1.MultiAnchorSaturation
