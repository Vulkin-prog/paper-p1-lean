module

public import PaperP1.Arithmetic.SaturationPrimes

/-! # Finite incoming and outgoing saturation counts for actual windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SaturationCounts

open Finset PaperP1.SaturationPrimes PaperP1.PrimeProductBudget

def offsetPairs (B : ℕ) : Finset (Fin B × Fin B) := univ.filter (fun q ↦ q.1 ≠ q.2)

def pairOffset {B : ℕ} (u v : Fin B) (j : Fin 2) : ℕ := if j = 0 then u.val else v.val

def outgoingCover (B N : ℕ) (Y : ℝ) (x : ℕ) : Finset ℕ :=
  (offsetPairs B).biUnion fun q ↦ PaperP1.PrimeSubsetCertificates.targets
    (pairPrimes Y x q.1 q.2) (assignmentExponent N Y) B N N (fun w ↦ w.val)

def incomingCover (B N : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ :=
  (offsetPairs B).biUnion fun q ↦ PaperP1.PrimeSubsetCertificates.targets
    (receiverPrimes B Y y) (assignmentExponent N Y) 2 N N (pairOffset q.1 q.2)

theorem mem_offsetPairs (B : ℕ) (q : Fin B × Fin B) : q ∈ offsetPairs B ↔ q.1 ≠ q.2 := by
  simp [offsetPairs]

theorem card_offsetPairs_le (B : ℕ) : (offsetPairs B).card ≤ B ^ 2 := by
  calc
    _ ≤ Fintype.card (Fin B × Fin B) := card_filter_le _ _
    _ = _ := by simp only [Fintype.card_prod, Fintype.card_fin, pow_two]

theorem outgoing_subset_cover {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    outgoing B N Y x ⊆ outgoingCover B N Y x := by
  classical
  intro y hy
  obtain ⟨hy, _, u, v, huv, D, hD, hdiv, hreceiving⟩ := (mem_outgoing B N Y x y).mp hy
  obtain ⟨hsub, hcard, hprod, hND, _⟩ := divisor_data hN hB hBN hx Y hY u v huv D hD hdiv
  let S := D.primeFactors
  have hw : ∀ p : S, ∃ w : Fin B, p.val ∣ value y w := fun p ↦ hreceiving p.val p.property
  let w : S → Fin B := fun p ↦ Classical.choose (hw p)
  have hwdiv (p : S) : p.val ∣ y - 1 + (w p).val := Classical.choose_spec (hw p)
  apply mem_biUnion.mpr
  refine ⟨(u, v), (mem_offsetPairs B _).mpr huv, ?_⟩
  apply (PaperP1.PrimeSubsetCertificates.mem_targets _ _ B N N y _).mpr
  exact ⟨by simpa only [two_mul] using hy, S, hsub, hcard, by rwa [hprod], w, hwdiv⟩

theorem incoming_subset_cover {B N y : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    incoming B N Y y ⊆ incomingCover B N Y y := by
  classical
  intro x hx
  obtain ⟨hx, _, u, v, huv, D, hD, hdiv, hreceiving⟩ := (mem_incoming B N Y x y).mp hx
  obtain ⟨_, hcard, hprod, hND, hprimes⟩ := divisor_data hN hB hBN hx Y hY u v huv D hD hdiv
  let S := D.primeFactors
  have hsub : S ⊆ receiverPrimes B Y y := by
    intro p hp
    obtain ⟨w, hw⟩ := hreceiving p hp
    have hprime := hprimes p hp
    apply (mem_receiverPrimes B Y y p).mpr
    exact ⟨w, (mem_largePrimes Y _ p (value_bounds hN hBN hy w).1).mpr ⟨hprime.1, hw, hprime.2.1⟩⟩
  have hw : ∀ p : S, ∃ j : Fin 2, p.val ∣ x - 1 + pairOffset u v j := by
    intro p
    rcases (hprimes p.val p.property).2.2 with h | h
    · exact ⟨0, by simpa only [pairOffset, ite_true, value] using h⟩
    · exact ⟨1, by simpa only [pairOffset, one_ne_zero, ite_false, value] using h⟩
  let w : S → Fin 2 := fun p ↦ Classical.choose (hw p)
  have hwdiv (p : S) : p.val ∣ x - 1 + pairOffset u v (w p) := Classical.choose_spec (hw p)
  apply mem_biUnion.mpr
  refine ⟨(u, v), (mem_offsetPairs B _).mpr huv, ?_⟩
  apply (PaperP1.PrimeSubsetCertificates.mem_targets _ _ 2 N N x _).mpr
  exact ⟨by simpa only [two_mul] using hx, S, hsub, hcard, by rwa [hprod], w, hwdiv⟩

theorem card_outgoingCover_le {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((outgoingCover B N Y x).card : ℝ) ≤ (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ assignmentExponent N Y := by
  have hcard : ((offsetPairs B).card : ℝ) ≤ (B : ℝ) ^ 2 := by exact_mod_cast card_offsetPairs_le B
  calc
    _ ≤ ∑ q ∈ offsetPairs B, ((PaperP1.PrimeSubsetCertificates.targets
        (pairPrimes Y x q.1 q.2) (assignmentExponent N Y) B N N (fun w ↦ w.val)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : (outgoingCover B N Y x).card ≤ _)
    _ ≤ ∑ _q ∈ offsetPairs B, ((B : ℝ) + 1) ^ assignmentExponent N Y := by
      apply sum_le_sum
      intro q hq
      obtain ⟨_, _, _, hPcard, hP⟩ := pair_data hN hB hBN hx Y hY q.1 q.2 ((mem_offsetPairs B q).mp hq)
      calc
        _ ≤ (1 + (B : ℝ)) ^ (pairPrimes Y x q.1 q.2).card :=
          PaperP1.PrimeSubsetCertificates.card_targets_le_full _ (fun p hp ↦ (hP p hp).1)
            _ B N N (by omega) _
        _ ≤ _ := by
          rw [add_comm 1 (B : ℝ)]
          apply pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) B] : (1 : ℝ) ≤ (B : ℝ) + 1) hPcard
    _ = ((offsetPairs B).card : ℝ) * ((B : ℝ) + 1) ^ assignmentExponent N Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem card_incomingCover_le {B N y : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((incomingCover B N Y y).card : ℝ) ≤
      (B : ℝ) ^ 2 * (2 * Real.exp 1 * (B : ℝ)) ^ assignmentExponent N Y := by
  have hY1 : 1 < Y := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hpool := card_receiverPrimes_le hN hBN hy Y hY1
  have hpoolR : ((receiverPrimes B Y y).card : ℝ) ≤ (B : ℝ) * assignmentExponent N Y := by exact_mod_cast hpool
  have hcard : ((offsetPairs B).card : ℝ) ≤ (B : ℝ) ^ 2 := by exact_mod_cast card_offsetPairs_le B
  calc
    _ ≤ ∑ q ∈ offsetPairs B, ((PaperP1.PrimeSubsetCertificates.targets
        (receiverPrimes B Y y) (assignmentExponent N Y) 2 N N (pairOffset q.1 q.2)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : (incomingCover B N Y y).card ≤ _)
    _ ≤ ∑ _q ∈ offsetPairs B, (2 * Real.exp 1 * (B : ℝ)) ^ assignmentExponent N Y := by
      apply sum_le_sum
      intro q _
      have ht := PaperP1.PrimeSubsetCertificates.card_targets_le _ (receiverPrimes_prime B Y y)
        (assignmentExponent N Y) 2 N N (by omega) (pairOffset q.1 q.2)
      have hw := PaperP1.BoundedSubsetWeights.weightSum_le_of_card_le
        (receiverPrimes B Y y) 2 (B : ℝ) (assignmentExponent N Y) (by norm_num)
          (by exact_mod_cast (show 1 ≤ B by omega)) hpoolR
      exact ht.trans hw
    _ = ((offsetPairs B).card : ℝ) * (2 * Real.exp 1 * (B : ℝ)) ^ assignmentExponent N Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem outgoing_bound {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((outgoing B N Y x).card : ℝ) ≤ (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^ assignmentExponent N Y := by
  have hsub : ((outgoing B N Y x).card : ℝ) ≤ (outgoingCover B N Y x).card := by
    exact_mod_cast card_le_card (outgoing_subset_cover hN hB hBN hx Y hY)
  exact hsub.trans (card_outgoingCover_le hN hB hBN hx Y hY)

theorem incoming_bound {B N y : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((incoming B N Y y).card : ℝ) ≤
      (B : ℝ) ^ 2 * (2 * Real.exp 1 * (B : ℝ)) ^ assignmentExponent N Y := by
  have hsub : ((incoming B N Y y).card : ℝ) ≤ (incomingCover B N Y y).card := by
    exact_mod_cast card_le_card (incoming_subset_cover hN hB hBN hy Y hY)
  exact hsub.trans (card_incomingCover_le hN hB hBN hy Y hY)

end PaperP1.SaturationCounts
