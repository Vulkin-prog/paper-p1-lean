module

public import PaperP1.Arithmetic.SaturationCounts

/-! # Saturation counting already works at the non-strict threshold D >= N -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelaxedSaturation

open Finset PaperP1.SaturationPrimes PaperP1.SaturationCounts

def Edge (B N : ℕ) (Y : ℝ) (x y : ℕ) : Prop :=
  x ≠ y ∧ ∃ u v : Fin B, u ≠ v ∧ ∃ D : ℕ,
    N ≤ D ∧ D ∣ pairProduct Y x u v ∧ ∀ p ∈ D.primeFactors, ∃ w : Fin B, p ∣ value y w

def outgoing (B N : ℕ) (Y : ℝ) (x : ℕ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter (Edge B N Y x)

def incoming (B N : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter (fun x ↦ Edge B N Y x y)

theorem source_edge_subset {B N : ℕ} {Y : ℝ} {x y : ℕ}
    (hB : 1 ≤ B) (h : PaperP1.SaturationPrimes.Edge B N Y x y) : Edge B N Y x y := by
  obtain ⟨hne, u, v, huv, D, hD, hdiv, hreceive⟩ := h
  exact ⟨hne, u, v, huv, D, by nlinarith, hdiv, hreceive⟩

theorem outgoing_subset_cover {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    outgoing B N Y x ⊆ outgoingCover B N Y x := by
  classical
  intro y hy
  obtain ⟨hy, _, u, v, huv, D, hD, hdiv, hreceiving⟩ := mem_filter.mp hy
  obtain ⟨hsub, hcard, hprod, hND, _⟩ := divisor_data_of_le hN hB hBN hx Y hY u v huv D hD hdiv
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
  obtain ⟨hx, _, u, v, huv, D, hD, hdiv, hreceiving⟩ := mem_filter.mp hx
  obtain ⟨_, hcard, hprod, hND, hprimes⟩ := divisor_data_of_le hN hB hBN hx Y hY u v huv D hD hdiv
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

theorem outgoing_bound {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((outgoing B N Y x).card : ℝ) ≤ (B : ℝ) ^ 2 * ((B : ℝ) + 1) ^
      PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  have hsub : ((outgoing B N Y x).card : ℝ) ≤ (outgoingCover B N Y x).card := by
    exact_mod_cast card_le_card (outgoing_subset_cover hN hB hBN hx Y hY)
  exact hsub.trans (card_outgoingCover_le hN hB hBN hx Y hY)

theorem incoming_bound {B N y : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((incoming B N Y y).card : ℝ) ≤ (B : ℝ) ^ 2 * (2 * Real.exp 1 * (B : ℝ)) ^
      PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  have hsub : ((incoming B N Y y).card : ℝ) ≤ (incomingCover B N Y y).card := by
    exact_mod_cast card_le_card (incoming_subset_cover hN hB hBN hy Y hY)
  exact hsub.trans (card_incomingCover_le hN hB hBN hy Y hY)

theorem neighbors_bound {B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((outgoing B N Y x ∪ incoming B N Y x).card : ℝ) ≤
      2 * (B : ℝ) ^ 2 * (2 * Real.exp 1 * (B : ℝ)) ^
        PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  have hout := outgoing_bound hN hB hBN hx Y hY
  have hin := incoming_bound hN hB hBN hx Y hY
  have hBpos : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase : (B : ℝ) + 1 ≤ 2 * Real.exp 1 * (B : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hexp) hBpos]
  have hout' := hout.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hbase (PaperP1.PrimeProductBudget.assignmentExponent N Y))
      (by positivity : (0 : ℝ) ≤ (B : ℝ) ^ 2))
  have hunion : ((outgoing B N Y x ∪ incoming B N Y x).card : ℝ) ≤
      (outgoing B N Y x).card + (incoming B N Y x).card := by exact_mod_cast card_union_le _ _
  linarith

end PaperP1.RelaxedSaturation
