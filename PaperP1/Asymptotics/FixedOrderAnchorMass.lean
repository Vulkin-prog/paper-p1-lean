module

public import PaperP1.Asymptotics.FixedAnchorDegreeBudget
public import PaperP1.Asymptotics.SaturationDegrees
public import PaperP1.Arithmetic.MultiAnchorTupleCover
public import PaperP1.Combinatorics.FiniteFamilyEnumeration

/-! # Fixed-order moderate certificates cost t/A rather than the all-order 2t/A -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedOrderAnchorMass

open Finset Filter PaperP1.Model PaperP1.FiniteFamilyEnumeration
  PaperP1.MultiAnchorTupleCover PaperP1.MultiAnchorOrder

/-- An actual enumeration is covered by a good-anchor CRT certificate. -/
def Covered (t r B N : ℕ) (Y T : ℝ) (I : Finset ℕ) : Prop :=
  ∃ z : Fin r → ℕ, tupleSet z = I ∧ z ∈ tupleCover t r B N Y T

theorem cardinal_bound (t r B N : ℕ) (Y T : ℝ) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I.card = r ∧ Covered t r B N Y T I) :
    F.card ≤ (tupleCover t r B N Y T).card := by
  apply family_count F _
  intro I hI
  obtain ⟨z, hset, hz⟩ := (hF I hI).2
  exact ⟨z, hz, hset⟩

theorem uniform_bound (t r : ℕ) (C M A β ε : ℝ)
    (ht : 1 ≤ t) (hr : 1 ≤ r) (hM : 0 ≤ M) (hA : 1 < A)
    (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧
        Covered t r (L + 1) N (cutoff A N) ((N : ℝ) ^ β) I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-(t : ℝ) * β + t / A + ε) := by
  have hD : 1 ≤ PaperP1.CriticalBandScale.upperScale := by
    unfold PaperP1.CriticalBandScale.upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  let J : ℝ := 6 ^ t * r * 2 ^ (r - 1) * (M + 1) ^ r
  have hJ : 0 < J := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    dsimp [J]
    positivity
  obtain ⟨NB, hb⟩ := eventually_atTop.mp
    (PaperP1.FixedAnchorDegreeBudget.product_le_power_eventually t (2 * t) A
      PaperP1.CriticalBandScale.upperScale r J ε (by linarith) hD
      (by exact_mod_cast (show 0 < r by omega)) hJ hε)
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C A hA
  refine ⟨max 10 (max NB (max NF (3 ^ t + 1))), by omega, ?_⟩
  intro N hN L hband p hp hcap F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨_hN10, hB, hBN, hY, hwidth⟩ := hf N (by omega) L hband
  have hcount : (F.card : ℝ) ≤ (tupleCover t r (L + 1) N (cutoff A N) ((N : ℝ) ^ β)).card := by
    exact_mod_cast cardinal_bound t r (L + 1) N (cutoff A N) ((N : ℝ) ^ β) F
      (fun I hI ↦ (hF I hI).2)
  have hfinite := card_tupleCover_le t r (L + 1) N ht hr (by omega) hB hBN
    (cutoff A N) ((N : ℝ) ^ β) hY (Real.one_le_rpow hn1 hβ)
  have hmass : (∑ I ∈ F, ∏ x ∈ I, p x) ≤ (F.card : ℝ) * ((M + 1) / N) ^ r := by
    calc
      _ ≤ ∑ _I ∈ F, ((M + 1) / N) ^ r := by
        apply sum_le_sum
        intro I hI
        have hprod := prod_le_prod₀ (fun x _ ↦ hp x) (fun x hx ↦
          (hcap x ((hF I hI).1 hx)).trans
            (div_le_div_of_nonneg_right (by linarith : M ≤ M + 1) hn.le))
        simpa only [prod_const, (hF I hI).2.1] using hprod
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hdenom : ((N : ℝ) ^ β) ^ t = (N : ℝ) ^ ((t : ℝ) * β) := by
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    ring
  have hcancel : ((6 : ℝ) ^ t * r * (↑(L + 1) : ℝ) ^ (2 * t) * 2 ^ (r - 1) *
      (N : ℝ) ^ r / ((N : ℝ) ^ β) ^ t *
      (↑(r * (L + 1)) : ℝ) ^ PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N (cutoff A N)) *
      ((M + 1) / N) ^ r =
      (J * (↑(L + 1) : ℝ) ^ (2 * t) * (r * (↑(L + 1) : ℝ)) ^ order t A N) /
        (N : ℝ) ^ ((t : ℝ) * β) := by
    dsimp [J, order]
    rw [hdenom, div_pow, Nat.cast_mul]
    field_simp
  have hbudget := hb N (by omega) (L + 1) (by omega) hwidth
  calc
    _ ≤ (F.card : ℝ) * ((M + 1) / N) ^ r := hmass
    _ ≤ ((tupleCover t r (L + 1) N (cutoff A N) ((N : ℝ) ^ β)).card : ℝ) *
        ((M + 1) / N) ^ r := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hfinite (by positivity)
    _ = _ := hcancel
    _ ≤ (N : ℝ) ^ ((t : ℝ) / A + ε) / (N : ℝ) ^ ((t : ℝ) * β) :=
      div_le_div_of_nonneg_right hbudget (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_sub hn]; congr 1; ring

end PaperP1.FixedOrderAnchorMass
