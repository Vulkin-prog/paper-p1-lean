module

public import PaperP1.Model.PrefixWindowCertificateFamilies
public import PaperP1.Arithmetic.PrefixModerateWeightedSeries

/-! # The actual unordered certificate mass is bounded by the proved factorial series at every cardinality -/

/-! The centre range in this module is the positive prefix [2,N+2),
with exactly N centres; no critical lower bound on a centre is assumed. -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixWindowCertificateMass

open Finset PaperP1.Model PaperP1.PrefixWindowCertificateFamilies PaperP1.PrefixModerateCertificateCount
  PaperP1.PrefixModerateWeightedSeries

theorem certified_layer_bound (r B N : ℕ) (Y T : ℝ) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ (Ico 2 (N + 2)) ∧ I.card = r)
    (hcert : ∀ I ∈ F, Certified r B N Y T I) (p : ℕ → ℝ) (hp : ∀ x, 0 ≤ p x)
    (a : ℝ) (ha : 0 ≤ a) (hcap : ∀ x ∈ (Ico 2 (N + 2)), p x ≤ a) :
    (∑ I ∈ F, ∏ x ∈ I, p x) ≤ weightedTerm B N Y T a r := by
  have hcount : (F.card : ℝ) * (r.factorial : ℝ) ≤ (sourceTuples r B N Y T).card := by
    exact_mod_cast certified_count r B N Y T F hF hcert
  have hfpos : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hcard : (F.card : ℝ) ≤ (sourceTuples r B N Y T).card / (r.factorial : ℝ) :=
    (le_div_iff₀ hfpos).mpr hcount
  calc
    _ ≤ ∑ _I ∈ F, a ^ r := by
      apply sum_le_sum
      intro I hI
      have hprod : (∏ x ∈ I, p x) ≤ ∏ _x ∈ I, a :=
        prod_le_prod₀ (fun x _ ↦ hp x) (fun x hx ↦ hcap x ((hF I hI).1 hx))
      simpa only [prod_const, (hF I hI).2] using hprod
    _ = (F.card : ℝ) * a ^ r := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((sourceTuples r B N Y T).card / (r.factorial : ℝ)) * a ^ r :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg ha _)
    _ = _ := by unfold weightedTerm; ring

theorem certified_total_bound (B N : ℕ) (Y T : ℝ) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ (Ico 2 (N + 2)))
    (hcert : ∀ I ∈ F, Certified I.card B N Y T I) (p : ℕ → ℝ) (hp : ∀ x, 0 ≤ p x)
    (a : ℝ) (ha : 0 ≤ a) (hcap : ∀ x ∈ (Ico 2 (N + 2)), p x ≤ a) :
    (∑ I ∈ F, ∏ x ∈ I, p x) ≤ weightedTotal B N Y T a := by
  classical
  have hsize (I : Finset ℕ) (hI : I ∈ F) : I.card ≤ N := by
    have h := card_le_card (hF I hI)
    simpa only [Nat.card_Ico, Nat.add_sub_cancel] using h
  have hsplit := sum_fiberwise_of_maps_to (s := F) (t := range (N + 1))
    (g := fun I : Finset ℕ ↦ I.card) (fun I hI ↦ mem_range.mpr (by have h := hsize I hI; omega))
    (fun I ↦ ∏ x ∈ I, p x)
  calc
    _ = ∑ r ∈ range (N + 1), ∑ I ∈ F.filter (fun I ↦ I.card = r), ∏ x ∈ I, p x := hsplit.symm
    _ ≤ ∑ r ∈ range (N + 1), weightedTerm B N Y T a r := by
      apply sum_le_sum
      intro r _
      apply certified_layer_bound r B N Y T _ ?_ ?_ p hp a ha hcap
      · intro I hI
        obtain ⟨hI, hcard⟩ := mem_filter.mp hI
        exact ⟨hF I hI, hcard⟩
      · intro I hI
        obtain ⟨hI, hcard⟩ := mem_filter.mp hI
        simpa only [hcard] using hcert I hI
    _ ≤ _ := (summable_weightedTerm B N Y T a).sum_le_tsum _
      (fun r _ ↦ weightedTerm_nonneg B N Y T a ha r)

end PaperP1.PrefixWindowCertificateMass
