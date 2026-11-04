module

public import PaperP1.Arithmetic.CleanPivotMultiples
public import Mathlib.Tactic.Positivity

/-! # Clean directed pivot targets with explicit collision and square losses

A target begins at a multiple of the chosen pivot `q`, with valuation one.
Every other selected pivot is excluded from every target position.
The inequalities are finite and uniform in the translated interval.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CleanPivotTargets

open Finset PaperP1.CleanPivotMultiples

def otherHits (A N q B : ℕ) (R : Finset ℕ) : Finset ℕ :=
  R.biUnion fun r ↦ (univ : Finset (Fin B)).biUnion fun k ↦ crossHits A N q r k.val

def targets (A N q B : ℕ) (R : Finset ℕ) : Finset ℕ :=
  multiples A N q \ (multiples A N (q ^ 2) ∪ otherHits A N q B R)

theorem mem_targets {A N q B n : ℕ} {R : Finset ℕ} :
    n ∈ targets A N q B R ↔ n ∈ Ioc A (A + N) ∧ q ∣ n ∧ ¬q ^ 2 ∣ n ∧
      ∀ r ∈ R, ∀ k : Fin B, ¬r ∣ n + k.val := by
  constructor
  · intro hn
    obtain ⟨hbase, hbad⟩ := mem_sdiff.mp hn
    obtain ⟨hI, hq⟩ := mem_filter.mp hbase
    refine ⟨hI, hq, ?_, ?_⟩
    · intro hsq
      exact hbad (mem_union_left _ (mem_filter.mpr ⟨hI, hsq⟩))
    · intro r hr k hdiv
      exact hbad (mem_union_right _ (mem_biUnion.mpr ⟨r, hr,
        mem_biUnion.mpr ⟨k, mem_univ _, mem_filter.mpr ⟨hI, hq, hdiv⟩⟩⟩))
  · rintro ⟨hI, hq, hsq, hother⟩
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨hI, hq⟩, ?_⟩
    intro hn
    rcases mem_union.mp hn with hn | hn
    · exact hsq (mem_filter.mp hn).2
    · obtain ⟨r, hr, hn⟩ := mem_biUnion.mp hn
      obtain ⟨k, _, hk⟩ := mem_biUnion.mp hn
      exact hother r hr k (mem_filter.mp hk).2.2

theorem other_card_upper (A N q B : ℕ) (R : Finset ℕ)
    (hcop : ∀ r ∈ R, q.Coprime r) :
    (otherHits A N q B R).card ≤ ∑ r ∈ R, ∑ _k : Fin B, (N / (q * r) + 1) := by
  calc
    _ ≤ ∑ r ∈ R, ((univ : Finset (Fin B)).biUnion fun k ↦ crossHits A N q r k.val).card :=
      card_biUnion_le
    _ ≤ ∑ r ∈ R, ∑ k : Fin B, (crossHits A N q r k.val).card :=
      sum_le_sum fun _ _ ↦ card_biUnion_le
    _ ≤ _ := sum_le_sum fun r hr ↦ sum_le_sum fun k _ ↦ cross_card_upper A N q r k.val (hcop r hr)

theorem other_real_upper (A N q B : ℕ) (R : Finset ℕ)
    (hcop : ∀ r ∈ R, q.Coprime r) :
    ((otherHits A N q B R).card : ℝ) ≤ ∑ r ∈ R, ∑ _k : Fin B, ((N : ℝ) / ((q : ℝ) * r) + 1) := by
  have hc : ((otherHits A N q B R).card : ℝ) ≤
      ∑ r ∈ R, ∑ _k : Fin B, (((N / (q * r) : ℕ) : ℝ) + 1) := by
    exact_mod_cast other_card_upper A N q B R hcop
  refine hc.trans (sum_le_sum fun r _ ↦ sum_le_sum fun _ _ ↦ ?_)
  have hd : ((N / (q * r) : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * r) := by
    simpa only [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := N) (n := q * r))
  linarith only [hd]

theorem other_cutoff_upper (A N q B Y : ℕ) (R : Finset ℕ)
    (hq : 0 < q) (hY : 0 < Y) (hR : ∀ r ∈ R, Y ≤ r)
    (hcop : ∀ r ∈ R, q.Coprime r) :
    ((otherHits A N q B R).card : ℝ) ≤
      (R.card : ℝ) * B * ((N : ℝ) / ((q : ℝ) * Y) + 1) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    _ ≤ ∑ r ∈ R, ∑ _k : Fin B, ((N : ℝ) / ((q : ℝ) * r) + 1) :=
      other_real_upper A N q B R hcop
    _ ≤ ∑ _r ∈ R, ∑ _k : Fin B, ((N : ℝ) / ((q : ℝ) * Y) + 1) := by
      apply sum_le_sum
      intro r hr
      apply sum_le_sum
      intro _ _
      have hd : (N : ℝ) / ((q : ℝ) * r) ≤ (N : ℝ) / ((q : ℝ) * Y) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos hqR hYR)
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hR r hr) hqR.le)
      linarith only [hd]
    _ = _ := by simp [mul_assoc]

theorem square_cutoff_upper (A N q Y : ℕ) (hY : 0 < Y) (hYq : Y ≤ q) :
    ((multiples A N (q ^ 2)).card : ℝ) ≤ (N : ℝ) / ((q : ℝ) * Y) + 1 := by
  have hq : 0 < q := hY.trans_le hYq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have h := (real_bounds A N (q ^ 2) (pow_pos hq 2)).2
  have hd : (N : ℝ) / (q : ℝ) ^ 2 ≤ (N : ℝ) / ((q : ℝ) * Y) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos hqR hYR)
      (by rw [pow_two]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hYq) hqR.le)
  simp only [Nat.cast_pow] at h
  linarith only [h, hd]

theorem cover_by_deleted (A N q B : ℕ) (R : Finset ℕ) :
    multiples A N q ⊆ targets A N q B R ∪ (multiples A N (q ^ 2) ∪ otherHits A N q B R) := by
  intro n hn
  by_cases hb : n ∈ multiples A N (q ^ 2) ∪ otherHits A N q B R
  · exact mem_union_right _ hb
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hn, hb⟩)

theorem card_deletion_ledger (A N q B : ℕ) (R : Finset ℕ) :
    (multiples A N q).card ≤ (targets A N q B R).card +
      (multiples A N (q ^ 2)).card + (otherHits A N q B R).card := by
  have h := (card_le_card (cover_by_deleted A N q B R)).trans (card_union_le _ _)
  have h' := card_union_le (s := multiples A N (q ^ 2)) (t := otherHits A N q B R)
  omega

/-- A literal finite lower bound, before any analytic density or cost estimate. -/
theorem clean_lower (A N q B Y : ℕ) (R : Finset ℕ)
    (hY : 0 < Y) (hYq : Y ≤ q) (hR : ∀ r ∈ R, Y ≤ r)
    (hcop : ∀ r ∈ R, q.Coprime r) :
    (N : ℝ) / q - 1 - ((R.card : ℝ) * B + 1) * ((N : ℝ) / ((q : ℝ) * Y) + 1) ≤
      ((targets A N q B R).card : ℝ) := by
  have hq : 0 < q := hY.trans_le hYq
  have hl := (real_bounds A N q hq).1
  have hs := square_cutoff_upper A N q Y hY hYq
  have ho := other_cutoff_upper A N q B Y R hq hY hR hcop
  have hd : ((multiples A N q).card : ℝ) ≤ (targets A N q B R).card +
      (multiples A N (q ^ 2)).card + (otherHits A N q B R).card := by
    exact_mod_cast card_deletion_ledger A N q B R
  nlinarith only [hl, hs, ho, hd]

end PaperP1.CleanPivotTargets
