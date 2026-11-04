module

public import PaperP1.Arithmetic.CleanPivotTargets
public import Mathlib.Tactic.Ring

/-! # Total clean directed source--target pairs with an exact reciprocal ledger

All distinguished sources are retained. Arbitrary exceptional target sets
and arbitrary exceptional PAIR sets have separate finite deletion costs.
No source or target independence, density estimate or asymptotic is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CleanPivotPairs

open Finset PaperP1.CleanPivotTargets

def pairs (J : Finset ℕ) (A N B : ℕ) (q : ℕ → ℕ) (R : ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  J.biUnion fun j ↦ (targets A N (q j) B (R j)).image (fun y ↦ (j, y))

theorem mem_pairs {J : Finset ℕ} {A N B : ℕ} {q : ℕ → ℕ} {R : ℕ → Finset ℕ}
    {j y : ℕ} : (j, y) ∈ pairs J A N B q R ↔ j ∈ J ∧ y ∈ targets A N (q j) B (R j) := by
  simp [pairs]

theorem card_pairs (J : Finset ℕ) (A N B : ℕ) (q : ℕ → ℕ) (R : ℕ → Finset ℕ) :
    (pairs J A N B q R).card = ∑ j ∈ J, (targets A N (q j) B (R j)).card := by
  have hd : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint
      ((targets A N (q j) B (R j)).image (fun y ↦ (j, y)))
      ((targets A N (q k) B (R k)).image (fun y ↦ (k, y))) := by
    intro j _ k _ hne
    apply disjoint_left.mpr
    intro p hp hk
    obtain ⟨y, _, hpy⟩ := mem_image.mp hp
    obtain ⟨z, _, hpz⟩ := mem_image.mp hk
    exact hne (congrArg Prod.fst (hpy.trans hpz.symm))
  rw [pairs, card_biUnion hd]
  apply sum_congr rfl
  intro j _
  exact card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.snd h)

def reciprocalSum (J : Finset ℕ) (q : ℕ → ℕ) : ℝ := ∑ j ∈ J, 1 / (q j : ℝ)

theorem reciprocalSum_nonneg (J : Finset ℕ) (q : ℕ → ℕ) : 0 ≤ reciprocalSum J q :=
  sum_nonneg fun _ _ ↦ by positivity

theorem total_lower (J : Finset ℕ) (A N B Y S : ℕ) (q : ℕ → ℕ) (R : ℕ → Finset ℕ)
    (hY : 0 < Y) (hq : ∀ j ∈ J, Y ≤ q j)
    (hR : ∀ j ∈ J, ∀ r ∈ R j, Y ≤ r)
    (hcop : ∀ j ∈ J, ∀ r ∈ R j, (q j).Coprime r) (hsize : ∀ j ∈ J, (R j).card ≤ S) :
    (N : ℝ) * reciprocalSum J q - J.card -
      ((S : ℝ) * B + 1) * (((N : ℝ) / Y) * reciprocalSum J q + J.card) ≤
        ((pairs J A N B q R).card : ℝ) := by
  have ht (j : ℕ) (hj : j ∈ J) :
      (N : ℝ) / q j - 1 - ((S : ℝ) * B + 1) * ((N : ℝ) / ((q j : ℝ) * Y) + 1) ≤
        ((targets A N (q j) B (R j)).card : ℝ) := by
    have h := clean_lower A N (q j) B Y (R j) hY (hq j hj) (hR j hj) (hcop j hj)
    have hs : ((R j).card : ℝ) ≤ S := by exact_mod_cast hsize j hj
    have hcoef : ((R j).card : ℝ) * B + 1 ≤ (S : ℝ) * B + 1 := by
      nlinarith only [hs, Nat.cast_nonneg (α := ℝ) B]
    have hprod := mul_le_mul_of_nonneg_right hcoef
      (by positivity : (0 : ℝ) ≤ (N : ℝ) / ((q j : ℝ) * Y) + 1)
    linarith only [h, hprod]
  calc
    _ = ∑ j ∈ J, ((N : ℝ) / q j - 1 -
        ((S : ℝ) * B + 1) * ((N : ℝ) / ((q j : ℝ) * Y) + 1)) := by
      unfold reciprocalSum
      simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul,
        div_eq_mul_inv, mul_inv_rev, one_mul, ← mul_sum]
      ring
    _ ≤ ∑ j ∈ J, ((targets A N (q j) B (R j)).card : ℝ) := sum_le_sum ht
    _ = _ := by rw [card_pairs, Nat.cast_sum]

def survivors (J : Finset ℕ) (A N B : ℕ) (q : ℕ → ℕ) (R : ℕ → Finset ℕ)
    (T : Finset ℕ) (D : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  pairs J A N B q R \ ((J ×ˢ T) ∪ D)

theorem survival_ledger (J : Finset ℕ) (A N B : ℕ) (q : ℕ → ℕ) (R : ℕ → Finset ℕ)
    (T : Finset ℕ) (D : Finset (ℕ × ℕ)) :
    (pairs J A N B q R).card ≤ (survivors J A N B q R T D).card + J.card * T.card + D.card := by
  have hcover : pairs J A N B q R ⊆ survivors J A N B q R T D ∪ ((J ×ˢ T) ∪ D) := by
    intro p hp
    by_cases hb : p ∈ (J ×ˢ T) ∪ D
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hp, hb⟩)
  have h := (card_le_card hcover).trans (card_union_le _ _)
  have h' := card_union_le (J ×ˢ T) D
  rw [card_product] at h'
  omega

theorem surviving_lower (J : Finset ℕ) (A N B Y S : ℕ) (q : ℕ → ℕ) (R : ℕ → Finset ℕ)
    (T : Finset ℕ) (D : Finset (ℕ × ℕ))
    (hY : 0 < Y) (hq : ∀ j ∈ J, Y ≤ q j)
    (hR : ∀ j ∈ J, ∀ r ∈ R j, Y ≤ r)
    (hcop : ∀ j ∈ J, ∀ r ∈ R j, (q j).Coprime r) (hsize : ∀ j ∈ J, (R j).card ≤ S) :
    (N : ℝ) * reciprocalSum J q - J.card -
      ((S : ℝ) * B + 1) * (((N : ℝ) / Y) * reciprocalSum J q + J.card) -
        (J.card : ℝ) * T.card - D.card ≤ ((survivors J A N B q R T D).card : ℝ) := by
  have hl := total_lower J A N B Y S q R hY hq hR hcop hsize
  have hd : ((pairs J A N B q R).card : ℝ) ≤
      (survivors J A N B q R T D).card + (J.card : ℝ) * T.card + D.card := by
    exact_mod_cast survival_ledger J A N B q R T D
  linarith only [hl, hd]

end PaperP1.CleanPivotPairs
