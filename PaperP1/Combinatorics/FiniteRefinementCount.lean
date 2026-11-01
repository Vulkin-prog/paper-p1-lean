module

public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Cardinal bounds for actual finite images and successive refinements -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRefinementCount

open Finset PaperP1.FiniteCoverCount

theorem image_card_le_of_determined {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, g x = g y → f x = f y) :
    (S.image f).card ≤ (S.image g).card := by
  classical
  have hcover : ∀ b ∈ S.image f, ∃ c ∈ S.image g, b ∈ (S.filter fun x ↦ g x = c).image f := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    exact ⟨g x, mem_image_of_mem g hx, mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩, rfl⟩⟩
  have hcell : ∀ c ∈ S.image g, (((S.filter fun x ↦ g x = c).image f).card : ℝ) ≤ 1 := by
    intro c _
    have hle : ((S.filter fun x ↦ g x = c).image f).card ≤ 1 := by
      apply card_le_one.mpr
      intro b hb b' hb'
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hb'
      exact hdet x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
        ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    exact_mod_cast hle
  have hbound := cardinal_le (S.image f) (S.image g) (fun c ↦ (S.filter fun x ↦ g x = c).image f) 1 hcover hcell
  simpa only [mul_one, Nat.cast_le] using hbound

theorem pairs_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset (α × β)) (A B : ℝ) (hB : 0 ≤ B)
    (hfirst : ((R.image Prod.fst).card : ℝ) ≤ A)
    (hsecond : ∀ a ∈ R.image Prod.fst,
      (((R.filter fun r ↦ r.1 = a).image Prod.snd).card : ℝ) ≤ B) :
    (R.card : ℝ) ≤ A * B := by
  classical
  have hcover : ∀ r ∈ R, ∃ a ∈ R.image Prod.fst, r ∈ R.filter fun r ↦ r.1 = a := by
    intro r hr
    exact ⟨r.1, mem_image_of_mem Prod.fst hr, mem_filter.mpr ⟨hr, rfl⟩⟩
  have hcell : ∀ a ∈ R.image Prod.fst, ((R.filter fun r ↦ r.1 = a).card : ℝ) ≤ B := by
    intro a ha
    have hinj : Set.InjOn (fun r : α × β ↦ r.2) (R.filter fun r ↦ r.1 = a) := by
      intro r hr s hs hrs
      exact Prod.ext ((mem_filter.mp hr).2.trans (mem_filter.mp hs).2.symm) hrs
    rw [← card_image_of_injOn hinj]
    exact hsecond a ha
  exact (cardinal_le R (R.image Prod.fst) (fun a ↦ R.filter fun r ↦ r.1 = a) B hcover hcell).trans
    (mul_le_mul_of_nonneg_right hfirst hB)

theorem pair_image_bound {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ) (A B : ℝ) (hB : 0 ≤ B)
    (hfirst : ((S.image f).card : ℝ) ≤ A)
    (hsecond : ∀ b ∈ S.image f, (((S.filter fun x ↦ f x = b).image g).card : ℝ) ≤ B) :
    ((S.image fun x ↦ (f x, g x)).card : ℝ) ≤ A * B := by
  classical
  let R := S.image fun x ↦ (f x, g x)
  have hfst : R.image Prod.fst = S.image f := by simp only [R, image_image, Function.comp_def]
  apply pairs_card_le R A B hB
  · rw [hfst]
    exact hfirst
  · intro b hb
    have heq : (R.filter fun r ↦ r.1 = b).image Prod.snd = (S.filter fun x ↦ f x = b).image g := by
      ext c
      constructor
      · intro hc
        obtain ⟨r, hr, hrc⟩ := mem_image.mp hc
        obtain ⟨hrS, hrb⟩ := mem_filter.mp hr
        obtain ⟨x, hx, hxr⟩ := mem_image.mp hrS
        exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, (congrArg Prod.fst hxr).trans hrb⟩,
          (congrArg Prod.snd hxr).trans hrc⟩
      · intro hc
        obtain ⟨x, hx, hxc⟩ := mem_image.mp hc
        obtain ⟨hxS, hxb⟩ := mem_filter.mp hx
        exact mem_image.mpr ⟨(f x, g x), mem_filter.mpr ⟨mem_image_of_mem _ hxS, hxb⟩, hxc⟩
    rw [heq]
    exact hsecond b (hfst ▸ hb)

theorem refinement_bound {α β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (S : Finset α) (past : α → β) (next : α → γ) (record : α → δ) (A : ℝ)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, past x = past y → record x = record y → next x = next y)
    (hrecords : ∀ p ∈ S.image past, (((S.filter fun x ↦ past x = p).image record).card : ℝ) ≤ A) :
    ((S.image next).card : ℝ) ≤ ((S.image past).card : ℝ) * A := by
  classical
  apply cardinal_le (S.image next) (S.image past)
    (fun p ↦ (S.filter fun x ↦ past x = p).image next) A
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    exact ⟨past x, mem_image_of_mem past hx,
      mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩, rfl⟩⟩
  · intro p hp
    have hle := image_card_le_of_determined (S.filter fun x ↦ past x = p) next record (by
      intro x hx y hy hrecord
      exact hdet x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
        ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hrecord)
    exact (show (((S.filter fun x ↦ past x = p).image next).card : ℝ) ≤
      (((S.filter fun x ↦ past x = p).image record).card : ℝ) by exact_mod_cast hle).trans (hrecords p hp)

theorem iterate_power_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (past : ℕ → α → β) (N : ℝ) (hN : 0 < N) (v : ℕ) (a : ℕ → ℝ)
    (hzero : ((S.image (past 0)).card : ℝ) ≤ 1)
    (hstep : ∀ k < v, ((S.image (past (k + 1))).card : ℝ) ≤
      ((S.image (past k)).card : ℝ) * N ^ a k)
    (hfinal : Set.InjOn (past v) S) : (S.card : ℝ) ≤ N ^ (∑ k ∈ range v, a k) := by
  classical
  have hbound : ∀ k ≤ v, ((S.image (past k)).card : ℝ) ≤ N ^ (∑ j ∈ range k, a j) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [range_zero, sum_empty, Real.rpow_zero] using hzero
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      calc
        _ ≤ ((S.image (past k)).card : ℝ) * N ^ a k := hstep k (by omega)
        _ ≤ N ^ (∑ j ∈ range k, a j) * N ^ a k :=
          mul_le_mul_of_nonneg_right hprev (Real.rpow_nonneg hN.le _)
        _ = _ := by rw [sum_range_succ, Real.rpow_add hN]
  rw [← card_image_of_injOn hfinal]
  exact hbound v le_rfl

theorem iterate_fin_power_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (past : ℕ → α → β) (N : ℝ) (hN : 0 < N) (v : ℕ) (a : Fin v → ℝ)
    (hzero : ((S.image (past 0)).card : ℝ) ≤ 1)
    (hstep : ∀ k : Fin v, ((S.image (past (k.val + 1))).card : ℝ) ≤
      ((S.image (past k.val)).card : ℝ) * N ^ a k)
    (hfinal : Set.InjOn (past v) S) : (S.card : ℝ) ≤ N ^ (∑ k, a k) := by
  classical
  let b : ℕ → ℝ := fun k ↦ if hk : k < v then a ⟨k, hk⟩ else 0
  have hcount := iterate_power_bound S past N hN v b hzero (by
    intro k hk
    simpa only [b, dite_eq_left hk] using hstep ⟨k, hk⟩) hfinal
  have hsum : (∑ k ∈ range v, b k) = ∑ k, a k := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro k _
    simp only [b, dite_eq_left k.isLt]
  rw [hsum] at hcount
  exact hcount

end PaperP1.FiniteRefinementCount
