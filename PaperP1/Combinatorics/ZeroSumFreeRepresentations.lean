module

public import PaperP1.Combinatorics.UniformTransversal
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring

/-! # Counting unordered zero-sum-free representations by a small transversal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ZeroSumFreeRepresentations

open Finset

variable {W : Type*} [AddCommGroup W] [DecidableEq W]

def ZeroSumFree (A : Finset W) : Prop :=
  ∀ B ⊆ A, (∑ a ∈ B, a) = 0 → B = ∅

def representations (S : Finset W) (j : ℕ) (α : W) : Finset (Finset W) := by
  classical
  exact (S.powersetCard j).filter fun A ↦ ZeroSumFree A ∧ (∑ a ∈ A, a) = α

def NoDisjointSums (S : Finset W) (d t : ℕ) : Prop :=
  ∀ α : W, α ≠ 0 → ∀ E : Finset (Finset W),
    (∀ A ∈ E, A ⊆ S ∧ 1 ≤ A.card ∧ A.card ≤ d ∧ (∑ a ∈ A, a) = α) →
    E.card = t → ¬(↑E : Set (Finset W)).PairwiseDisjoint id

theorem mem_representations {S A : Finset W} {j : ℕ} {α : W} :
    A ∈ representations S j α ↔ A ⊆ S ∧ A.card = j ∧ ZeroSumFree A ∧ (∑ a ∈ A, a) = α := by
  classical
  simp only [representations, mem_filter, mem_powersetCard, and_assoc]

omit [DecidableEq W] in
theorem zeroSumFree_mono {A B : Finset W} (hA : ZeroSumFree A) (hBA : B ⊆ A) : ZeroSumFree B := by
  intro C hCB hzero
  exact hA C (hCB.trans hBA) hzero

theorem erase_representation {S A : Finset W} {j : ℕ} {α x : W}
    (hA : A ∈ representations S j α) (hx : x ∈ A) :
    A.erase x ∈ representations S (j - 1) (α - x) := by
  obtain ⟨hAS, hcard, hfree, hsum⟩ := mem_representations.mp hA
  apply mem_representations.mpr
  refine ⟨(erase_subset x A).trans hAS, ?_, zeroSumFree_mono hfree (erase_subset x A), ?_⟩
  · rw [card_erase_of_mem hx, hcard]
  · apply eq_sub_iff_add_eq.mpr
    simpa only [id_eq, hsum] using sum_erase_add A id hx

theorem residual_ne_zero {S A : Finset W} {j : ℕ} {α x : W}
    (hA : A ∈ representations S j α) (hj : 2 ≤ j) (hx : x ∈ A) : α - x ≠ 0 := by
  intro hzero
  obtain ⟨_, hcard, hfree, _⟩ := mem_representations.mp hA
  have herase := mem_representations.mp (erase_representation hA hx)
  have hempty : A.erase x = ∅ := hfree _ (erase_subset x A) (herase.2.2.2.trans hzero)
  have hc := card_erase_add_one hx
  rw [hempty, card_empty, hcard] at hc
  omega

theorem representations_one_card_le (S : Finset W) (α : W) :
    (representations S 1 α).card ≤ 1 := by
  have hsub : representations S 1 α ⊆ {{α}} := by
    intro A hA
    obtain ⟨_, hcard, _, hsum⟩ := mem_representations.mp hA
    obtain ⟨a, rfl⟩ := card_eq_one.mp hcard
    have ha : a = α := by simpa only [sum_singleton] using hsum
    simp only [mem_singleton]
    exact congrArg singleton ha
  exact (card_le_card hsub).trans_eq (card_singleton _)

theorem representation_cover (S : Finset W) (j : ℕ) (α : W) (H : Finset W)
    (hH : ∀ A ∈ representations S j α, (A ∩ H).Nonempty) :
    representations S j α ⊆ H.biUnion
      (fun x ↦ (representations S (j - 1) (α - x)).image (insert x)) := by
  intro A hA
  obtain ⟨x, hx⟩ := hH A hA
  obtain ⟨hxA, hxH⟩ := mem_inter.mp hx
  exact mem_biUnion.mpr ⟨x, hxH,
    mem_image.mpr ⟨A.erase x, erase_representation hA hxA, insert_erase hxA⟩⟩

/-- The constant retains t-1 from the exact disjoint-family bound. -/
theorem representations_card_le (S : Finset W) (d t : ℕ)
    (hno : NoDisjointSums S d t) (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d)
    (α : W) (hα : α ≠ 0) :
    (representations S j α).card ≤ j.factorial * (t - 1) ^ (j - 1) := by
  classical
  induction j generalizing α with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst j
      simpa only [Nat.zero_add, Nat.factorial_one, Nat.sub_self, pow_zero, mul_one] using
        representations_one_card_le S α
    have hjpos : 1 ≤ j := by omega
    let F := representations S (j + 1) α
    have hcard : ∀ A ∈ F, A.card = j + 1 := fun A hA ↦ (mem_representations.mp hA).2.1
    have hnomatch : ∀ E ⊆ F, E.card = t → ¬(↑E : Set (Finset W)).PairwiseDisjoint id := by
      intro E hEF hEt
      apply hno α hα E
      · intro A hAE
        obtain ⟨hAS, hc, _, hs⟩ := mem_representations.mp (hEF hAE)
        exact ⟨hAS, by omega, by omega, hs⟩
      · exact hEt
    obtain ⟨H, hHF, hHcard, hhit⟩ := UniformTransversal.exists_transversal F (j + 1) t
      (by omega) hcard hnomatch
    have hnonzero (x : W) (hx : x ∈ H) : α - x ≠ 0 := by
      obtain ⟨A, hAF, hxA⟩ := mem_biUnion.mp (hHF hx)
      exact residual_ne_zero hAF (by omega) hxA
    have hcover := representation_cover S (j + 1) α H hhit
    simp only [Nat.add_sub_cancel_right] at hcover
    have hsmall (x : W) (hx : x ∈ H) :
        (representations S j (α - x)).card ≤ j.factorial * (t - 1) ^ (j - 1) :=
      ih hjpos (by omega) (α - x) (hnonzero x hx)
    have hpow : (t - 1) ^ (j - 1) * (t - 1) = (t - 1) ^ j := by
      rw [← pow_succ, Nat.sub_add_cancel hjpos]
    calc
      _ ≤ (H.biUnion (fun x ↦ (representations S j (α - x)).image (insert x))).card := card_le_card hcover
      _ ≤ ∑ x ∈ H, ((representations S j (α - x)).image (insert x)).card := card_biUnion_le
      _ ≤ ∑ x ∈ H, (representations S j (α - x)).card := sum_le_sum fun _ _ ↦ card_image_le
      _ ≤ ∑ _x ∈ H, j.factorial * (t - 1) ^ (j - 1) := sum_le_sum hsmall
      _ = H.card * (j.factorial * (t - 1) ^ (j - 1)) := by simp
      _ ≤ ((j + 1) * (t - 1)) * (j.factorial * (t - 1) ^ (j - 1)) :=
        Nat.mul_le_mul_right _ hHcard
      _ = (j + 1).factorial * (t - 1) ^ j := by
        rw [Nat.factorial_succ]
        calc
          _ = (j + 1) * j.factorial * ((t - 1) ^ (j - 1) * (t - 1)) := by ring
          _ = _ := by rw [hpow]

end PaperP1.ZeroSumFreeRepresentations
