module

public import PaperP1.Algebra.NonnegativePowerDifference
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-! # Actual sequential fresh paths, with exact branch sums and finite power budgets

Lists store added coordinates in reverse chronological order. Their source
union and their actual multiplicities do not depend on this storage choice.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SequentialBranchingPaths

open Finset

variable {ι : Type*} [DecidableEq ι]

def old (A : Finset ι) (xs : List ι) : Finset ι := A ∪ xs.toFinset

def paths (next : Finset ι → Finset ι) (A : Finset ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => (paths next A k).biUnion fun xs ↦ (next (old A xs)).image fun z ↦ z :: xs

theorem length (next : Finset ι → Finset ι) (A : Finset ι) (k : ℕ)
    (xs : List ι) (hxs : xs ∈ paths next A k) : xs.length = k := by
  induction k generalizing xs with
  | zero => rw [mem_singleton.mp hxs]; rfl
  | succ k ih =>
    obtain ⟨ys, hys, himage⟩ := mem_biUnion.mp hxs
    obtain ⟨z, _hz, rfl⟩ := mem_image.mp himage
    rw [List.length_cons, ih ys hys]


theorem old_cons (A : Finset ι) (xs : List ι) (z : ι) : old A (z :: xs) = insert z (old A xs) := by
  simp only [old, List.toFinset_cons, union_insert]

theorem data (G : Finset ι) (next : Finset ι → Finset ι) (A : Finset ι) (hA : A ⊆ G)
    (hnext : ∀ S ⊆ G, next S ⊆ G \ S) (k : ℕ) (xs : List ι) (hxs : xs ∈ paths next A k) :
    xs.length = k ∧ xs.Nodup ∧ Disjoint A xs.toFinset ∧ old A xs ⊆ G := by
  induction k generalizing xs with
  | zero =>
    have hx : xs = [] := mem_singleton.mp hxs
    subst xs
    simpa [old] using hA
  | succ k ih =>
    obtain ⟨ys, hys, himage⟩ := mem_biUnion.mp hxs
    obtain ⟨z, hz, rfl⟩ := mem_image.mp himage
    obtain ⟨hlen, hnodup, hdis, hsub⟩ := ih ys hys
    obtain ⟨hzG, hzold⟩ := mem_sdiff.mp (hnext (old A ys) hsub hz)
    have hzA : z ∉ A := fun h ↦ hzold (mem_union_left _ h)
    have hzys : z ∉ ys.toFinset := fun h ↦ hzold (mem_union_right _ h)
    refine ⟨by simp only [List.length_cons, hlen], List.nodup_cons.mpr ⟨by simpa using hzys, hnodup⟩, ?_, ?_⟩
    · rw [List.toFinset_cons, disjoint_insert_right]
      exact ⟨hzA, hdis⟩
    · rw [old_cons]
      exact insert_subset_iff.mpr ⟨hzG, hsub⟩

theorem sum_succ {M : Type*} [AddCommMonoid M] (next : Finset ι → Finset ι) (A : Finset ι)
    (k : ℕ) (f : List ι → M) :
    (∑ xs ∈ paths next A (k + 1), f xs) =
      ∑ xs ∈ paths next A k, ∑ z ∈ next (old A xs), f (z :: xs) := by
  rw [paths, sum_biUnion]
  · apply sum_congr rfl
    intro xs _
    exact sum_image (fun _ _ _ _ h ↦ (List.cons.inj h).1)
  · intro xs _ ys _ hne
    apply disjoint_left.mpr
    intro zs hzxs hzys
    obtain ⟨x, _hx, hxeq⟩ := mem_image.mp hzxs
    obtain ⟨y, _hy, hyeq⟩ := mem_image.mp hzys
    exact hne (List.cons.inj (hxeq.trans hyeq.symm)).2

theorem card_succ (next : Finset ι → Finset ι) (A : Finset ι) (k : ℕ) :
    ((paths next A (k + 1)).card : ℝ) =
      ∑ xs ∈ paths next A k, ((next (old A xs)).card : ℝ) := by
  simpa only [sum_const, nsmul_eq_mul, mul_one] using sum_succ next A k (fun _ ↦ (1 : ℝ))

theorem old_card (A : Finset ι) (xs : List ι) : (old A xs).card ≤ A.card + xs.length :=
  (card_union_le _ _).trans (Nat.add_le_add_left (List.toFinset_card_le xs) _)

theorem card_bounds (G : Finset ι) (next : Finset ι → Finset ι) (A : Finset ι) (m : ℕ)
    (hA : A ⊆ G) (hnext : ∀ S ⊆ G, next S ⊆ G \ S) (D : ℝ)
    (hDG : D ≤ G.card)
    (hcount : ∀ S ⊆ G, S.card ≤ A.card + m → (G.card : ℝ) - D ≤ (next S).card) :
    ∀ k ≤ m, ((G.card : ℝ) - D) ^ k ≤ (paths next A k).card ∧
      ((paths next A k).card : ℝ) ≤ (G.card : ℝ) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp only [paths, card_singleton, Nat.cast_one, pow_zero, le_refl, and_self]
  | succ k ih =>
    intro hkm
    obtain ⟨hlo, hhi⟩ := ih (by omega)
    have hbounds (xs : List ι) (hxs : xs ∈ paths next A k) :
        (G.card : ℝ) - D ≤ (next (old A xs)).card ∧ ((next (old A xs)).card : ℝ) ≤ G.card := by
      have hd := data G next A hA hnext k xs hxs
      exact ⟨hcount (old A xs) hd.2.2.2 (by have hh := old_card A xs; rw [hd.1] at hh; omega),
        by exact_mod_cast card_le_card ((hnext _ hd.2.2.2).trans sdiff_subset)⟩
    rw [card_succ]
    constructor
    · calc
        _ = ((G.card : ℝ) - D) ^ k * ((G.card : ℝ) - D) := pow_succ _ _
        _ ≤ ((paths next A k).card : ℝ) * ((G.card : ℝ) - D) :=
          mul_le_mul_of_nonneg_right hlo (sub_nonneg.mpr hDG)
        _ ≤ _ := by
          rw [← nsmul_eq_mul, ← sum_const]
          exact sum_le_sum fun xs hxs ↦ (hbounds xs hxs).1
    · calc
        _ ≤ ∑ _xs ∈ paths next A k, (G.card : ℝ) := sum_le_sum fun xs hxs ↦ (hbounds xs hxs).2
        _ = ((paths next A k).card : ℝ) * G.card := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (G.card : ℝ) ^ k * G.card := mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg _)
        _ = _ := (pow_succ _ _).symm

theorem probability_exact (G : Finset ι) (next : Finset ι → Finset ι) (A : Finset ι)
    (hA : A ⊆ G) (hnext : ∀ S ⊆ G, next S ⊆ G \ S) (q : Finset ι → ℝ) (p : ℝ)
    (hstep : ∀ S ⊆ G, ∀ z ∈ next S, q (insert z S) = p * q S)
    (k : ℕ) (xs : List ι) (hxs : xs ∈ paths next A k) : q (old A xs) = p ^ k * q A := by
  induction k generalizing xs with
  | zero =>
    have hx : xs = [] := mem_singleton.mp hxs
    subst xs
    simp only [old, List.toFinset_nil, union_empty, pow_zero, one_mul]
  | succ k ih =>
    obtain ⟨ys, hys, himage⟩ := mem_biUnion.mp hxs
    obtain ⟨z, hz, rfl⟩ := mem_image.mp himage
    rw [old_cons, hstep (old A ys) (data G next A hA hnext k ys hys).2.2.2 z hz, ih ys hys, pow_succ]
    rw [← mul_assoc, mul_comm p (p ^ k)]

theorem mass_exact (G : Finset ι) (next : Finset ι → Finset ι) (A : Finset ι)
    (hA : A ⊆ G) (hnext : ∀ S ⊆ G, next S ⊆ G \ S) (q : Finset ι → ℝ) (p : ℝ)
    (hstep : ∀ S ⊆ G, ∀ z ∈ next S, q (insert z S) = p * q S) (k : ℕ) :
    (∑ xs ∈ paths next A k, q (old A xs)) = (paths next A k).card * (p ^ k * q A) := by
  calc
    _ = ∑ _xs ∈ paths next A k, p ^ k * q A :=
      sum_congr rfl (fun xs hxs ↦ probability_exact G next A hA hnext q p hstep k xs hxs)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem card_error (G : Finset ι) (next : Finset ι → Finset ι) (A : Finset ι) (m : ℕ)
    (hA : A ⊆ G) (hnext : ∀ S ⊆ G, next S ⊆ G \ S) (D : ℝ)
    (hD : 0 ≤ D) (hDG : D ≤ G.card)
    (hcount : ∀ S ⊆ G, S.card ≤ A.card + m → (G.card : ℝ) - D ≤ (next S).card)
    (k : ℕ) (hkm : k ≤ m) :
    |((paths next A k).card : ℝ) - (G.card : ℝ) ^ k| ≤ D * k * (G.card : ℝ) ^ (k - 1) := by
  obtain ⟨hlo, hhi⟩ := card_bounds G next A m hA hnext D hDG hcount k hkm
  have hp := NonnegativePowerDifference.bound (G.card : ℝ) ((G.card : ℝ) - D) G.card
    (Nat.cast_nonneg _) (sub_nonneg.mpr hDG) le_rfl (sub_le_self _ hD) k
  rw [show (G.card : ℝ) - ((G.card : ℝ) - D) = D by ring, abs_of_nonneg hD] at hp
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  calc
    _ = (G.card : ℝ) ^ k - (paths next A k).card := by ring
    _ ≤ (G.card : ℝ) ^ k - ((G.card : ℝ) - D) ^ k := sub_le_sub_left hlo _
    _ ≤ |(G.card : ℝ) ^ k - ((G.card : ℝ) - D) ^ k| := le_abs_self _
    _ ≤ _ := hp

theorem mass_error (G : Finset ι) (next : Finset ι → Finset ι) (A : Finset ι) (m : ℕ)
    (hA : A ⊆ G) (hnext : ∀ S ⊆ G, next S ⊆ G \ S) (D : ℝ)
    (hD : 0 ≤ D) (hDG : D ≤ G.card)
    (hcount : ∀ S ⊆ G, S.card ≤ A.card + m → (G.card : ℝ) - D ≤ (next S).card)
    (q : Finset ι → ℝ) (p : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q A)
    (hstep : ∀ S ⊆ G, ∀ z ∈ next S, q (insert z S) = p * q S)
    (k : ℕ) (hkm : k ≤ m) :
    |(∑ xs ∈ paths next A k, q (old A xs)) - ((G.card : ℝ) * p) ^ k * q A| ≤
      (p ^ k * q A) * (D * k * (G.card : ℝ) ^ (k - 1)) := by
  rw [mass_exact G next A hA hnext q p hstep k, mul_pow]
  have heq : ((paths next A k).card : ℝ) * (p ^ k * q A) - (G.card : ℝ) ^ k * p ^ k * q A =
      (p ^ k * q A) * (((paths next A k).card : ℝ) - (G.card : ℝ) ^ k) := by ring
  rw [heq, abs_mul, abs_of_nonneg (mul_nonneg (pow_nonneg hp _) hq)]
  exact mul_le_mul_of_nonneg_left (card_error G next A m hA hnext D hD hDG hcount k hkm)
    (mul_nonneg (pow_nonneg hp _) hq)

end PaperP1.SequentialBranchingPaths
