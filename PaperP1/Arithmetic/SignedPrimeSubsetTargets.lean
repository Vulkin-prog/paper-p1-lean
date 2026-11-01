module

public import PaperP1.Arithmetic.SmoothModulusHosts
public import PaperP1.Arithmetic.PrimeSubsetCertificates

/-! # Counting actual signed-offset centres from bounded prime subset codes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedPrimeSubsetTargets

open Finset PaperP1.BoundedSubsetWeights PaperP1.LinearKernelFibres

variable {β : Type*} [Fintype β]

def qualifying (P : Finset ℕ) (k X : ℕ) : Finset (Finset ℕ) :=
  (boundedSubsets P k).filter fun T ↦ X ≤ T.prod id

def fibre (G : Finset ℕ) (T : Finset ℕ) (offset : β → ℤ) (f : T → β) : Finset ℕ :=
  G.filter fun n ↦ ∀ p : T, p.val ∣ value n (offset (f p))

def targets (G : Finset ℕ) (P : Finset ℕ) (k X : ℕ) (offset : β → ℤ) : Finset ℕ :=
  (qualifying P k X).biUnion fun T ↦ univ.biUnion fun f : T → β ↦ fibre G T offset f

theorem mem_qualifying (P T : Finset ℕ) (k X : ℕ) :
    T ∈ qualifying P k X ↔ T ⊆ P ∧ T.card ≤ k ∧ X ≤ T.prod id := by
  simp only [qualifying, mem_filter, mem_boundedSubsets, and_assoc]

theorem mem_targets (G : Finset ℕ) (P : Finset ℕ) (k X n : ℕ) (offset : β → ℤ) :
    n ∈ targets G P k X offset ↔ n ∈ G ∧ ∃ T : Finset ℕ,
      T ⊆ P ∧ T.card ≤ k ∧ X ≤ T.prod id ∧
        ∃ f : T → β, ∀ p : T, p.val ∣ value n (offset (f p)) := by
  constructor
  · intro hn
    obtain ⟨T, hT, hn⟩ := mem_biUnion.mp hn
    obtain ⟨f, _, hn⟩ := mem_biUnion.mp hn
    obtain ⟨hTP, hcard, hprod⟩ := (mem_qualifying P T k X).mp hT
    obtain ⟨hnG, hdiv⟩ := mem_filter.mp hn
    exact ⟨hnG, T, hTP, hcard, hprod, f, hdiv⟩
  · rintro ⟨hnG, T, hTP, hcard, hprod, f, hdiv⟩
    exact mem_biUnion.mpr ⟨T, (mem_qualifying P T k X).mpr ⟨hTP, hcard, hprod⟩,
      mem_biUnion.mpr ⟨f, mem_univ _, mem_filter.mpr ⟨hnG, hdiv⟩⟩⟩

omit [Fintype β] in
theorem fibre_count (G : Finset ℕ) (T : Finset ℕ) (X W : ℕ) (offset : β → ℤ) (f : T → β)
    (hG : ∀ n ∈ G, W < n ∧ n ≤ X) (hT : ∀ p ∈ T, p.Prime)
    (hprod : X ≤ T.prod id) (hoffset : ∀ b, (offset b).natAbs ≤ W) :
    (fibre G T offset f).card ≤ 1 := by
  have hcop := PaperP1.PrimeSubsetCertificates.primes_pairwise_coprime T hT
  apply PaperP1.SmoothModulusHosts.fixed_fibre_count (fibre G T offset f) X W
    (fun p : T ↦ offset (f p)) (fun p : T ↦ p.val)
  · intro n hn
    exact hG n (mem_filter.mp hn).1
  · intro p
    exact hoffset (f p)
  · exact hcop
  · rw [show (∏ p : T, p.val) = T.prod id from prod_coe_sort T id]
    exact hprod
  · intro n hn
    exact (mem_filter.mp hn).2

theorem targets_count (G : Finset ℕ) (P : Finset ℕ) (k X W : ℕ) (offset : β → ℤ)
    (hG : ∀ n ∈ G, W < n ∧ n ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hoffset : ∀ b, (offset b).natAbs ≤ W) :
    ((targets G P k X offset).card : ℝ) ≤ weightSum P (Fintype.card β : ℝ) k := by
  have hcard : (targets G P k X offset).card ≤ ∑ T ∈ boundedSubsets P k, (Fintype.card β) ^ T.card := by
    calc
      _ ≤ ∑ T ∈ qualifying P k X, (univ.biUnion fun f : T → β ↦ fibre G T offset f).card := card_biUnion_le
      _ ≤ ∑ T ∈ qualifying P k X, (Fintype.card β) ^ T.card := by
        apply sum_le_sum
        intro T hT
        obtain ⟨hTP, _, hprod⟩ := (mem_qualifying P T k X).mp hT
        calc
          _ ≤ ∑ f : T → β, (fibre G T offset f).card := card_biUnion_le
          _ ≤ ∑ _f : T → β, 1 := sum_le_sum (fun f _ ↦
            fibre_count G T X W offset f hG (fun p hp ↦ hP p (hTP hp)) hprod hoffset)
          _ = _ := by simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_coe, smul_eq_mul, mul_one]
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  unfold weightSum
  exact_mod_cast hcard

end PaperP1.SignedPrimeSubsetTargets
