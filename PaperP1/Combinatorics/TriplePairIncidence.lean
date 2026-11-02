module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Lean.Elab.Tactic.Omega

/-! # Exact incidence count: a set with a distinguished member is its complement and that member -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.TriplePairIncidence

open Finset

variable {ι A : Type*} [DecidableEq ι] [AddCommMonoid A]

theorem erased_sum (G : Finset ι) (r : ℕ) (f : Finset ι → ι → A) :
    (∑ T ∈ G.powersetCard (r + 1), ∑ z ∈ T, f (T.erase z) z) =
      ∑ e ∈ G.powersetCard r, ∑ z ∈ G \ e, f e z := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun t _ ↦ (⟨t.1.erase t.2, t.2⟩ : (Σ _ : Finset ι, ι)))
  · intro t ht
    obtain ⟨hT, hz⟩ := mem_sigma.mp ht
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
    apply mem_sigma.mpr
    refine ⟨mem_powersetCard.mpr ⟨(erase_subset _ _).trans hsub, ?_⟩, ?_⟩
    · change (t.1.erase t.2).card = r
      have he := card_erase_add_one hz
      omega
    · exact mem_sdiff.mpr ⟨hsub hz, notMem_erase _ _⟩
  · intro t ht u hu htu
    obtain ⟨_, hz⟩ := mem_sigma.mp ht
    obtain ⟨_, hw⟩ := mem_sigma.mp hu
    have he : t.1.erase t.2 = u.1.erase u.2 := congrArg Sigma.fst htu
    have hzw : t.2 = u.2 := congrArg Sigma.snd htu
    have hT : t.1 = u.1 := by
      calc
        t.1 = insert t.2 (t.1.erase t.2) := (insert_erase hz).symm
        _ = insert u.2 (u.1.erase u.2) := by rw [he, hzw]
        _ = u.1 := insert_erase hw
    exact Sigma.ext hT (heq_of_eq hzw)
  · intro e he
    obtain ⟨hecard, hz⟩ := mem_sigma.mp he
    obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp hecard
    obtain ⟨hzG, hze⟩ := mem_sdiff.mp hz
    refine ⟨⟨insert e.2 e.1, e.2⟩, mem_sigma.mpr ⟨?_, mem_insert_self _ _⟩, ?_⟩
    · apply mem_powersetCard.mpr
      exact ⟨insert_subset hzG hesub, by rw [card_insert_of_notMem hze, hecard]⟩
    · simp only [erase_insert hze]
  · intro t ht
    rfl

theorem restricted_erased_sum_le (G : Finset ι) (r : ℕ) (F : Finset (Finset ι))
    (hF : F ⊆ G.powersetCard (r + 1)) (f : Finset ι → ι → ℝ)
    (hf : ∀ e z, 0 ≤ f e z) (R : Finset ι → ι → Prop) [∀ e, DecidablePred (R e)]
    (hR : ∀ T ∈ F, ∀ z ∈ T, f (T.erase z) z ≠ 0 → R (T.erase z) z) :
    (∑ T ∈ F, ∑ z ∈ T, f (T.erase z) z) ≤
      ∑ e ∈ G.powersetCard r, ∑ z ∈ G \ e, if R e z then f e z else 0 := by
  classical
  calc
    _ = ∑ T ∈ F, ∑ z ∈ T, if R (T.erase z) z then f (T.erase z) z else 0 := by
      apply sum_congr rfl
      intro T hT
      apply sum_congr rfl
      intro z hz
      by_cases hr : R (T.erase z) z
      · rw [ite_eq_left hr]
      · have hzero : f (T.erase z) z = 0 := by
          by_contra hn
          exact hr (hR T hT z hz hn)
        simp only [hzero, ite_self]
    _ ≤ ∑ T ∈ G.powersetCard (r + 1), ∑ z ∈ T,
          if R (T.erase z) z then f (T.erase z) z else 0 := by
      apply sum_le_sum_of_subset_of_nonneg hF
      intro T _ _
      apply sum_nonneg
      intro z _
      split_ifs
      · exact hf _ _
      · exact le_rfl
    _ = _ := erased_sum G r (fun e z ↦ if R e z then f e z else 0)

end PaperP1.TriplePairIncidence
