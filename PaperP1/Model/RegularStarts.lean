module

public import PaperP1.Coding.TwoDefectsInRelation
public import PaperP1.Model.LocalRunRank
public import PaperP1.Model.RelativeSignIndependence
public import PaperP1.Arithmetic.TwoDefectWindows

/-! # The regular dyadic set and its exceptional windows

Regularity means full effective square-class rank, exactly as in main 3.1.
Every irregular window contains two actual (L+1)-defective integers.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularStarts

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
open PaperP1.Model.InfiniteRademacher
open WindowRelationCode TwoDefectsInRelation TwoDefectWindows Finset

local instance regularStartsPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance regularStartsMeasurableF2 : MeasurableSpace F₂ := ⊤

def regularStarts (N L : ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ Module.finrank F₂ (squareClassSpace x L) = L

def irregularStarts (N L : ℕ) : Finset ℕ := dyadicBlock N \ regularStarts N L

theorem mem_regularStarts {N L x : ℕ} : x ∈ regularStarts N L ↔
    x ∈ dyadicBlock N ∧ Module.finrank F₂ (squareClassSpace x L) = L := by
  classical
  simp only [regularStarts, mem_filter]

theorem regularStarts_subset (N L : ℕ) : regularStarts N L ⊆ dyadicBlock N :=
  filter_subset _ _

theorem mem_irregularStarts {N L x : ℕ} : x ∈ irregularStarts N L ↔
    x ∈ dyadicBlock N ∧ Module.finrank F₂ (squareClassSpace x L) ≠ L := by
  classical
  simp only [irregularStarts, mem_sdiff, mem_regularStarts]
  tauto

theorem no_relation_of_regular {N L x : ℕ} (hx : 0 < x)
    (hreg : x ∈ regularStarts N L) :
    Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) = 0 := by
  have hrank := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hx
  have hfull := (mem_regularStarts.mp hreg).2
  omega

theorem irregularStarts_subset_twoDefectWindows {N L : ℕ} (hN : 2 ≤ N) :
    irregularStarts N L ⊆ dyadicTwoDefectWindows N (L + 1) L := by
  classical
  intro x hx
  obtain ⟨hxblock, hxrank⟩ := mem_irregularStarts.mp hx
  have hxlo : N ≤ x := (mem_Ico.mp hxblock).1
  have hxhi : x < 2 * N := (mem_Ico.mp hxblock).2
  have hxpos : 0 < x := by omega
  have hcode : windowRelationCode (x - 1) (L + 1) ≠ ⊥ := by
    intro hbot
    have hrank := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hxpos
    rw [hbot, finrank_bot, add_zero] at hrank
    exact hxrank hrank
  have hdef : ∃ i j : Fin (L + 1), i ≠ j ∧
      DefectivePredicate.HDefective (L + 1) (x - 1 + i.val) ∧
      DefectivePredicate.HDefective (L + 1) (x - 1 + j.val) := by
    by_contra h
    push Not at h
    apply hcode
    apply relation_eq_bot_of_at_most_one_defect
    intro i j hi hj
    by_contra hij
    exact h i j hij hi hj
  obtain ⟨i, j, hij, hi, hj⟩ := hdef
  apply mem_dyadicTwoDefectWindows.mpr
  refine ⟨hxlo, hxhi, x - 1 + i.val, ?_, x - 1 + j.val, ?_, ?_, hi, hj⟩
  · exact mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
  · exact mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩
  · intro heq
    exact hij (Fin.ext (by omega))

theorem card_irregularStarts_le_rpow_eventually
    (E : ℝ) (hE : 0 ≤ E) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ E * Real.log N →
      ((irregularStarts N L).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₁, hN₁⟩ := dyadic_two_defect_windows_le_rpow_eventually E E hE hE ε hε
  refine ⟨max 2 N₁, ?_⟩
  intro N hN L hL
  have hNtwo : 2 ≤ N := by omega
  have hL' : (L : ℝ) ≤ E * Real.log N :=
    (show (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) by norm_num).trans hL
  have h := hN₁ N (by omega) (L + 1) L hL hL'
  exact (by exact_mod_cast card_le_card (irregularStarts_subset_twoDefectWindows
    (L := L) hNtwo) : ((irregularStarts N L).card : ℝ) ≤
      ((dyadicTwoDefectWindows N (L + 1) L).card : ℝ)).trans h

theorem affine_atom_on_regular {N L x : ℕ} (hx : 0 < x)
    (hreg : x ∈ regularStarts N L) (b : Fin L → F₂) :
    infiniteRademacherMeasure.real {ω | RelativeSignIndependence.infiniteStartBits x L ω = b} =
      (2 ^ L : ℝ)⁻¹ :=
  RelativeSignIndependence.infiniteStartBits_atom_uniform hx (no_relation_of_regular hx hreg) b

theorem infiniteMarginal_eq_affine_atom {x L : ℕ} (hL : 0 < L) :
    InfiniteStarts.infiniteMarginal x L = infiniteRademacherMeasure.real
      {ω | RelativeSignIndependence.infiniteStartBits x L ω = startRhs L} := by
  rw [InfiniteStarts.infiniteMarginal_eq_finite (M := x + L) le_rfl,
    exactMarginal_start_eq_affineMass _ _ _ hL,
    RelativeSignIndependence.infiniteStartBits_atom_eq_finite (M := x + L) le_rfl]

theorem marginal_on_regular {N L x : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hreg : x ∈ regularStarts N L) :
    InfiniteStarts.infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ := by
  rw [infiniteMarginal_eq_affine_atom hL]
  exact affine_atom_on_regular hx hreg _

end PaperP1.RegularStarts
