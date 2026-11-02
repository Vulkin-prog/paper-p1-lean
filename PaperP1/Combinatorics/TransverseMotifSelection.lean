module

public import PaperP1.Arithmetic.TransverseMotifs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! # Three bounded motifs selected from a macroscopic disjoint population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TransverseMotifSelection

open Finset PaperP1.TransverseMotifs

theorem total_size {L : ℕ} (F : Finset (Finset (Vertex L)))
    (hdisj : (↑F : Set (Finset (Vertex L))).PairwiseDisjoint id) :
    ∑ E ∈ F, E.card ≤ 3 * (L + 1) := by
  have hh := card_le_card (subset_univ (F.biUnion id))
  calc
    _ = (F.biUnion id).card := by simpa only [id_eq] using (card_biUnion hdisj).symm
    _ ≤ _ := by simpa only [card_univ, Fintype.card_prod, Fintype.card_fin] using hh

theorem small_population {L : ℕ} (F : Finset (Finset (Vertex L)))
    (hdisj : (↑F : Set (Finset (Vertex L))).PairwiseDisjoint id)
    (η : ℝ) (hη : 0 < η) (d : ℕ) (hd : 6 ≤ η * (d + 1))
    (hpop : η * (L + 1) ≤ (F.card : ℝ)) :
    η * (L + 1) / 2 ≤ ((F.filter fun E ↦ E.card ≤ d).card : ℝ) := by
  let G := F.filter fun E ↦ d < E.card
  have hlarge : (d + 1) * G.card ≤ 3 * (L + 1) := by
    calc
      _ = ∑ _E ∈ G, (d + 1) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ E ∈ G, E.card := sum_le_sum (fun E hE ↦ by have hh := (mem_filter.mp hE).2; omega)
      _ ≤ ∑ E ∈ F, E.card := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
      _ ≤ 3 * (L + 1) := total_size F hdisj
  have hlargeR : ((d : ℝ) + 1) * G.card ≤ 3 * (L + 1) := by exact_mod_cast hlarge
  have hmult := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg G.card : (0 : ℝ) ≤ G.card)
  have hbudget := mul_le_mul_of_nonneg_left hlargeR hη.le
  have hupper : (G.card : ℝ) ≤ η * (L + 1) / 2 := by nlinarith only [hmult, hbudget]
  have hpartition : (F.filter fun E ↦ E.card ≤ d).card + G.card = F.card := by
    simpa only [G, Nat.not_le] using card_filter_add_card_filter_not (s := F) (p := fun E ↦ E.card ≤ d)
  have hpartR : ((F.filter fun E ↦ E.card ≤ d).card : ℝ) + G.card = F.card := by exact_mod_cast hpartition
  linarith only [hpop, hupper, hpartR]

theorem select_three {L : ℕ} (F : Finset (Finset (Vertex L)))
    (hdisj : (↑F : Set (Finset (Vertex L))).PairwiseDisjoint id)
    (η : ℝ) (hη : 0 < η) (d : ℕ) (hd : 6 ≤ η * (d + 1))
    (hpop : η * (L + 1) ≤ (F.card : ℝ)) (hwidth : 6 ≤ η * (L + 1)) :
    ∃ E : Fin 3 → Finset (Vertex L),
      (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint E ∧
      ∀ i, E i ∈ F ∧ (E i).card ≤ d := by
  have hsmall := small_population F hdisj η hη d hd hpop
  have hthree : 3 ≤ (F.filter fun E ↦ E.card ≤ d).card := by
    have hh : (3 : ℝ) ≤ ((F.filter fun E ↦ E.card ≤ d).card : ℝ) := by linarith
    exact_mod_cast hh
  obtain ⟨I, hI, hcard⟩ := exists_subset_card_eq hthree
  let e : Fin 3 ≃ I := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hcard)).symm
  let E : Fin 3 → Finset (Vertex L) := fun i ↦ (e i).val
  have hE (i : Fin 3) : E i ∈ F ∧ (E i).card ≤ d := mem_filter.mp (hI (e i).property)
  refine ⟨E, ?_, hE⟩
  intro i _hi j _hj hij
  have hne : E i ≠ E j := fun hh ↦ hij (e.injective (Subtype.ext hh))
  exact hdisj (hE i).1 (hE j).1 hne

end PaperP1.TransverseMotifSelection
