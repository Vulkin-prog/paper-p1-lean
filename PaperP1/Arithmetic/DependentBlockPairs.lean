module

public import PaperP1.Arithmetic.EffectiveWindowLists
public import PaperP1.Affine.PairFourierIntersection
public import Mathlib.Tactic.FinCases

/-! # Actual pairs with a nonzero common effective vector, including equal centres -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentBlockPairs

open Finset PaperP1.Arithmetic

def Dependent (blocks : Fin 2 → ℕ → Finset ℕ) (p : ℕ × ℕ) : Prop :=
  ∃ u : ℕ →₀ F₂, u ≠ 0 ∧ u ∈ PaperP1.FiniteEvenSquareClasses.space (blocks 0 p.1) ∧
    u ∈ PaperP1.FiniteEvenSquareClasses.space (blocks 1 p.2)

def pairs (G : Finset ℕ) (blocks : Fin 2 → ℕ → Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (G ×ˢ G).filter (Dependent blocks)

def offDiagonal (G : Finset ℕ) (blocks : Fin 2 → ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  (pairs G blocks).filter fun p ↦ p.1 ≠ p.2

def diagonal (G : Finset ℕ) (blocks : Fin 2 → ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  (pairs G blocks).filter fun p ↦ p.1 = p.2

def active (G : Finset ℕ) (block : ℕ → Finset ℕ) : Finset ℕ := by
  classical
  exact G.filter fun x ↦ PaperP1.FiniteEvenSquareClasses.space (block x) ≠ ⊥

def tuple (p : ℕ × ℕ) : Fin 2 → ℕ := ![p.1, p.2]

theorem dependent_iff_intersection (blocks : Fin 2 → ℕ → Finset ℕ) (p : ℕ × ℕ) :
    Dependent blocks p ↔
      PaperP1.FiniteEvenSquareClasses.space (blocks 0 p.1) ⊓
        PaperP1.FiniteEvenSquareClasses.space (blocks 1 p.2) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨u, hne, h₀, h₁⟩
    exact ⟨u, ⟨h₀, h₁⟩, hne⟩
  · rintro ⟨u, hu, hne⟩
    exact ⟨u, hne, hu.1, hu.2⟩

theorem tuple_injective : Function.Injective tuple := by
  intro p q hpq
  apply Prod.ext
  · have h := congrFun hpq 0
    simpa only [tuple, Matrix.cons_val_zero] using h
  · have h := congrFun hpq 1
    simpa only [tuple, Matrix.cons_val_one, Matrix.cons_val_zero] using h

theorem off_diagonal_in_effective (G : Finset ℕ) (blocks : Fin 2 → ℕ → Finset ℕ)
    (p : ℕ × ℕ) (hp : p ∈ offDiagonal G blocks) :
    tuple p ∈ PaperP1.EffectiveWindowLists.lists G blocks ∅ := by
  classical
  obtain ⟨hpdep, hne⟩ := mem_filter.mp hp
  obtain ⟨hpG, u, hu, h₀, h₁⟩ := mem_filter.mp hpdep
  obtain ⟨hp₀, hp₁⟩ := mem_product.mp hpG
  apply (PaperP1.EffectiveWindowLists.mem_lists G blocks ∅ (tuple p)).mpr
  refine ⟨?_, ?_, (fun _ ↦ u), ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hp₀
    · exact hp₁
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [tuple]
  · intro i
    fin_cases i
    · exact ⟨h₀, hu⟩
    · exact ⟨h₁, hu⟩
  · rw [Fin.sum_univ_two, PaperP1.PairFourierIntersection.self_add]
    exact Submodule.zero_mem _

theorem off_diagonal_count (G : Finset ℕ) (blocks : Fin 2 → ℕ → Finset ℕ) :
    (offDiagonal G blocks).card ≤ (PaperP1.EffectiveWindowLists.lists G blocks ∅).card := by
  apply card_le_card_of_injOn tuple
  · exact fun p hp ↦ off_diagonal_in_effective G blocks p hp
  · exact fun _ _ _ _ hpq ↦ tuple_injective hpq

theorem diagonal_count (G : Finset ℕ) (blocks : Fin 2 → ℕ → Finset ℕ) :
    (diagonal G blocks).card ≤ (active G (blocks 0)).card := by
  classical
  apply card_le_card_of_injOn Prod.fst
  · intro p hp
    obtain ⟨hpdep, _⟩ := mem_filter.mp hp
    obtain ⟨hpG, u, hne, h₀, _⟩ := mem_filter.mp hpdep
    refine mem_filter.mpr ⟨(mem_product.mp hpG).1, ?_⟩
    exact (Submodule.ne_bot_iff _).mpr ⟨u, h₀, hne⟩
  · intro p hp q hq hpq
    have hpdiag := (mem_filter.mp hp).2
    have hqdiag := (mem_filter.mp hq).2
    exact Prod.ext hpq (hpdiag.symm.trans (hpq.trans hqdiag))

theorem split_count (G : Finset ℕ) (blocks : Fin 2 → ℕ → Finset ℕ) :
    (pairs G blocks).card ≤ (offDiagonal G blocks).card + (diagonal G blocks).card := by
  classical
  have hcover : pairs G blocks ⊆ offDiagonal G blocks ∪ diagonal G blocks := by
    intro p hp
    by_cases h : p.1 = p.2
    · exact mem_union_right _ (mem_filter.mpr ⟨hp, h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, h⟩)
  exact (card_le_card hcover).trans (card_union_le _ _)

end PaperP1.DependentBlockPairs
