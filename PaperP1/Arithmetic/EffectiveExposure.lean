module

public import PaperP1.Arithmetic.EffectiveWindowLists
public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Data.Fintype.EquivFin

/-! # Actual finite exposure populations and extension fibres

Each step exposes a nonempty new group with nonzero own-space projections
whose sum lies in the full span of the previously exposed blocks.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveExposure

open Finset PaperP1.Arithmetic

def Code (r : ℕ) := Σ k : Fin r, Fin r ≃ (Fin k.val ⊕ Fin (r - k.val))

instance (r : ℕ) : Fintype (Code r) := by unfold Code; infer_instance

def leftCentres {r : ℕ} (c : Code r) (n : Fin r → ℕ) : Fin c.1.val → ℕ :=
  fun i ↦ n (c.2.symm (Sum.inl i))

def rightCentres {r : ℕ} (c : Code r) (n : Fin r → ℕ) : Fin (r - c.1.val) → ℕ :=
  fun i ↦ n (c.2.symm (Sum.inr i))

def leftBlocks {r : ℕ} (c : Code r) (blocks : Fin r → ℕ → Finset ℕ) : Fin c.1.val → ℕ → Finset ℕ :=
  fun i ↦ blocks (c.2.symm (Sum.inl i))

def rightBlocks {r : ℕ} (c : Code r) (blocks : Fin r → ℕ → Finset ℕ) : Fin (r - c.1.val) → ℕ → Finset ℕ :=
  fun i ↦ blocks (c.2.symm (Sum.inr i))

def oldValues {r : ℕ} (c : Code r) (blocks : Fin r → ℕ → Finset ℕ) (old : Fin c.1.val → ℕ) : Finset ℕ :=
  univ.biUnion fun i ↦ leftBlocks c blocks i (old i)

def Extension {r : ℕ} (c : Code r) (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ) : Prop :=
  ∃ u : Fin (r - c.1.val) → (ℕ →₀ F₂),
    (∀ i, u i ∈ PaperP1.FiniteEvenSquareClasses.space (rightBlocks c blocks i (rightCentres c n i)) ∧ u i ≠ 0) ∧
      (∑ i, u i) ∈ PaperP1.OldSpaceProjection.oldSpace (oldValues c blocks (leftCentres c n))

def Exposable {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ) : Prop :=
  if r = 0 then True else
    ∃ c : Code r, Exposable (leftBlocks c blocks) (leftCentres c n) ∧ Extension c blocks n
termination_by r
decreasing_by exact c.1.isLt

def population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧ Exposable blocks n

def cell {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (c : Code r) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧
    Exposable (leftBlocks c blocks) (leftCentres c n) ∧ Extension c blocks n

theorem mem_population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ) :
    n ∈ population G blocks ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧ Exposable blocks n := by
  classical
  simp only [population, mem_filter, Fintype.mem_piFinset]

theorem mem_cell {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (c : Code r) (n : Fin r → ℕ) :
    n ∈ cell G blocks c ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧
      Exposable (leftBlocks c blocks) (leftCentres c n) ∧ Extension c blocks n := by
  classical
  simp only [cell, mem_filter, Fintype.mem_piFinset]

theorem exposable_zero (blocks : Fin 0 → ℕ → Finset ℕ) (n : Fin 0 → ℕ) : Exposable blocks n := by
  rw [Exposable]
  trivial

theorem exposable_pos {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ) (hr : 0 < r) :
    Exposable blocks n ↔ ∃ c : Code r, Exposable (leftBlocks c blocks) (leftCentres c n) ∧ Extension c blocks n := by
  rw [Exposable, ite_eq_right (by omega : r ≠ 0)]

theorem determined {r : ℕ} (c : Code r) (n m : Fin r → ℕ)
    (hpre : leftCentres c n = leftCentres c m) (hsuf : rightCentres c n = rightCentres c m) : n = m := by
  have heq : ∀ z : Fin c.1.val ⊕ Fin (r - c.1.val), n (c.2.symm z) = m (c.2.symm z) := by
    intro z
    cases z with
    | inl i => exact congrFun hpre i
    | inr i => exact congrFun hsuf i
  funext i
  simpa only [Equiv.symm_apply_apply] using heq (c.2 i)

theorem prefix_population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (c : Code r) (n : Fin r → ℕ) (hn : n ∈ cell G blocks c) :
    leftCentres c n ∈ population G (leftBlocks c blocks) := by
  obtain ⟨hnG, hinj, hpre, _⟩ := (mem_cell G blocks c n).mp hn
  apply (mem_population G (leftBlocks c blocks) (leftCentres c n)).mpr
  refine ⟨fun i ↦ hnG _, ?_, hpre⟩
  intro i j hij
  exact Sum.inl.inj (c.2.symm.injective (hinj hij))

theorem suffix_effective {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (c : Code r) (n : Fin r → ℕ) (hn : n ∈ cell G blocks c) :
    rightCentres c n ∈ PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks (leftCentres c n)) := by
  obtain ⟨hnG, hinj, _, hext⟩ := (mem_cell G blocks c n).mp hn
  apply (PaperP1.EffectiveWindowLists.mem_lists G _ _ _).mpr
  refine ⟨fun i ↦ hnG _, ?_, hext⟩
  intro i j hij
  exact Sum.inr.inj (c.2.symm.injective (hinj hij))

theorem fibre_count {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (c : Code r) (p : Fin c.1.val → ℕ) :
    ((cell G blocks c).filter fun n ↦ leftCentres c n = p).card ≤
      (PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)).card := by
  classical
  apply card_le_card_of_injOn (rightCentres c)
  · intro n hn
    obtain ⟨hncell, hnp⟩ := mem_filter.mp hn
    change rightCentres c n ∈ PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)
    simpa only [hnp] using suffix_effective G blocks c n hncell
  · intro n hn m hm hnm
    exact determined c n m ((mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm) hnm

theorem cell_count {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (c : Code r) (B : ℝ)
    (hB : ∀ p ∈ population G (leftBlocks c blocks),
      ((PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)).card : ℝ) ≤ B) :
    ((cell G blocks c).card : ℝ) ≤ ((population G (leftBlocks c blocks)).card : ℝ) * B := by
  classical
  let F := fun p ↦ (cell G blocks c).filter fun n ↦ leftCentres c n = p
  apply PaperP1.FiniteCoverCount.cardinal_le (cell G blocks c) (population G (leftBlocks c blocks)) F B
  · intro n hn
    exact ⟨leftCentres c n, prefix_population G blocks c n hn, mem_filter.mpr ⟨hn, rfl⟩⟩
  · intro p hp
    exact (show ((F p).card : ℝ) ≤
      (PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)).card by
        exact_mod_cast fibre_count G blocks c p).trans (hB p hp)

theorem population_cover {r : ℕ} (G : Finset ℕ) (blocks : Fin (r + 1) → ℕ → Finset ℕ) :
    ∀ n ∈ population G blocks, ∃ c ∈ (univ : Finset (Code (r + 1))), n ∈ cell G blocks c := by
  intro n hn
  obtain ⟨hnG, hinj, hexp⟩ := (mem_population G blocks n).mp hn
  obtain ⟨c, hpre, hext⟩ := (exposable_pos blocks n (by omega)).mp hexp
  exact ⟨c, mem_univ _, (mem_cell G blocks c n).mpr ⟨hnG, hinj, hpre, hext⟩⟩

theorem zero_card (G : Finset ℕ) (blocks : Fin 0 → ℕ → Finset ℕ) : (population G blocks).card ≤ 1 := by
  apply card_le_one.mpr
  exact fun n _ m _ ↦ Subsingleton.elim n m

end PaperP1.EffectiveExposure
