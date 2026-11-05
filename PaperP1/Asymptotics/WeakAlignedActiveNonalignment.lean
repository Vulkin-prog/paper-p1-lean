module

public import PaperP1.Asymptotics.CriticalAlignedSelections
public import PaperP1.Arithmetic.TwoTargetUnitExclusion
public import PaperP1.Arithmetic.SelectedProportionalPairs

/-! # Actual offset nonalignment after all but one channel unit is excluded

The selected active positions may be arbitrarily numerous. Each possible
four-position obstruction is ruled out by the fixed-size independence theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakAlignedActiveNonalignment

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.NormalizedWindowSets PaperP1.FiniteEvenSquareClasses

theorem uniform_no_exact (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      ∀ a b : ℕ, 0 < a → 0 < b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
      EnlargedPairGeometry.Geometric a b y z L →
      ∀ D : Finset (Fin (L + 1) × Fin (L + 1)), (units a b y z L \ D).card ≤ 1 →
      ∀ P Q : Fin (L + 1) → Prop, (∀ w ∈ D, ¬P w.1 ∨ ¬Q w.2) →
      ∀ u₁ u₂ v₁ v₂ : Fin (L + 1), P u₁ → P u₂ → Q v₁ → Q v₂ →
      (offset u₁, offset v₁) ≠ (offset u₂, offset v₂) →
      ((y : ℤ) + offset u₁) * ((z : ℤ) + offset v₂) ≠
        ((y : ℤ) + offset u₂) * ((z : ℤ) + offset v₁) := by
  obtain ⟨N₀, hN₀, hu⟩ := CriticalAlignedSelections.uniform_selected_directness C 4
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband y z hy hz a b ha hb haH hbH hgeom D hremaining P Q hsafe u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne he
  classical
  have hy2 : 2 ≤ y := by have hh := (mem_Ico.mp hy).1; omega
  have hz2 : 2 ≤ z := by have hh := (mem_Ico.mp hz).1; omega
  have hyp : 0 < y := by omega
  have hzp : 0 < z := by omega
  let I : Finset (Fin (L + 1)) := {u₁, u₂}
  let J : Finset (Fin (L + 1)) := {v₁, v₂}
  let S := I.image (startCompleteVertexLabel y L)
  let T := J.image (startCompleteVertexLabel z L)
  have hPI (u : Fin (L + 1)) (hu : u ∈ I) : P u := by
    have hh : u = u₁ ∨ u = u₂ := by simpa only [I, mem_insert, mem_singleton] using hu
    rcases hh with rfl | rfl
    · exact hu₁
    · exact hu₂
  have hQJ (v : Fin (L + 1)) (hv : v ∈ J) : Q v := by
    have hh : v = v₁ ∨ v = v₂ := by simpa only [J, mem_insert, mem_singleton] using hv
    rcases hh with rfl | rfl
    · exact hv₁
    · exact hv₂
  have havoid (w : Fin (L + 1) × Fin (L + 1)) (hw : w ∈ D) : w.1 ∉ I ∨ w.2 ∉ J := by
    rcases hsafe w hw with hP | hQ
    · exact Or.inl (fun h ↦ hP (hPI _ h))
    · exact Or.inr (fun h ↦ hQ (hQJ _ h))
  have hS : S ⊆ NormalizedWindowSets.values y L := by
    intro n hn
    obtain ⟨u, _hu, rfl⟩ := mem_image.mp hn
    exact NormalizedWindowSets.mem_values.mpr ⟨u, rfl⟩
  have hT : T ⊆ NormalizedWindowSets.values z L := by
    intro n hn
    obtain ⟨v, _hv, rfl⟩ := mem_image.mp hn
    exact NormalizedWindowSets.mem_values.mpr ⟨v, rfl⟩
  have hIcard : I.card ≤ 2 := by simpa only [I, card_singleton] using card_insert_le u₁ {u₂}
  have hJcard : J.card ≤ 2 := by simpa only [J, card_singleton] using card_insert_le v₁ {v₂}
  have hcard : S.card + T.card ≤ 4 :=
    (Nat.add_le_add card_image_le card_image_le).trans (by omega)
  have hoverlap := TwoTargetUnitExclusion.selected_overlap_le_one I J D hremaining havoid
  obtain ⟨hindS, _hindT, hdis⟩ := hu N hN L hband y z hy hz a b ha hb haH hbH hgeom S T hS hT hcard hoverlap
  have hny (u : Fin (L + 1)) : startCompleteVertexLabel y L u ≠ 0 := by
    rw [startCompleteVertexLabel_eq_offset hyp]
    omega
  have hnz (v : Fin (L + 1)) : startCompleteVertexLabel z L v ≠ 0 := by
    rw [startCompleteVertexLabel_eq_offset hzp]
    omega
  have hcross : startCompleteVertexLabel y L u₁ * startCompleteVertexLabel z L v₂ =
      startCompleteVertexLabel y L u₂ * startCompleteVertexLabel z L v₁ := by
    have hh : ((startCompleteVertexLabel y L u₁ : ℕ) : ℤ) *
        ((startCompleteVertexLabel z L v₂ : ℕ) : ℤ) =
        ((startCompleteVertexLabel y L u₂ : ℕ) : ℤ) *
          ((startCompleteVertexLabel z L v₁ : ℕ) : ℤ) := by
      simpa only [label_cast hyp, label_cast hzp] using he
    exact_mod_cast hh
  have hune : u₁ ≠ u₂ := by
    intro hh
    subst u₂
    have hv : v₂ = v₁ := startCompleteVertexLabel_injective hzp (mul_left_cancel₀ (hny u₁) hcross)
    exact hne (Prod.ext rfl (congrArg offset hv.symm))
  have hlabels : startCompleteVertexLabel y L u₁ ≠ startCompleteVertexLabel y L u₂ :=
    fun h ↦ hune (startCompleteVertexLabel_injective hyp h)
  have hforbid := SelectedProportionalPairs.no_proportional_pairs S T hindS hdis
    (fun n hn ↦ NormalizedWindowSets.values_positive hy2 n (hS hn))
    (fun n hn ↦ NormalizedWindowSets.values_positive hz2 n (hT hn))
    (startCompleteVertexLabel y L u₁) (startCompleteVertexLabel y L u₂)
    (startCompleteVertexLabel z L v₁) (startCompleteVertexLabel z L v₂)
    (mem_image.mpr ⟨u₁, by simp [I], rfl⟩) (mem_image.mpr ⟨u₂, by simp [I], rfl⟩)
    (mem_image.mpr ⟨v₁, by simp [J], rfl⟩) (mem_image.mpr ⟨v₂, by simp [J], rfl⟩) hlabels
  exact hforbid hcross

end PaperP1.WeakAlignedActiveNonalignment
