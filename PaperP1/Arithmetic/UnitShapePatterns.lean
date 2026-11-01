module

public import PaperP1.Arithmetic.SelectedUnitWords
public import PaperP1.Arithmetic.ChannelWordHosts

/-! # Actual pair-specific unit shapes are the global patterns carrying that source unit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitShapePatterns

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.SelectedUnitWords PaperP1.ChannelWordHosts PaperP1.ChannelPlacements

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def HasUnit {L a b : ℕ} (x y : ℕ) (p : Patterns L a b) : Prop :=
  (placementIndex L p.2.1.val, placementIndex L p.2.2.val) ∈ units a b x y L

def coefficient {L a b : ℕ} (p : Patterns L a b) : ℤ :=
  ChannelSumIdentity.weight p.1.val * placementSign p.2.1.val * placementSign p.2.2.val

def integerPatternSum (a b x y L : ℕ) : ℤ :=
  ∑ p : Patterns L a b, if HasUnit x y p then coefficient p else 0

theorem index_fin_value {L : ℕ} (i : Fin (L + 1)) : placementIndex L i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

def pattern {a b x y L : ℕ} (s : Shapes a b x y L) : Patterns L a b :=
  ⟨s.1, ⟨⟨s.2.val.val.1.val, s.2.property.1⟩, ⟨s.2.val.val.2.val, s.2.property.2⟩⟩⟩

theorem pattern_has_unit {a b x y L : ℕ} (s : Shapes a b x y L) : HasUnit x y (pattern s) := by
  unfold HasUnit pattern
  dsimp only
  rw [index_fin_value, index_fin_value]
  exact s.2.val.property

def shape {a b x y L : ℕ} (p : Patterns L a b) (hp : HasUnit x y p) : Shapes a b x y L :=
  ⟨p.1, ⟨⟨(placementIndex L p.2.1.val, placementIndex L p.2.2.val), hp⟩,
    by simpa only [placement_index_val] using p.2.1.property,
    by simpa only [placement_index_val] using p.2.2.property⟩⟩

theorem pattern_shape {a b x y L : ℕ} (p : Patterns L a b) (hp : HasUnit x y p) :
    pattern (shape p hp) = p := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply Prod.ext <;> apply Subtype.ext
  · exact placement_index_val p.2.1
  · exact placement_index_val p.2.2

theorem shape_pattern {a b x y L : ℕ} (s : Shapes a b x y L) :
    shape (pattern s) (pattern_has_unit s) = s := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (index_fin_value _) (index_fin_value _)

def patternEquiv (a b x y L : ℕ) : Shapes a b x y L ≃ {p : Patterns L a b // HasUnit x y p} where
  toFun s := ⟨pattern s, pattern_has_unit s⟩
  invFun p := shape p.val p.property
  left_inv := shape_pattern
  right_inv p := Subtype.ext (pattern_shape p.val p.property)

theorem shape_sum (a b x y L : ℕ) :
    (∑ s : Shapes a b x y L, ChannelSumIdentity.weight s.1.val *
      placementSign s.2.val.val.1.val * placementSign s.2.val.val.2.val) = integerPatternSum a b x y L := by
  calc
    _ = ∑ p : {p : Patterns L a b // HasUnit x y p}, coefficient p.val := by
      apply Fintype.sum_equiv (patternEquiv a b x y L)
      intro s
      rfl
    _ = _ := by
      unfold integerPatternSum
      symm
      rw [← sum_filter]
      exact sum_subtype _ (by intro p; simp only [mem_filter, mem_univ, true_and]) coefficient

end PaperP1.UnitShapePatterns
