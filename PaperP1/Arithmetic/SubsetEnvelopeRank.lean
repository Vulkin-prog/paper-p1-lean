module

public import PaperP1.Arithmetic.SubsetEnvelopeRelation
public import PaperP1.Combinatorics.PinnedTargetBudget

/-! # A two-subset interaction pays for actual target values rather than envelope width -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetEnvelopeRank

open PaperP1.Arithmetic PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricEnvelopeGraph
  PaperP1.SubsetEnvelopeGraph PaperP1.SubsetEnvelopeRelation PaperP1.LargePrimeGraph

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def selectionMap (y H R : ℕ) (U V : Finset ℕ)
    (hV : V ⊆ Finset.Ico (y - R) (y - R + (H + 1))) :
    (oldSpace H U).comap (EvenImage.evenMap (SubsetEvenLoss.data H V)) →ₗ[F₂] (Fin (H + 1) → F₂) :=
  (FinitePiExtension.extend (SubsetEnvelopeGraph.index y H R V hV)).comp
    ((LinearMap.ker (EvenSupportRank.sumMap F₂ V)).subtype.comp
      ((oldSpace H U).comap (EvenImage.evenMap (SubsetEvenLoss.data H V))).subtype)

def componentCount (x y H R : ℕ) (U V : Finset ℕ) : ℕ :=
  (PinnedTargetRestriction.components (largePrimeGraph (start x R) (start y R) H)
    (SubsetEnvelopeGraph.pins x y H R U V) (targets y H R V)).card

def singletonCount (x y H R : ℕ) (U V : Finset ℕ) : ℕ :=
  (TargetComponentBudget.singleton (PinnedTargetBudget.family (largePrimeGraph (start x R) (start y R) H)
    (SubsetEnvelopeGraph.pins x y H R U V) (targets y H R V)) (targets y H R V)).card

theorem selectionMap_injective (y H R : ℕ) (U V : Finset ℕ)
    (hV : V ⊆ Finset.Ico (y - R) (y - R + (H + 1))) :
    Function.Injective (selectionMap y H R U V hV) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  exact FinitePiExtensionSupport.extend_injective (SubsetEnvelopeGraph.index y H R V hV) he

theorem range_le_graph {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ)
    (hU : U ⊆ Finset.Ico (x - R) (x - R + (H + 1)))
    (hV : V ⊆ Finset.Ico (y - R) (y - R + (H + 1))) :
    LinearMap.range (selectionMap y H R U V hV) ≤
      LinearMap.range (PinnedTargetRestriction.restrictionOn
        (largePrimeGraph (start x R) (start y R) H) (SubsetEnvelopeGraph.pins x y H R U V)
          (Sum.inr : Fin (H + 1) → PaperP1.LargePrimeOccurrences.Occurrence H)) := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := represent hx hy U V hU hV w
  exact ⟨u, funext hu⟩

theorem loss_le_components {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ)
    (hU : U ⊆ Finset.Ico (x - R) (x - R + (H + 1)))
    (hV : V ⊆ Finset.Ico (y - R) (y - R + (H + 1))) :
    SubsetEvenLoss.loss H U V ≤ componentCount x y H R U V := by
  have heq := LinearMap.finrank_range_of_inj (selectionMap_injective y H R U V hV)
  calc
    _ = Module.finrank F₂ (LinearMap.range (selectionMap y H R U V hV)) := heq.symm
    _ ≤ Module.finrank F₂ (LinearMap.range (PinnedTargetRestriction.restrictionOn
        (largePrimeGraph (start x R) (start y R) H) (SubsetEnvelopeGraph.pins x y H R U V)
          (Sum.inr : Fin (H + 1) → PaperP1.LargePrimeOccurrences.Occurrence H))) :=
      Submodule.finrank_mono (range_le_graph hx hy U V hU hV)
    _ ≤ _ := PinnedTargetRestriction.finrank_restrictionOn_le_of_pins _ _ _ _
      (SubsetEnvelopeGraph.target_pins_cover x y H R U V)

theorem twice_loss_le_actual_budget {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ)
    (hU : U ⊆ Finset.Ico (x - R) (x - R + (H + 1)))
    (hV : V ⊆ Finset.Ico (y - R) (y - R + (H + 1))) :
    2 * SubsetEvenLoss.loss H U V ≤ V.card + singletonCount x y H R U V := by
  have hrank := loss_le_components hx hy U V hU hV
  have hbudget := PinnedTargetBudget.component_budget (largePrimeGraph (start x R) (start y R) H)
    (SubsetEnvelopeGraph.pins x y H R U V) (targets y H R V)
  have hcard := targets_card_le (H := H) hy V
  change 2 * componentCount x y H R U V ≤ (targets y H R V).card + singletonCount x y H R U V at hbudget
  omega

end PaperP1.SubsetEnvelopeRank
