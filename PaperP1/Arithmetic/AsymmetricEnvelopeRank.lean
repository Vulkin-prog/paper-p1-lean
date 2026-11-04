module

public import PaperP1.Arithmetic.AsymmetricEnvelopeRelation
public import PaperP1.Combinatorics.PinnedTargetBudget

/-! # The actual asymmetric loss is bounded by the target components and their singleton budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricEnvelopeRank

open PaperP1.Arithmetic PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricEnvelopeGraph
  PaperP1.AsymmetricEnvelopeRelation PaperP1.LargePrimeGraph

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def selectionMap (y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    (Submodule.comap (EvenImage.evenMap (newData H y L)) (oldSpace H old)) →ₗ[F₂] (Fin (H + 1) → F₂) :=
  (FinitePiExtension.extend (targetIndex L H R hnew hamb)).comp
    ((LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1)))).subtype.comp
      (Submodule.comap (EvenImage.evenMap (newData H y L)) (oldSpace H old)).subtype)

def componentCount (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) : ℕ :=
  (PinnedTargetRestriction.components (largePrimeGraph (start x R) (start y R) H)
    (pins x y L H R hnew hamb old) (targetPositions L H R hnew hamb)).card

def singletonCount (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) : ℕ :=
  (TargetComponentBudget.singleton (PinnedTargetBudget.family (largePrimeGraph (start x R) (start y R) H)
    (pins x y L H R hnew hamb old) (targetPositions L H R hnew hamb))
      (targetPositions L H R hnew hamb)).card

theorem selectionMap_injective (y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    Function.Injective (selectionMap y L H R hnew hamb old) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  exact FinitePiExtensionSupport.extend_injective (targetIndex L H R hnew hamb) he

theorem range_le_graph {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) :
    LinearMap.range (selectionMap y L H R hnew hamb old) ≤
      LinearMap.range (PinnedTargetRestriction.restrictionOn
        (largePrimeGraph (start x R) (start y R) H) (pins x y L H R hnew hamb old)
          (Sum.inr : Fin (H + 1) → PaperP1.LargePrimeOccurrences.Occurrence H)) := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := represent hx hy hnew hamb old hold w
  exact ⟨u, funext hu⟩

theorem loss_le_components {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) :
    loss H old y L ≤ componentCount x y L H R hnew hamb old := by
  have heq := LinearMap.finrank_range_of_inj (selectionMap_injective y L H R hnew hamb old)
  calc
    _ = Module.finrank F₂ (LinearMap.range (selectionMap y L H R hnew hamb old)) := heq.symm
    _ ≤ Module.finrank F₂ (LinearMap.range (PinnedTargetRestriction.restrictionOn
        (largePrimeGraph (start x R) (start y R) H) (pins x y L H R hnew hamb old)
          (Sum.inr : Fin (H + 1) → PaperP1.LargePrimeOccurrences.Occurrence H))) :=
      Submodule.finrank_mono (range_le_graph hx hy hnew hamb old hold)
    _ ≤ _ := PinnedTargetRestriction.finrank_restrictionOn_le_of_pins _ _ _ _
      (target_pins_cover x y L H R hnew hamb old)

theorem twice_loss_le_target_budget {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) :
    2 * loss H old y L ≤ L + 1 + singletonCount x y L H R hnew hamb old := by
  have hrank := loss_le_components hx hy hnew hamb old hold
  have hbudget := PinnedTargetBudget.component_budget (largePrimeGraph (start x R) (start y R) H)
    (pins x y L H R hnew hamb old) (targetPositions L H R hnew hamb)
  rw [targetPositions_card] at hbudget
  change 2 * componentCount x y L H R hnew hamb old ≤ L + 1 + singletonCount x y L H R hnew hamb old at hbudget
  omega

theorem loss_le_length (H y L : ℕ) (old : Finset ℕ) : loss H old y L ≤ L := by
  have hh : Module.finrank F₂ (Submodule.comap (EvenImage.evenMap (newData H y L)) (oldSpace H old)) ≤
      Module.finrank F₂ (LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1)))) := Submodule.finrank_le _
  rw [EvenSupportRank.kernel_sum_finrank, Fintype.card_fin] at hh
  exact hh

end PaperP1.AsymmetricEnvelopeRank
