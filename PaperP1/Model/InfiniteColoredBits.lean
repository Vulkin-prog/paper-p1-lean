module

public import PaperP1.Model.InfiniteColoredSamples
public import PaperP1.Model.RelativeSignIndependence

/-! # Original infinite run-window bits under shared small and colored large prime signs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteColoredBits

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.RelativeSignIndependence

local instance infiniteColoredBitsTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance infiniteColoredBitsMeasurableF2 : MeasurableSpace F₂ := ⊤

def selected {κ : Type*} (Y : ℕ) (k : κ) (ω : InfiniteColoredSamples.Sample κ) : InfiniteSample :=
  fun j ↦ if Nat.nth Nat.Prime j ≤ Y then ω.1 j else ω.2 k j

def bits {κ : Type*} (Y x L : ℕ) (k : κ) (ω : InfiniteColoredSamples.Sample κ) : Fin L → F₂ :=
  infiniteStartBits x L (selected Y k ω)

theorem selected_restrict {κ : Type*} (M Y : ℕ) (k : κ) (ω : InfiniteColoredSamples.Sample κ) :
    restrictToFinite M (selected Y k ω) =
      ColoredPrimeSamples.select M Y k (InfiniteColoredSamples.restrict κ M ω) := by
  funext p
  have hprime : Nat.nth Nat.Prime (Nat.primeCounting' p.val.val) = p.val.val := Nat.nth_count p.property
  change (if Nat.nth Nat.Prime (Nat.primeCounting' p.val.val) ≤ Y then _ else _) = _
  rw [hprime]
  rfl

theorem bits_restrict {κ : Type*} {M x L : ℕ} (hcut : x + L ≤ M) (Y : ℕ)
    (k : κ) (ω : InfiniteColoredSamples.Sample κ) :
    ColoredPrimeSamples.start M Y x L k (InfiniteColoredSamples.restrict κ M ω) = bits Y x L k ω := by
  unfold bits
  rw [← startSystem_restrict_eq hcut (selected Y k ω), selected_restrict]
  rfl

end PaperP1.InfiniteColoredBits
