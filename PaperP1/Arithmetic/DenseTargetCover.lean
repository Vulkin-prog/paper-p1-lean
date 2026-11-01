module

public import PaperP1.Arithmetic.DenseTargetClassification

/-! # The actual rank-loss population is covered by the two proved classifications -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseTargetCover

open Finset PaperP1.Arithmetic PaperP1.PhysicalWindowRelations PaperP1.DenseTargetRegularization

local instance denseTargetCoverTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def extended {s : ℕ} (x : Fin s → ℕ) (z : ℕ) : Option (Fin s) → ℕ
  | none => z
  | some a => x a

def targets {s : ℕ} (x : Fin s → ℕ) (L N : ℕ) (η : ℝ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter fun z ↦ η * L ≤ (loss (extended x z) L : ℝ)

theorem mem_targets {s : ℕ} (x : Fin s → ℕ) (L N z : ℕ) (η : ℝ) :
    z ∈ targets x L N η ↔ z ∈ Ico N (2 * N) ∧ η * L ≤ (loss (extended x z) L : ℝ) := by
  classical
  exact mem_filter

theorem uniform_cover (s : ℕ) (hs : 1 ≤ s) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ k : ℕ, 1 ≤ k → ∃ L₀ : ℕ, ∀ N ≥ 2, ∀ L ≥ L₀,
      ∀ x : Fin s → ℕ, (∀ a, x a ∈ Ico N (2 * N)) →
        targets x L N η ⊆ FixedSourceCertificate.sourceTargets x L k N ∪
          CodedClassTargets.targets x L (2 * (L + 1)) (t - 1) N
            ⌊(N : ℝ) ^ DenseTargetClassification.residualExponent s t k⌋₊ := by
  obtain ⟨t, ht, hregularize⟩ := uniform_regularization s hs η hη
  refine ⟨t, ht, ?_⟩
  intro k hk
  let L₀ := ⌈4 * (k + 2 : ℝ) / η⌉₊ + 1
  refine ⟨L₀, ?_⟩
  intro N hN L hL x hx z hz
  obtain ⟨hz, hloss⟩ := (mem_targets x L N z η).mp hz
  let X := extended x z
  have hL1 : 1 ≤ L := by dsimp [L₀] at hL; omega
  have hLreal : 4 * (k + 2 : ℝ) / η ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4 * (k + 2 : ℝ) / η⌉₊ ≤ L by dsimp [L₀] at hL; omega))
  have hbig : 4 * (k + 2 : ℝ) ≤ η * L := by
    have h := (div_le_iff₀ hη).mp hLreal
    linarith
  have hX : ∀ i, 2 ≤ X i := by
    intro i
    rcases i with _ | a
    · exact hN.trans (mem_Ico.mp hz).1
    · exact hN.trans (mem_Ico.mp (hx a)).1
  have hXone : ∀ i, 1 ≤ X i := fun i ↦ (by omega : 1 ≤ 2).trans (hX i)
  obtain ⟨M, hM, hlabels, _, _⟩ := hregularize X L hL1
  have hlabelsNat : k + 2 ≤ (targetLabels X L M).card := by
    have hr : (k + 2 : ℝ) ≤ ((targetLabels X L M).card : ℝ) := by
      change η * L ≤ (loss X L : ℝ) at hloss
      nlinarith only [hloss, hlabels, hbig]
    exact_mod_cast hr
  rcases DenseTargetClassification.certificate_or_code (H := 2 * (L + 1)) X M hX (by omega) hXone ht
    (by omega : 1 ≤ N) hk hM hz hlabelsNat with hcert | hcode
  · exact mem_union_left _ ((FixedSourceCertificate.mem_sourceTargets x L k N z).mpr ⟨hz, hcert⟩)
  · exact mem_union_right _ hcode

end PaperP1.DenseTargetCover
