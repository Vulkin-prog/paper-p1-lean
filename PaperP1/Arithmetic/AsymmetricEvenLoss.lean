module

public import PaperP1.Algebra.EvenPreimageRank
public import PaperP1.Arithmetic.EvenSquareClasses
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # The literal asymmetric even-selection loss above an old raw-value space

Small-prime coordinates are forgotten on BOTH sides. The old space has no
block-parity restriction. The new domain is exactly the zero-sum selection
space on its actual complete window, as in companion T1.10.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricEvenLoss

open Finset PaperP1.Arithmetic PaperP1.Affine

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def largeParity (H n : ℕ) : ℕ →₀ F₂ := (parityVec n).filter (fun p ↦ H < p)

def oldSpace (H : ℕ) (U : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  Submodule.span F₂ ((fun n ↦ largeParity H n) '' (U : Set ℕ))

def newData (H z L : ℕ) (u : Fin (L + 1)) : ℕ →₀ F₂ :=
  largeParity H (startCompleteVertexLabel z L u)

def loss (H : ℕ) (U : Finset ℕ) (z L : ℕ) : ℕ :=
  Module.finrank F₂ (Submodule.comap (EvenImage.evenMap (newData H z L)) (oldSpace H U))

theorem old_mem {H n : ℕ} {U : Finset ℕ} (hn : n ∈ U) : largeParity H n ∈ oldSpace H U :=
  Submodule.subset_span ⟨n, hn, rfl⟩

theorem selected_lower (H : ℕ) (U : Finset ℕ) (z L : ℕ) (I : Finset (Fin (L + 1)))
    (hI : ∀ u ∈ I, ∃ n ∈ U, largeParity H n = newData H z L u) : I.card - 1 ≤ loss H U z L := by
  apply EvenPreimageRank.selected_lower
  intro u hu
  obtain ⟨n, hn, he⟩ := hI u hu
  rw [← he]
  exact old_mem hn

theorem largeParity_mul {a b : ℕ} (H : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    largeParity H (a * b) = largeParity H a + largeParity H b := by
  ext p
  simp only [largeParity, parityVec_mul ha hb, Finsupp.filter_apply, Finsupp.add_apply]
  split_ifs <;> simp only [zero_add]

theorem largeParity_prime_zero {p H : ℕ} (hp : p.Prime) (hH : p ≤ H) : largeParity H p = 0 := by
  ext q
  by_cases hq : H < q
  · have hpq : p ≠ q := by omega
    simp [largeParity, hq, hp.factorization, hpq]
  · simp only [largeParity, Finsupp.filter_apply, hq, ite_false, Finsupp.zero_apply]

theorem scaled_two_three {H n : ℕ} (hH : 3 ≤ H) (hn : 0 < n) :
    largeParity H (3 * n) = largeParity H (2 * n) := by
  rw [largeParity_mul H (by decide : (3 : ℕ) ≠ 0) hn.ne',
    largeParity_mul H (by decide : (2 : ℕ) ≠ 0) hn.ne',
    largeParity_prime_zero Nat.prime_three hH,
    largeParity_prime_zero Nat.prime_two (by omega), zero_add]

end PaperP1.AsymmetricEvenLoss
