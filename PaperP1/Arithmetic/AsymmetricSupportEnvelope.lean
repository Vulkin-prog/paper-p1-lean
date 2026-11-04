module

public import PaperP1.Arithmetic.AsymmetricLossSelections
public import PaperP1.Arithmetic.TruncatedAsymmetricSupport
public import PaperP1.Model.FiniteRademacher

/-! # Actual asymmetric losses embed into a common translated forward interval

The enclosing old set is arbitrary inside its stated radius. The new
selection remains in the original, shorter complete window.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricSupportEnvelope

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEvenLoss PaperP1.Model

def population (N L H : ℕ) (old : ℕ → Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦ 0 < loss H (old p.1) p.2 L

def translate (R : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 - R + 1, p.2 - R + 1)

theorem translated_domain {N R x : ℕ} (hR : 1 ≤ R) (hRN : R < N) (hx : x ∈ dyadicBlock N) :
    x - R + 1 ∈ Ico (N - R + 1) (N - R + 1 + N) := by
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  apply mem_Ico.mpr
  omega

theorem translated_old {N H R x n : ℕ} (hRN : R < N) (hH : 2 * R + 1 ≤ H)
    (hx : x ∈ dyadicBlock N) (hn : |(n : ℤ) - x| ≤ (R : ℤ)) :
    n ∈ Ico ((x - R + 1) - 1) ((x - R + 1) - 1 + H) := by
  have hxlo := (mem_Ico.mp hx).1
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  apply mem_Ico.mpr
  omega

theorem translated_new {N L H R y n : ℕ} (hRN : R < N) (hR : L + 1 ≤ R) (hH : 2 * R + 1 ≤ H)
    (hy : y ∈ dyadicBlock N) (hn : n ∈ NormalizedWindowSets.values y L) :
    n ∈ Ico ((y - R + 1) - 1) ((y - R + 1) - 1 + H) := by
  have hylo := (mem_Ico.mp hy).1
  have hypos : 0 < y := by omega
  rw [NormalizedWindowSets.values_eq_interval hypos] at hn
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hn
  apply mem_Ico.mpr
  omega

theorem translated_related {N L H R x y : ℕ} {old : ℕ → Finset ℕ}
    (hRN : R < N) (hR : L + 1 ≤ R) (hH : 2 * R + 1 ≤ H)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (hold : ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) (hloss : 0 < loss H (old x) y L) :
    TruncatedAsymmetricSupport.Related H (x - R + 1) (y - R + 1) := by
  have hypos : 0 < y := by have hh := (mem_Ico.mp hy).1; omega
  obtain ⟨A, I, hA, hI, _heven, hcard, he⟩ := AsymmetricLossSelections.exists_selections hypos hloss
  refine ⟨A, I, ?_, ?_, hcard, he.symm⟩
  · intro n hn
    exact translated_old hRN hH hx (hold n (hA hn))
  · intro n hn
    exact translated_new hRN hR hH hy (hI hn)

theorem population_card {N L H R : ℕ} (old : ℕ → Finset ℕ) (hR : L + 1 ≤ R)
    (hH : 2 * R + 1 ≤ H) (hHN : H ≤ N)
    (hold : ∀ x ∈ dyadicBlock N, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) :
    (population N L H old).card ≤ (TruncatedAsymmetricSupport.population N H (N - R + 1)).card := by
  classical
  have hRN : R < N := by omega
  have hRpos : 1 ≤ R := by omega
  apply card_le_card_of_injOn (translate R)
  · intro p hp
    obtain ⟨hpblock, hloss⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hpblock
    exact mem_filter.mpr ⟨mem_product.mpr ⟨translated_domain hRpos hRN hx, translated_domain hRpos hRN hy⟩,
      translated_related hRN hR hH hx hy (hold p.1 hx) hloss⟩
  · intro p hp q hq he
    have hpD := (mem_product.mp (mem_filter.mp hp).1)
    have hqD := (mem_product.mp (mem_filter.mp hq).1)
    have hpx := (mem_Ico.mp hpD.1).1
    have hpy := (mem_Ico.mp hpD.2).1
    have hqx := (mem_Ico.mp hqD.1).1
    have hqy := (mem_Ico.mp hqD.2).1
    have hex := congrArg Prod.fst he
    have hey := congrArg Prod.snd he
    change p.1 - R + 1 = q.1 - R + 1 at hex
    change p.2 - R + 1 = q.2 - R + 1 at hey
    exact Prod.ext (by omega) (by omega)

end PaperP1.AsymmetricSupportEnvelope
