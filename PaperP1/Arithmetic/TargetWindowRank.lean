module

public import PaperP1.Arithmetic.ProjectedOldInformation
public import PaperP1.Arithmetic.ScaledTargetValues
public import PaperP1.Arithmetic.SeparatedTargetMatches

/-! # The actual target quotient-rank loss, including old prime information -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TargetWindowRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ScaledTargetValues PaperP1.ProjectedOldInformation
  PaperP1.NormalizedUnitCount PaperP1.ActualNormalizedMatches

local instance targetWindowPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def oldSpace (Q : Finset ℕ) (x y L : ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  (squareClassSpace x L ⊔ squareClassSpace y L) ⊔ primeSpan Q

instance oldSpace_finite (Q : Finset ℕ) (x y L : ℕ) : FiniteDimensional F₂ (oldSpace Q x y L) := by
  change FiniteDimensional F₂ ((squareClassSpace x L ⊔ squareClassSpace y L) ⊔ primeSpan Q : Submodule F₂ (ℕ →₀ F₂))
  infer_instance

def deficiency (Q : Finset ℕ) (x y z L : ℕ) : ℕ :=
  L - (Module.finrank F₂ ↥(oldSpace Q x y L ⊔ squareClassSpace z L) - Module.finrank F₂ (oldSpace Q x y L))

theorem deficiency_comm (Q : Finset ℕ) (x y z L : ℕ) :
    deficiency Q x y z L = deficiency Q y x z L := by
  have hW : oldSpace Q x y L = oldSpace Q y x L := by
    unfold oldSpace
    rw [sup_comm (squareClassSpace x L) (squareClassSpace y L)]
  unfold deficiency
  rw [hW]

theorem deficiency_empty (x y z L : ℕ) :
    deficiency ∅ x y z L = L -
      (Module.finrank F₂ ↥((squareClassSpace x L ⊔ squareClassSpace y L) ⊔ squareClassSpace z L) -
        Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L)) := by
  have hempty : primeSpan (∅ : Finset ℕ) = (⊥ : Submodule F₂ (ℕ →₀ F₂)) := primeSpan_empty
  have hbot : (squareClassSpace x L ⊔ squareClassSpace y L) ⊔ (⊥ : Submodule F₂ (ℕ →₀ F₂)) =
      squareClassSpace x L ⊔ squareClassSpace y L := sup_bot_eq _
  unfold deficiency oldSpace
  rw [hempty, hbot]

theorem kernel_rank_eq (W : Submodule F₂ (ℕ →₀ F₂)) [FiniteDimensional F₂ W]
    {a b d z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hz : 2 ≤ z) :
    Module.finrank F₂ (W.comap (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data (newValues a b d z L)))) =
      L - (Module.finrank F₂ ↥(W ⊔ squareClassSpace z L) - Module.finrank F₂ W) := by
  have h := QuotientRank.joined_rank_add_kernel W
    (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data (newValues a b d z L)))
  change Module.finrank F₂ ↥(W ⊔ FiniteEvenSquareClasses.space (newValues a b d z L)) +
    Module.finrank F₂ (W.comap (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data (newValues a b d z L)))) =
    Module.finrank F₂ W + Module.finrank F₂ (LinearMap.ker (EvenSupportRank.sumMap F₂ (newValues a b d z L))) at h
  rw [new_space ha hb hd hz, EvenSupportRank.kernel_sum_finrank, Fintype.card_coe,
    new_card ha hb hd (by omega : 0 < z), Nat.add_sub_cancel] at h
  have hmono : Module.finrank F₂ W ≤ Module.finrank F₂ ↥(W ⊔ squareClassSpace z L) :=
    Submodule.finrank_mono le_sup_left
  omega

theorem finite_bound {P Q : Finset ℕ} (hQP : Q ⊆ P) {a b c d x y z L : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hunits : (units a b x y L).Nonempty) :
    deficiency Q x y z L ≤ (exactOffsets a b c d x y z L).card +
      Module.finrank F₂ (CoverGraphResolution.rowSolutions (PrimeRowComponents.rows (allValues a b c d x y z L) P)) := by
  have h := ProjectedOldInformation.matches_add_residual hQP (oldValues a b c x y L) (newValues a b d z L)
  rw [old_space ha hb hc hx hy hunits] at h
  change Module.finrank F₂ ((oldSpace Q x y L).comap
    (EvenImage.evenMap (K := F₂) (FiniteEvenSquareClasses.data (newValues a b d z L)))) ≤ _ at h
  rw [kernel_rank_eq (oldSpace Q x y L) ha hb hd hz, ← intersection_card ha hb hd (by omega : 0 < z)] at h
  exact h

theorem interior_bound {P Q : Finset ℕ} (hQP : Q ⊆ P) {a b c d x y z L t : ℕ}
    (ha : 0 < a) (hb : 3 ≤ b) (hab : a.Coprime b) (horder : a < b)
    (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d) (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hsepX : x + L ≤ z ∨ z + L ≤ x) (hsepY : y + L ≤ z ∨ z + L ≤ y)
    (i j : Fin (L + 1)) (h : ℤ) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t) (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hlo : (b : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 2 * a) :
    (deficiency Q x y z L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * FixedChannelGamma.gammaReal a b + 3 +
      Module.finrank F₂ (CoverGraphResolution.rowSolutions (PrimeRowComponents.rows (allValues a b c d x y z L) P)) := by
  have hbpos : 0 < b := by omega
  have hunit : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j := by
    rw [hbaseX, hbaseY]
    ring
  have hfinite : (deficiency Q x y z L : ℝ) ≤ ((exactOffsets a b c d x y z L).card : ℝ) +
      Module.finrank F₂ (CoverGraphResolution.rowSolutions (PrimeRowComponents.rows (allValues a b c d x y z L) P)) := by
    exact_mod_cast finite_bound hQP ha hbpos hc hd hx hy hz (⟨(i, j), mem_units.mpr hunit⟩)
  have hcount := SeparatedTargetMatches.match_bound ha hb hab horder hc hd hcop (by omega : 0 < x)
    (by omega : 0 < y) (by omega : 0 < z) hsepX hsepY i j h hbaseX hbaseY htarget hlo hhi
  linarith

end PaperP1.TargetWindowRank
