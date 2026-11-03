module

public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Model.IndependentFullSupportTail

/-! # Exact cardinality-weighted primitive rank mass and its actual joint-plus-centered consequence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPrimitiveMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

def families (G : Finset ℕ) (L s : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun I ↦ s ≤ I.card ∧ Primitive L I

def rankMass (F : Finset (Finset ℕ)) (L : ℕ) (u : ℝ) : ℝ :=
  ∑ I ∈ F, u ^ I.card * PrimitiveWindowMass.weight L I

def actualMass (F : Finset (Finset ℕ)) (L : ℕ) (u : ℝ) : ℝ :=
  ∑ I ∈ F, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)

theorem mem_families (G I : Finset ℕ) (L s : ℕ) :
    I ∈ families G L s ↔ I ⊆ G ∧ s ≤ I.card ∧ Primitive L I := by
  classical
  simp only [families, mem_filter, mem_powerset]

theorem rankMass_nonneg (F : Finset (Finset ℕ)) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) : 0 ≤ rankMass F L u :=
  sum_nonneg fun I _ ↦ mul_nonneg (pow_nonneg hu _) (PrimitiveWindowMass.weight_nonneg L I)

theorem fixed_weight (F : Finset (Finset ℕ)) (L r : ℕ) (u : ℝ) (hF : ∀ I ∈ F, I.card = r) :
    rankMass F L u = u ^ r * PrimitiveWindowMass.mass F L := by
  rw [PrimitiveWindowMass.mass, mul_sum]
  apply sum_congr rfl
  intro I hI
  rw [hF I hI]

theorem rank_le_independent {N L : ℕ} (hN : 2 ≤ N) (F : Finset (Finset ℕ)) (u : ℝ) (hu : 0 ≤ u)
    (hF : ∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.Nonempty ∧ Primitive L I) :
    rankMass F L u ≤ (2 ^ L : ℝ) * ∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L := by
  rw [mul_sum]
  apply sum_le_sum
  intro I hI
  have hpos : ∀ x ∈ I, 0 < x := by
    intro x hx
    have h := (mem_Ico.mp ((hF I hI).1 hx)).1
    omega
  have h := mul_le_mul_of_nonneg_left (PrimitiveWindowMass.primitive_weight_le L I
    (hF I hI).2.1 (hF I hI).2.2 hpos) (pow_nonneg hu I.card)
  rw [prod_mul_distrib, prod_const]
  exact h.trans_eq (by ring)

theorem actual_le_rank (F : Finset (Finset ℕ)) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u)
    (hF : ∀ I ∈ F, I.Nonempty ∧ ∀ x ∈ I, 0 < infiniteMarginal x L) :
    actualMass F L u ≤ 2 * rankMass F L u := by
  rw [rankMass, mul_sum]
  apply sum_le_sum
  intro I hI
  have hq := PrimitiveWindowMass.joint_le_weight L hL I
  have hc := PrimitiveWindowMass.centered_le_weight L hL I (hF I hI).1 (hF I hI).2
  have h := mul_le_mul_of_nonneg_left (show infiniteJointMoment L I + |infiniteCenteredCoefficient L I| ≤
    2 * PrimitiveWindowMass.weight L I by linarith only [hq, hc]) (pow_nonneg hu I.card)
  exact h.trans_eq (by ring)

end PaperP1.WeightedPrimitiveMass
