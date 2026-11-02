module

public import PaperP1.Model.RetainedCardinalityDeficits

/-! # Exact cardinality grouping of the actual retained-reference deficits -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedDeficitGrouping

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.RegularStarts PaperP1.GoodEdgeCompression PaperP1.RetainedGoodEdges
  PaperP1.RetainedReferenceIdentity PaperP1.RetainedReferenceTheorem PaperP1.RetainedDeficitNorm
  PaperP1.RetainedCardinalityDeficits

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem nominal_product {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (A : Finset ℕ)
    (hA : A ⊆ regularStarts N L) :
    (∏ x ∈ A, infiniteMarginal x L) = ((2 ^ L : ℝ)⁻¹) ^ A.card := by
  calc
    _ = ∏ _x ∈ A, (2 ^ L : ℝ)⁻¹ := prod_congr rfl (fun x hx ↦ ground_marginal hN hL x (hA hx))
    _ = _ := by simp

theorem sum_mapped_constant {R ι : Type*} [CommRing R] (φ : ℝ →+* R) (s : Finset ι) (a : ℝ) (v : R) :
    (∑ _i ∈ s, φ a * v) = φ ((s.card : ℝ) * a) * v := by
  rw [← sum_mul, ← map_sum, sum_const, nsmul_eq_mul]

theorem first_grouped {R : Type*} [CommRing R] {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (φ : ℝ →+* R) (f : ℕ → R) :
    (∑ I ∈ excluded N L, φ (∏ x ∈ I, infiniteMarginal x L) * f I.card) =
      ∑ r ∈ range ((regularStarts N L).card + 1), φ (firstCoefficient N L r) * f r := by
  have hsize (I : Finset ℕ) (hI : I ∈ excluded N L) : I.card + 0 ≤ (regularStarts N L).card := by
    exact Nat.add_zero I.card ▸ card_le_card (mem_powerset.mp (mem_filter.mp hI).1)
  rw [sum_by_shifted_card (excluded N L) (regularStarts N L).card 0 hsize]
  apply sum_congr rfl
  intro r _hr
  simp only [Nat.add_zero]
  change (∑ I ∈ ((regularStarts N L).powerset.filter (fun I ↦ runRelativeNullity L I ≠ 0)).filter
    (fun I ↦ I.card = r), φ (∏ x ∈ I, infiniteMarginal x L) * f I.card) = _
  rw [first_layer_eq]
  calc
    _ = ∑ _I ∈ ((regularStarts N L).powersetCard r).filter (fun I ↦ runRelativeNullity L I ≠ 0),
        φ (((2 ^ L : ℝ)⁻¹) ^ r) * f r := by
      apply sum_congr rfl
      intro I hI
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hI).1
      rw [nominal_product hN hL I hsub, hcard]
    _ = _ := by
      rw [sum_mapped_constant, first_layer_count]
      have heq : (((regularStarts N L).card.choose r - (directAt N L r).card : ℕ) : ℝ) *
          ((2 ^ L : ℝ)⁻¹) ^ r = firstCoefficient N L r := by unfold firstCoefficient; ring1
      rw [heq]

theorem edge_grouped {R : Type*} [CommRing R] {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (H : ℝ) (e : Finset ℕ) (he : e ∈ goodEdges H N L) (φ : ℝ →+* R) (f : ℕ → R) :
    (∑ A ∈ failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e,
      φ (infiniteJointMoment L e * ∏ x ∈ A, infiniteMarginal x L) * f (A.card + 2)) =
      ∑ r ∈ range ((regularStarts N L).card + 1), φ (edgeCoefficient N L e r) * f r := by
  rw [sum_by_shifted_card _ (regularStarts N L).card 2 (failed_size_bound hN H e he)]
  apply sum_congr rfl
  intro r _hr
  by_cases hr : r < 2
  · rw [failed_layer_empty N L e r hr, sum_empty, edgeCoefficient, ite_eq_left hr, map_zero, zero_mul]
  · have hr₂ : 2 ≤ r := by omega
    calc
      _ = ∑ _A ∈ (failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e).filter
          (fun A ↦ A.card + 2 = r), φ (infiniteJointMoment L e * ((2 ^ L : ℝ)⁻¹) ^ (r - 2)) * f r := by
        apply sum_congr rfl
        intro A hA
        have hbase := (mem_filter.mp hA).1
        have hcard := (mem_filter.mp hA).2
        have hsub := mem_powerset.mp (mem_filter.mp hbase).1
        have hcard' : A.card = r - 2 := by omega
        rw [nominal_product hN hL A (hsub.trans sdiff_subset), hcard, hcard']
      _ = _ := by
        rw [sum_mapped_constant, failed_layer_count hN H e he r hr₂]
        have heq : ((((regularStarts N L).card - 2).choose (r - 2) -
            (gamma N L e (r - 2)).card : ℕ) : ℝ) *
            (infiniteJointMoment L e * ((2 ^ L : ℝ)⁻¹) ^ (r - 2)) = edgeCoefficient N L e r := by
          unfold edgeCoefficient
          rw [ite_eq_right hr]
          ring1
        rw [heq]

theorem firstDeficit_grouped {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    firstDeficit N L = ∑ r ∈ range ((regularStarts N L).card + 1),
      scalar (firstCoefficient N L r) * forwardDifference ^ r := by
  unfold firstDeficit directDeficit
  change (∑ I ∈ excluded N L, familyTerm (fun x ↦ scalar (infiniteMarginal x L)) forwardDifference I) = _
  calc
    _ = ∑ I ∈ excluded N L, scalar (∏ x ∈ I, infiniteMarginal x L) * forwardDifference ^ I.card := by
      apply sum_congr rfl
      intro I _hI
      exact familyTerm_scalar _ I
    _ = _ := first_grouped hN hL scalar (fun r ↦ (forwardDifference : SignedLaw ℝ) ^ r)

theorem firstMass_grouped {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    firstMass N L = ∑ r ∈ range ((regularStarts N L).card + 1), (2 : ℝ) ^ r * firstCoefficient N L r := by
  have h := first_grouped hN hL (RingHom.id ℝ) (fun r ↦ (2 : ℝ) ^ r)
  simp only [RingHom.id_apply] at h
  unfold firstMass directMass
  change (∑ I ∈ excluded N L, (2 : ℝ) ^ I.card * ∏ x ∈ I, infiniteMarginal x L) = _
  calc
    _ = ∑ I ∈ excluded N L, (∏ x ∈ I, infiniteMarginal x L) * (2 : ℝ) ^ I.card := by
      apply sum_congr rfl
      intro I _hI
      ring1
    _ = _ := by rw [h]; apply sum_congr rfl; intro r _hr; ring1

theorem secondDeficit_grouped {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    secondDeficit H N L = ∑ r ∈ range ((regularStarts N L).card + 1),
      scalar (secondCoefficient H N L r) * forwardDifference ^ r := by
  unfold secondDeficit compressedDeficit
  calc
    _ = ∑ e ∈ goodEdges H N L, ∑ A ∈ failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e,
        scalar (infiniteJointMoment L e * ∏ x ∈ A, infiniteMarginal x L) * forwardDifference ^ (A.card + 2) := by
      apply sum_congr rfl
      intro e _he
      apply sum_congr rfl
      intro A _hA
      exact compressed_term_eq _ _ e A
    _ = ∑ e ∈ goodEdges H N L, ∑ r ∈ range ((regularStarts N L).card + 1),
        scalar (edgeCoefficient N L e r) * forwardDifference ^ r := by
      apply sum_congr rfl
      intro e he
      exact edge_grouped hN hL H e he scalar (fun r ↦ (forwardDifference : SignedLaw ℝ) ^ r)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r _hr
      simp only [secondCoefficient, map_sum, sum_mul]

theorem secondMass_grouped {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    secondMass H N L = ∑ r ∈ range ((regularStarts N L).card + 1),
      (2 : ℝ) ^ r * secondCoefficient H N L r := by
  unfold secondMass compressedMass
  calc
    _ = ∑ e ∈ goodEdges H N L, ∑ A ∈ failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e,
        (infiniteJointMoment L e * ∏ x ∈ A, infiniteMarginal x L) * (2 : ℝ) ^ (A.card + 2) := by
      apply sum_congr rfl
      intro e _he
      apply sum_congr rfl
      intro A _hA
      ring1
    _ = ∑ e ∈ goodEdges H N L, ∑ r ∈ range ((regularStarts N L).card + 1),
        edgeCoefficient N L e r * (2 : ℝ) ^ r := by
      apply sum_congr rfl
      intro e he
      simpa only [RingHom.id_apply] using edge_grouped hN hL H e he (RingHom.id ℝ) (fun r ↦ (2 : ℝ) ^ r)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r _hr
      simp only [secondCoefficient, mul_sum]
      apply sum_congr rfl
      intro e _he
      ring1

end PaperP1.RetainedDeficitGrouping
