module

public import PaperP1.Model.PrivateChannelSources
public import PaperP1.Model.PairRowActivity
public import PaperP1.Arithmetic.FixedChannelLinearCount

/-! # Actual unordered fixed-channel pairs and exact centered activity comparison -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelActivity

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrivateChannelSources PaperP1.PrivateUnitCovariance

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (N H a b L : ℕ) : Finset (Finset ℕ) :=
  (goodSources N H a b L).image fun xy ↦ {xy.1, xy.2}

def independentMass (N H a b L : ℕ) : ℝ :=
  ∑ e ∈ pairs N H a b L, ∏ x ∈ e, infiniteMarginal x L

theorem pair_map_injective {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    Set.InjOn (fun xy : ℕ × ℕ ↦ ({xy.1, xy.2} : Finset ℕ))
      (goodSources N H a b L) := by
  intro xy hxy uv huv heq
  change ({xy.1, xy.2} : Finset ℕ) = {uv.1, uv.2} at heq
  have hxylt := good_sources_order hN hab hlarge hxy
  have huvlt := good_sources_order hN hab hlarge huv
  have hx : xy.1 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← heq]; simp
  have hy : xy.2 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← heq]; simp
  simp only [mem_insert, mem_singleton] at hx hy
  exact Prod.ext (by omega) (by omega)

theorem pair_data {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {e : Finset ℕ} (he : e ∈ pairs N H a b L) :
    e ⊆ dyadicBlock N ∧ e.card = 2 := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, _, _⟩ := mem_goodSources.mp hxy
  exact ⟨by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hx hy,
    by simp [ne_of_lt (good_sources_order hN hab hlarge hxy)]⟩

theorem card_bound {N H a b L : ℕ} (hN : 0 < N) (ha : 0 < a) :
    (pairs N H a b L).card ≤ (L + 1) ^ 2 * N :=
  (card_image_le).trans (good_sources_card hN ha)

theorem card_bound_linear {N H a b L : ℕ} (hN : 0 < N) (ha : 0 < a) :
    (pairs N H a b L).card ≤ (2 * (a + b) + 1) * (L + 1) * N :=
  (card_image_le).trans ((card_le_card (good_sources_subset_unitSources N H a b L)).trans
    (FixedChannelLinearCount.unit_sources_card_linear hN ha))

theorem joint_mass_eq {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    (∑ e ∈ pairs N H a b L, infiniteJointMoment L e) = channelMass N H a b L / 2 := by
  rw [channel_mass_twice_forward hN hab hlarge, pairs, sum_image (pair_map_injective hN hab hlarge)]
  unfold forwardMass
  ring

theorem independent_mass_eq {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    independentMass N H a b L = ((2 ^ L : ℝ)⁻¹) ^ 2 * (goodSources N H a b L).card := by
  rw [independentMass, pairs, sum_image (pair_map_injective hN hab hlarge)]
  calc
    _ = ∑ _xy ∈ goodSources N H a b L, ((2 ^ L : ℝ)⁻¹) ^ 2 := by
      apply sum_congr rfl
      intro xy hxy
      obtain ⟨hx, hy, _, hprivate⟩ := mem_goodSources.mp hxy
      obtain ⟨hpx, hpy⟩ := private_marginals ha (ha.trans hab) (hN.trans (mem_Ico.mp hx).1)
        (hN.trans (mem_Ico.mp hy).1) hL hprivate.private
      rw [prod_pair (ne_of_lt (good_sources_order hN hab hlarge hxy)), hpx, hpy, pow_two]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

theorem signed_eq {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    CompatibleActivitySplit.signed L (pairs N H a b L) =
      channelMass N H a b L / 2 - independentMass N H a b L := by
  unfold CompatibleActivitySplit.signed
  calc
    _ = ∑ e ∈ pairs N H a b L, (infiniteJointMoment L e - ∏ x ∈ e, infiniteMarginal x L) := by
      apply sum_congr rfl
      intro e he
      exact CompressedJointMoments.centered_pair L e (pair_data hN hab hlarge he).2
    _ = _ := by rw [sum_sub_distrib, joint_mass_eq hN hab hlarge, independentMass]

theorem absolute_comparison {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    |CompatibleActivitySplit.absolute L (pairs N H a b L) - channelMass N H a b L / 2| ≤
      independentMass N H a b L := by
  have hlo : CompatibleActivitySplit.signed L (pairs N H a b L) ≤
      CompatibleActivitySplit.absolute L (pairs N H a b L) :=
    sum_le_sum fun _ _ ↦ le_abs_self _
  have hup : CompatibleActivitySplit.absolute L (pairs N H a b L) ≤
      channelMass N H a b L / 2 + independentMass N H a b L := by
    rw [← joint_mass_eq hN hab hlarge, independentMass, ← sum_add_distrib]
    apply sum_le_sum
    intro e he
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (pair_data hN hab hlarge he).2
    simpa only [prod_pair hxy] using PairRowActivity.pair_absolute_bound L x y hxy
  rw [signed_eq hN hab hlarge] at hlo
  exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hup]⟩

theorem coefficient_bound {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L)
    {e : Finset ℕ} (he : e ∈ pairs N H a b L) :
    |infiniteCenteredCoefficient L e| ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 *
      (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, _, hprivate⟩ := mem_goodSources.mp hxy
  have hxyne := ne_of_lt (good_sources_order hN hab hlarge hxy)
  obtain ⟨hpx, hpy⟩ := private_marginals ha (ha.trans hab) (hN.trans (mem_Ico.mp hx).1)
    (hN.trans (mem_Ico.mp hy).1) hL hprivate.private
  rw [CompressedJointMoments.centered_pair L {xy.1, xy.2} (by simp [hxyne]),
    prod_pair hxyne, hpx, hpy, ← pow_two,
    private_pair_covariance ha (ha.trans hab) (hN.trans (mem_Ico.mp hx).1)
      (hN.trans (mem_Ico.mp hy).1) hxyne hL hprivate.private,
    abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (UnitFourierWeight.abs_signed_unit_sum_le_rpow ha (ha.trans hab) hcop
      (by have h := (mem_Ico.mp hx).1; omega) (by have h := (mem_Ico.mp hy).1; omega))
    (sq_nonneg _)

end PaperP1.PrivateChannelActivity
