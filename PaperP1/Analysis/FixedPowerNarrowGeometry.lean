module

public import PaperP1.Analysis.FixedPowerPrimeBand
public import PaperP1.Analysis.NarrowPrimeBands


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerNarrowGeometry
open Finset Filter PaperP1
open scoped Classical

theorem anchor_bounds (a b : ℝ) (H N j : ℕ) (hH : 2 ≤ H)
    (hj : j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N)) :
    (N : ℝ)^a/2 ≤ NarrowPrimeBands.anchor H j ∧ NarrowPrimeBands.anchor H j ≤ (N : ℝ)^b := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
  have hP := FixedPowerPrimeBand.mem_primes a b N p hp
  change p.Prime ∧ (N : ℝ)^a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ)^b at hP
  have hAnchor := NarrowPrimeBands.index_bounds H p (by omega) hP.1.one_le
  have hGrowth := mul_le_mul_of_nonneg_right (NarrowPrimeBands.growth_le_two H hH)
    (NarrowPrimeBands.anchor_pos H (NarrowPrimeBands.index H p)).le
  exact ⟨by linarith only [hP.2.1,hAnchor.2,hGrowth],hAnchor.1.trans hP.2.2⟩

theorem eventual_lower (a b : ℝ) (ha : 0 < a) (H : ℕ) (hH : 2 ≤ H) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
      (N : ℝ)^(a/2) ≤ NarrowPrimeBands.anchor H j := by
  filter_upwards [(FixedPowerPrimeBand.lower_tendsto (a/2) (by positivity)).eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 1] with N hPower hN
  intro j hj
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hTwo : 2 ≤ (N : ℝ)^(a/2) := hPower
  have hSquare : (N : ℝ)^a=(N : ℝ)^(a/2)*(N : ℝ)^(a/2) := by
    rw [← Real.rpow_add hNP]
    congr 1
    ring
  have hProduct := mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hNP.le (a/2))
  have hHalf : (N : ℝ)^(a/2) ≤ (N : ℝ)^a/2 := by rw [hSquare]; linarith only [hProduct]
  exact hHalf.trans (anchor_bounds a b H N j hH hj).1

theorem eventual_geometry (a b : ℝ) (ha : 0 < a) (H : ℕ) (hH : 4 ≤ H) (hOrder : 2 ≤ a*(H : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
      (H : ℝ) ≤ NarrowPrimeBands.anchor H j ∧ (N : ℝ) ≤ (NarrowPrimeBands.anchor H j)^H := by
  filter_upwards [eventual_lower a b ha H (by omega),
    (FixedPowerPrimeBand.lower_tendsto (a/2) (by positivity)).eventually (eventually_ge_atTop (H : ℝ)),
    eventually_ge_atTop 1] with N hLower hBig hN
  intro j hj
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : (N : ℝ)^(a/2) ≤ NarrowPrimeBands.anchor H j := hLower j hj
  refine ⟨hBig.trans hL,?_⟩
  calc
    _ = (N : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (N : ℝ)^((a/2)*(H : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hOrder])
    _ = ((N : ℝ)^(a/2))^H := by rw [← Real.rpow_natCast,← Real.rpow_mul hNP.le]
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hNP.le _) hL H

theorem width_exists (a : ℝ) (ha : 0 < a) (L : ℕ) : ∃ H : ℕ, 4 ≤ H ∧ L ≤ H ∧ 2 ≤ a*(H : ℝ) := by
  let H := max 4 (max L ⌈2/a⌉₊)
  have hFour : 4 ≤ H := le_max_left _ _
  have hL : L ≤ H := (le_max_left _ _).trans (le_max_right _ _)
  have hCeil : ⌈2/a⌉₊ ≤ H := (le_max_right _ _).trans (le_max_right _ _)
  have hRatio : 2/a ≤ (H : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hCeil)
  have hProduct := mul_le_mul_of_nonneg_left hRatio ha.le
  have he : a*(2/a)=2 := by field_simp [ha.ne']
  rw [he] at hProduct
  exact ⟨H,hFour,hL,hProduct⟩

theorem upper_anchor (a b : ℝ) (H N j : ℕ) (hH : 2 ≤ H) (hN : 1 ≤ N) (hb : b ≤ 1/16)
    (hj : j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N)) :
    NarrowPrimeBands.anchor H j ≤ (N : ℝ)^(1/16 : ℝ) :=
  (anchor_bounds a b H N j hH hj).2.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hb)
end PaperP1.FixedPowerNarrowGeometry
