module

public import PaperP1.Arithmetic.PolynomialPrimeCover

/-! # Internally supplied logarithmic mass of disjoint prime bands

Every sufficiently large interval (P,16P] has logarithmic reciprocal prime mass
at least1/8. Actual disjoint geometric bands accumulate this mass without loss.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeLogarithmicBands

open Finset DefectCounting PolynomialPrimeCover

def mass (S : Finset ℕ) : ℝ := ∑ p ∈ S, Real.log p / p

theorem mass_nonneg (S : Finset ℕ) : 0 ≤ mass S :=
  sum_nonneg (fun p _ ↦ div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))

theorem interval_lower : ∃ P₀ : ℕ, 16 ≤ P₀ ∧ ∀ P ≥ P₀,
    (1 / 8 : ℝ) ≤ mass (interval P) := by
  obtain ⟨P₀, hP₀, hcount⟩ := interval_count_lower
  refine ⟨P₀, hP₀, ?_⟩
  intro P hP
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlog : 0 < Real.log P := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hc := (div_le_iff₀ hlog).mp (hcount P hP)
  have hfirst : (1 / 8 : ℝ) ≤ ((interval P).card : ℝ) * (Real.log P / (16 * P)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * P)).mpr
    nlinarith only [hc]
  refine hfirst.trans ?_
  calc
    _ = ∑ _p ∈ interval P, Real.log P / (16 * P) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpprime, hpl, hpu⟩ := (mem_interval P p).mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hlogp : Real.log P ≤ Real.log p := Real.log_le_log hPpos (by exact_mod_cast hpl.le)
      have hpupper : (p : ℝ) ≤ 16 * P := by exact_mod_cast hpu
      exact (div_le_div_of_nonneg_left hlog.le hp0 hpupper).trans
        (div_le_div_of_nonneg_right hlogp hp0.le)

def bands (Z k : ℕ) : Finset ℕ := (range k).biUnion fun j ↦ interval (Z * 16 ^ j)

theorem band_disjoint {Z i j : ℕ} (hij : i < j) :
    Disjoint (interval (Z * 16 ^ i)) (interval (Z * 16 ^ j)) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hi := (mem_interval _ _).mp hpi
  have hj := (mem_interval _ _).mp hpj
  have hpow : Z * 16 ^ (i + 1) ≤ Z * 16 ^ j :=
    Nat.mul_le_mul_left Z (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 16) (by omega))
  rw [pow_succ] at hpow
  nlinarith only [hi.2.2, hj.2.1, hpow]

theorem band_pairwise (Z k : ℕ) :
    (range k : Set ℕ).PairwiseDisjoint (fun j ↦ interval (Z * 16 ^ j)) := by
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact band_disjoint h
  · exact (band_disjoint h).symm

theorem bands_properties {Z k p : ℕ} (hp : p ∈ bands Z k) :
    p.Prime ∧ Z < p ∧ p ≤ Z * 16 ^ k := by
  obtain ⟨j, hj, hp⟩ := mem_biUnion.mp hp
  obtain ⟨hpp, hpl, hpu⟩ := (mem_interval _ _).mp hp
  have hlow : Z ≤ Z * 16 ^ j := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left Z (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 16))
  have hhigh : Z * 16 ^ (j + 1) ≤ Z * 16 ^ k :=
    Nat.mul_le_mul_left Z (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 16)
      (by have := mem_range.mp hj; omega))
  rw [pow_succ] at hhigh
  exact ⟨hpp, hlow.trans_lt hpl, (by nlinarith only [hpu, hhigh])⟩

theorem bands_subset (Z k : ℕ) : bands Z k ⊆ smallPrimesUpTo (Z * 16 ^ k) := by
  intro p hp
  have hh := bands_properties hp
  exact mem_smallPrimesUpTo.mpr ⟨hh.1, hh.2.2⟩

theorem bands_mass (Z k : ℕ) :
    mass (bands Z k) = ∑ j ∈ range k, mass (interval (Z * 16 ^ j)) := by
  exact sum_biUnion (band_pairwise Z k)

theorem uniform_bands_lower : ∃ Z₀ : ℕ, 16 ≤ Z₀ ∧ ∀ Z ≥ Z₀, ∀ k : ℕ,
    (k : ℝ) / 8 ≤ mass (bands Z k) := by
  obtain ⟨Z₀, hZ₀, hl⟩ := interval_lower
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ k
  rw [bands_mass]
  calc
    _ = ∑ _j ∈ range k, (1 / 8 : ℝ) := by simp only [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      apply hl
      exact hZ.trans (by simpa only [mul_one] using
        Nat.mul_le_mul_left Z (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 16)))

end PaperP1.PrimeLogarithmicBands
