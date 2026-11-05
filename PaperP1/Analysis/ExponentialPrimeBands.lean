module

public import PaperP1.Analysis.PrimeLogarithmicBands
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Actual positive logarithmic prime mass between two exponential cutoffs

For each fixed0<a<1 the prime band [exp(aH),exp(H)] has mass at least bH
for an internal positive constant b, beyond one threshold before H.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExponentialPrimeBands

open Finset DefectCounting PrimeLogarithmicBands

theorem exists_band (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ b : ℝ, 0 < b ∧ ∃ H₀ : ℝ, ∀ H ≥ H₀,
      ∃ T : Finset ℕ, T ⊆ smallPrimesUpTo ⌊Real.exp H⌋₊ ∧
        (∀ p ∈ T, Real.exp (a * H) ≤ (p : ℝ)) ∧ b * H ≤ mass T := by
  obtain ⟨Z₀, hZ₀, hmass⟩ := uniform_bands_lower
  let d := 1 - a
  have hd : 0 < d := by dsimp only [d]; linarith only [ha1]
  have hl16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let b := d / (16 * Real.log 16)
  have hb : 0 < b := by dsimp only [b]; positivity
  refine ⟨b, hb, max 0 (max (Real.log Z₀ / a) (2 * (Real.log 2 + Real.log 16) / d)), ?_⟩
  intro H hH
  have hH0 : 0 ≤ H := (le_max_left _ _).trans hH
  have hHZ : Real.log Z₀ / a ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHsize : 2 * (Real.log 2 + Real.log 16) ≤ d * H := by
    have hh := (div_le_iff₀ hd).mp ((le_max_right _ _).trans ((le_max_right _ _).trans hH))
    nlinarith only [hh]
  let Z := ⌈Real.exp (a * H)⌉₊
  have hZreal : Real.exp (a * H) ≤ (Z : ℝ) := Nat.le_ceil _
  have hZbig : Z₀ ≤ Z := by
    have hh : Real.log Z₀ ≤ a * H := by
      have hh := (div_le_iff₀ ha).mp hHZ
      nlinarith only [hh]
    have h := Real.exp_le_exp.mpr hh
    rw [Real.exp_log (by exact_mod_cast (show 0 < Z₀ by omega))] at h
    exact_mod_cast h.trans hZreal
  have he1 : 1 ≤ Real.exp (a * H) := Real.one_le_exp (mul_nonneg ha.le hH0)
  have hZupper : (Z : ℝ) ≤ 2 * Real.exp (a * H) := by
    have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg (a * H))).le
    change (Z : ℝ) ≤ Real.exp (a * H) + 1 at hh
    linarith only [hh, he1]
  let u := (d * H - Real.log 2) / Real.log 16
  let k := ⌊u⌋₊
  have hu0 : 0 ≤ u := by dsimp only [u]; apply div_nonneg <;> linarith only [hHsize, hl2, hl16]
  have hkupper : (k : ℝ) * Real.log 16 ≤ d * H - Real.log 2 := by
    have hh : (k : ℝ) ≤ (d * H - Real.log 2) / Real.log 16 := Nat.floor_le hu0
    exact (le_div_iff₀ hl16).mp hh
  have hklower : d * H / (2 * Real.log 16) ≤ (k : ℝ) := by
    have hh := Nat.sub_one_lt_floor u
    have hh' : u < (k : ℝ) + 1 := by change u - 1 < (k : ℝ) at hh; linarith only [hh]
    have hx := (div_lt_iff₀ hl16).mp hh'
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log 16)).mpr
    nlinarith only [hx, hHsize]
  have hpower : (((16 : ℕ) ^ k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log 16) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  have hcut : Z * 16 ^ k ≤ ⌊Real.exp H⌋₊ := by
    apply (Nat.le_floor_iff (Real.exp_nonneg H)).mpr
    rw [Nat.cast_mul, hpower]
    calc
      _ ≤ 2 * Real.exp (a * H) * Real.exp ((k : ℝ) * Real.log 16) :=
        mul_le_mul_of_nonneg_right hZupper (Real.exp_nonneg _)
      _ = Real.exp (Real.log 2 + a * H + (k : ℝ) * Real.log 16) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [d] at hkupper; linarith only [hkupper])
  refine ⟨bands Z k, ?_, ?_, ?_⟩
  · intro p hp
    have hh := bands_properties hp
    exact mem_smallPrimesUpTo.mpr ⟨hh.1, hh.2.2.trans hcut⟩
  · intro p hp
    exact hZreal.trans (by exact_mod_cast (bands_properties hp).2.1.le)
  · have hh : b * H ≤ (k : ℝ) / 8 := by
      have hh := div_le_div_of_nonneg_right hklower (by norm_num : (0 : ℝ) ≤ 8)
      convert hh using 1
      dsimp only [b]
      ring
    exact hh.trans (hmass Z hZbig k)

end PaperP1.ExponentialPrimeBands
