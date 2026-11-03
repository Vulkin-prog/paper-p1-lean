module

public import PaperP1.Asymptotics.RankinCertificateCritical

/-! # Choosing fixed confinement parameters and proving the logarithmic count is o(L) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolylogConfinementScales

open PaperP1.CriticalBandScale

theorem choose_parameters (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      (1 + 1 / (k : ℝ)) * (1 + (2 + ζ) / c) < 1 + 2 / c + ε / 2 := by
  let ζ := min (c * ε / 4) (1 / 2)
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let s := 1 + (2 + ζ) / c
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / (4 * s))
  let k := max 3 (n + 1)
  have hk : 3 ≤ k := le_max_left _ _
  have hkn : (n + 1 : ℝ) ≤ k := by exact_mod_cast (le_max_right 3 (n + 1))
  have hsmall : 1 / (k : ℝ) < ε / (4 * s) :=
    (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1) hkn).trans_lt hn
  have hm := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * s)).mp hsmall
  have hzfrac : ζ / c ≤ ε / 4 := (div_le_iff₀ hc).mpr (by
    have hz := min_le_left (c * ε / 4) (1 / 2)
    change ζ ≤ _ at hz
    nlinarith)
  refine ⟨k, hk, ζ, hζ, hζ1, ?_⟩
  have heq : (1 + 1 / (k : ℝ)) * (1 + (2 + ζ) / c) =
      1 + 2 / c + ζ / c + (1 / (k : ℝ)) * s := by dsimp [s]; ring
  rw [heq]
  nlinarith [hm]

theorem logarithmic_count_sublinear (C c : ℝ) (hc : 0 < c) (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((k - 1 + ⌊Real.log N / (c * Real.log ((L + 1 : ℕ) : ℝ))⌋₊ : ℕ) : ℝ) ≤ η * L := by
  let A : ℝ := 4 / (c * lowerScale * η)
  let Bmin : ℕ := ⌈max (Real.exp A) (2 * (k : ℝ) / η + 2)⌉₊ + 2
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C Bmin
  refine ⟨max 2 NG, by omega, ?_⟩
  intro N hN L hband
  have hgeom := hg N (by omega) L hband
  have hBlo : (Bmin : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hgeom.2.1
  have hlarge : max (Real.exp A) (2 * (k : ℝ) / η + 2) ≤ ((L + 1 : ℕ) : ℝ) := by
    have hceil := Nat.le_ceil (max (Real.exp A) (2 * (k : ℝ) / η + 2))
    have hmin : (⌈max (Real.exp A) (2 * (k : ℝ) / η + 2)⌉₊ : ℝ) ≤ Bmin := by
      dsimp [Bmin]
      push_cast
      linarith
    exact hceil.trans (hmin.trans hBlo)
  have hL : 1 ≤ L := by have hb := hgeom.2.2.1; omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hBpos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by positivity
  have hlogB : 0 < Real.log ((L + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L + 1))
  have hAlog : A ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos A) ((le_max_left _ _).trans hlarge)
  have hbig : (4 : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) * (c * lowerScale * η) := by
    exact (div_le_iff₀ (mul_pos (mul_pos hc lowerScale_pos) hη)).mp hAlog
  have hcoeff : (2 : ℝ) / lowerScale ≤ η / 2 * (c * Real.log ((L + 1 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ lowerScale_pos).mpr
    nlinarith [hbig]
  have hlow := hgeom.2.2.2.2.1
  have hlogN : Real.log N ≤ (2 / lowerScale) * L := by
    rw [show (2 / lowerScale : ℝ) * L = (2 * L) / lowerScale by ring]
    apply (le_div_iff₀ lowerScale_pos).mpr
    push_cast at hlow
    nlinarith [hlow]
  have hratio : Real.log N / (c * Real.log ((L + 1 : ℕ) : ℝ)) ≤ η / 2 * L := by
    apply (div_le_iff₀ (mul_pos hc hlogB)).mpr
    have hm := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg L)
    nlinarith [hlogN, hm]
  have hNlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hfloor := Nat.floor_le (div_nonneg hNlog (mul_pos hc hlogB).le)
  have hkL : ((k - 1 : ℕ) : ℝ) ≤ η / 2 * L := by
    have hkl := (le_max_right _ _).trans hlarge
    have hkl' : 2 * (k : ℝ) / η + 2 ≤ (L : ℝ) + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using hkl
    have hmul := (div_le_iff₀ hη).mp (show 2 * (k : ℝ) / η ≤ (L : ℝ) - 1 by linarith)
    have hsub : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
    nlinarith [hmul, hsub]
  rw [Nat.cast_add]
  linarith [hfloor, hratio, hkL]

end PaperP1.PolylogConfinementScales
