module

public import PaperP1.Arithmetic.NormalizedUnitCount

/-! # Common integer dilations preserve exact intersection counts and their reduced-ratio budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledNormalizedIntersections

open Finset PaperP1.NormalizedWindowSets PaperP1.FiniteEvenSquareClasses

theorem normalized_scale (c b x L : ℕ) :
    normalized (c * b) x L = dilate c (normalized b x L) := by
  unfold normalized dilate
  rw [image_image]
  congr 1
  funext n
  exact Nat.mul_assoc c b n

theorem dilate_inter {c : ℕ} (hc : 0 < c) (S T : Finset ℕ) :
    dilate c (S ∩ T) = dilate c S ∩ dilate c T := by
  unfold dilate
  exact image_inter S T (mul_right_injective₀ hc.ne')

theorem scaled_intersection_card {c : ℕ} (hc : 0 < c) (a b x y L : ℕ) :
    (normalized (c * b) x L ∩ normalized (c * a) y L).card =
      (normalized b x L ∩ normalized a y L).card := by
  rw [normalized_scale, normalized_scale, ← dilate_inter hc, dilate,
    card_image_of_injective _ (mul_right_injective₀ hc.ne')]

theorem reduced_intersection_bound {c u v x y L : ℕ} (hc : 0 < c) (hu : 0 < u) (hv : 0 < v)
    (hx : 0 < x) (hy : 0 < y) :
    ((normalized (c * v) x L ∩ normalized (c * u) y L).card : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * (Nat.gcd u v : ℝ)) / v + 1 := by
  let g := Nat.gcd u v
  let a := u / g
  let b := v / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left v hu
  have hga : g * a = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hgb : g * b = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have ha : 0 < a := by nlinarith only [hga, hu]
  have hb : 0 < b := by nlinarith only [hgb, hv]
  have hcop : a.Coprime b := Nat.gcd_div_gcd_div_gcd_of_pos_left hu
  have hcu : (c * g) * a = c * u := by rw [Nat.mul_assoc, hga]
  have hcv : (c * g) * b = c * v := by rw [Nat.mul_assoc, hgb]
  have hcard : (normalized (c * v) x L ∩ normalized (c * u) y L).card =
      (normalized b x L ∩ normalized a y L).card := by
    rw [← hcv, ← hcu]
    exact scaled_intersection_card (Nat.mul_pos hc hg) a b x y L
  have hgbR : (g : ℝ) * b = v := by exact_mod_cast hgb
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hratio : (((L + 1 : ℕ) : ℝ)) / b = (((L + 1 : ℕ) : ℝ) * (g : ℝ)) / v := by
    rw [← hgbR]
    field_simp
  rw [hcard]
  exact (NormalizedUnitCount.intersection_card_bound ha hb hcop hx hy).trans_eq (by rw [hratio])

end PaperP1.ScaledNormalizedIntersections
