module

public import PaperP1.Arithmetic.RationalTripleSmallRatios

/-! # Main 14.2, unique extremality, and the next rational-overlap value -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleOverlap

open PaperP1.RationalTripleDensity PaperP1.RationalTripleSmallRatios

theorem primitive_swap_last {u v w : ℕ}
    (h : Nat.gcd (Nat.gcd u v) w = 1) : Nat.gcd (Nat.gcd u w) v = 1 := by
  rw [Nat.gcd_assoc, Nat.gcd_comm w v, ← Nat.gcd_assoc]
  exact h

theorem primitive_cycle {u v w : ℕ}
    (h : Nat.gcd (Nat.gcd u v) w = 1) : Nat.gcd (Nat.gcd v w) u = 1 := by
  rw [Nat.gcd_comm (Nat.gcd v w) u, ← Nat.gcd_assoc]
  exact h

theorem scaled_primitive {a b c d : ℕ} (hab : Nat.Coprime a b)
    (h : Nat.gcd (Nat.gcd (a * d) (b * d)) c = 1) : Nat.Coprime c d := by
  rw [Nat.gcd_mul_right, hab.gcd_eq_one, Nat.one_mul] at h
  change Nat.gcd c d = 1
  rwa [Nat.gcd_comm]

theorem density_swap_last (a b c : ℕ) : density a b c = density a c b := by
  unfold density
  rw [pairDensity_comm c b, max_comm c b]
  ring

/-- A quantitative rigidity statement for the primitive rational geometry. -/
theorem gap {u v w : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Nat.gcd (Nat.gcd u v) w = 1) :
    (u = 10 ∧ v = 12 ∧ w = 15) ∨ density u v w ≤ 11 / 18 := by
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have hw : 0 < w := by omega
  by_cases h1 : 5 * Nat.gcd u v ≤ v
  · by_cases h2 : 5 * Nat.gcd u w ≤ w
    · by_cases h3 : 5 * Nat.gcd v w ≤ w
      · right
        exact (all_pairs_high hu huv hvw h1 h2 h3).trans (by norm_num)
      · obtain ⟨d, hd, hratio | hratio⟩ := small_pair hv hvw (by omega) (by omega : w < 5 * Nat.gcd v w)
        · obtain ⟨hvd, hwd⟩ := hratio
          have hcd : Nat.Coprime u d := scaled_primitive (a := 2) (b := 3) (by norm_num [Nat.Coprime])
            (by simpa only [hvd, hwd] using primitive_cycle hprimitive)
          rcases ratio23_gap hd hu hcd (by omega) (by omega) (by omega) (by omega) with hbad | hbound
          · omega
          · right
            rw [density_cycle u v w, hvd, hwd]
            exact hbound
        · obtain ⟨hvd, hwd⟩ := hratio
          have hcd : Nat.Coprime u d := scaled_primitive (a := 3) (b := 4) (by norm_num [Nat.Coprime])
            (by simpa only [hvd, hwd] using primitive_cycle hprimitive)
          right
          rw [density_cycle u v w, hvd, hwd]
          exact ratio34_gap hd hu hcd (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨d, hd, hratio | hratio⟩ := small_pair hu (by omega : u < w) hw2u (by omega : w < 5 * Nat.gcd u w)
      · obtain ⟨hud, hwd⟩ := hratio
        have hcd : Nat.Coprime v d := scaled_primitive (a := 2) (b := 3) (by norm_num [Nat.Coprime])
          (by simpa only [hud, hwd] using primitive_swap_last hprimitive)
        rcases ratio23_gap hd hv hcd (by omega) (by omega) (by omega) (by omega) with hbad | hbound
        · left
          omega
        · right
          rw [density_swap_last u v w, hud, hwd]
          exact hbound
      · obtain ⟨hud, hwd⟩ := hratio
        have hcd : Nat.Coprime v d := scaled_primitive (a := 3) (b := 4) (by norm_num [Nat.Coprime])
          (by simpa only [hud, hwd] using primitive_swap_last hprimitive)
        right
        rw [density_swap_last u v w, hud, hwd]
        exact ratio34_gap hd hv hcd (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨d, hd, hratio | hratio⟩ := small_pair hu huv (by omega) (by omega : v < 5 * Nat.gcd u v)
    · obtain ⟨hud, hvd⟩ := hratio
      have hcd : Nat.Coprime w d := scaled_primitive (a := 2) (b := 3) (by norm_num [Nat.Coprime])
        (by simpa only [hud, hvd] using hprimitive)
      rcases ratio23_gap hd hw hcd (by omega) (by omega) (by omega) (by omega) with hbad | hbound
      · omega
      · right
        simpa only [hud, hvd] using hbound
    · obtain ⟨hud, hvd⟩ := hratio
      have hcd : Nat.Coprime w d := scaled_primitive (a := 3) (b := 4) (by norm_num [Nat.Coprime])
        (by simpa only [hud, hvd] using hprimitive)
      right
      simpa only [hud, hvd] using
        ratio34_gap hd hw hcd (by omega) (by omega) (by omega) (by omega)

theorem extremal_value : density 10 12 15 = 19 / 30 := by norm_num [density, pairDensity]

theorem next_value : density 8 9 12 = 11 / 18 := by norm_num [density, pairDensity]

theorem bound {u v w : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Nat.gcd (Nat.gcd u v) w = 1) : density u v w ≤ 19 / 30 := by
  rcases gap huv hvw hw2u hprimitive with ⟨rfl, rfl, rfl⟩ | h
  · exact extremal_value.le
  · exact h.trans (by norm_num)

theorem equality_iff {u v w : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Nat.gcd (Nat.gcd u v) w = 1) :
    density u v w = 19 / 30 ↔ u = 10 ∧ v = 12 ∧ w = 15 := by
  constructor
  · intro heq
    rcases gap huv hvw hw2u hprimitive with h | h
    · exact h
    · rw [heq] at h
      norm_num at h
  · rintro ⟨rfl, rfl, rfl⟩
    exact extremal_value

/-- The exact ordered expression in the manuscript, including its witness. -/
theorem article_14_2 {u v w : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Nat.gcd (Nat.gcd u v) w = 1) :
    (Nat.gcd u v : ℝ) / v + ((Nat.gcd u w : ℝ) + Nat.gcd v w - 1) / w ≤ 19 / 30 := by
  rw [← density_ordered huv.le hvw.le]
  exact bound huv hvw hw2u hprimitive

theorem ordered_gap {u v w : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprimitive : Nat.gcd (Nat.gcd u v) w = 1)
    (hne : ¬(u = 10 ∧ v = 12 ∧ w = 15)) :
    (Nat.gcd u v : ℝ) / v + ((Nat.gcd u w : ℝ) + Nat.gcd v w - 1) / w ≤ 11 / 18 := by
  rw [← density_ordered huv.le hvw.le]
  exact (gap huv hvw hw2u hprimitive).resolve_left hne

end PaperP1.RationalTripleOverlap
