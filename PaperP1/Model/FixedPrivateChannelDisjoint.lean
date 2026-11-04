module

public import PaperP1.Arithmetic.SmallChannelUniqueness
public import PaperP1.Model.CompatibleChannelEdges
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Different fixed reduced private channels have disjoint actual edge sets

The cutoffs may vary independently by channel. Disjointness follows from
the actual source orientations and the exact geometric slope determinant.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPrivateChannelDisjoint

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem reduced_equal {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hab : a.Coprime b) (hcd : c.Coprime d) (hslope : a * d = b * c) : a = c ∧ b = d := by
  have hac : a ∣ c := hab.dvd_mul_left.mp ⟨d, hslope.symm⟩
  have hca : c ∣ a := hcd.dvd_mul_left.mp ⟨b, by nlinarith only [hslope]⟩
  have heq : a = c := Nat.le_antisymm (Nat.le_of_dvd hc hac) (Nat.le_of_dvd ha hca)
  refine ⟨heq, ?_⟩
  subst c
  have hh : a * d = a * b := by simpa only [mul_comm b a] using hslope
  exact (Nat.eq_of_mul_eq_mul_left ha hh).symm

theorem same_channel {N H J a b c d L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hc : 0 < c)
    (hab : a < b) (hcd : c < d) (hcopA : a.Coprime b) (hcopC : c.Coprime d)
    (hlargeA : (a + b) * (L + 1) < N) (hlargeC : (c + d) * (L + 1) < N)
    (haB : a ≤ 2 * (L + 1)) (hbB : b ≤ 2 * (L + 1))
    (hcB : c ≤ 2 * (L + 1)) (hdB : d ≤ 2 * (L + 1)) (hfar : 16 * (L + 1) ^ 3 < N)
    {e : Finset ℕ} (heA : e ∈ PrivateChannelActivity.pairs N H a b L)
    (heC : e ∈ PrivateChannelActivity.pairs N J c d L) : a = c ∧ b = d := by
  obtain ⟨xy, hxy, hxyE⟩ := mem_image.mp heA
  obtain ⟨uv, huv, huvE⟩ := mem_image.mp heC
  have hxylt := PrivateChannelSources.good_sources_order hN hab hlargeA hxy
  have huvlt := PrivateChannelSources.good_sources_order hN hcd hlargeC huv
  have hpairs : ({xy.1, xy.2} : Finset ℕ) = {uv.1, uv.2} := hxyE.trans huvE.symm
  have hx : xy.1 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← hpairs]; simp
  have hy : xy.2 ∈ ({uv.1, uv.2} : Finset ℕ) := by rw [← hpairs]; simp
  simp only [mem_insert, mem_singleton] at hx hy
  have huvxy : uv = xy := Prod.ext (by omega) (by omega)
  subst uv
  have huA := PrivateChannelSources.good_sources_subset_unitSources N H a b L hxy
  have huC := PrivateChannelSources.good_sources_subset_unitSources N J c d L huv
  have hgA := FixedChannelLinearCount.unit_alignment (by omega : 0 < N) huA
  have hgC := FixedChannelLinearCount.unit_alignment (by omega : 0 < N) huC
  have hfarY : 16 * (L + 1) ^ 3 < xy.2 :=
    hfar.trans_le (mem_Ico.mp (PrivateChannelSources.mem_goodSources.mp hxy).2.1).1
  apply reduced_equal ha hc hcopA hcopC
  apply SmallChannelUniqueness.same_slope a b c d xy.1 xy.2 L haB hbB hcB hdB hfarY
  · simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using hgA
  · simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using hgC

theorem uniform_geometry (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < L ∧ 16 * (L + 1) ^ 3 < N ∧ ∀ ab ∈ F,
        (ab.1 + ab.2) * (L + 1) < N ∧ ab.1 ≤ 2 * (L + 1) ∧ ab.2 ≤ 2 * (L + 1) := by
  let Q := F.sup Prod.snd
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (Q + 2)
  obtain ⟨NF, hf⟩ := CriticalPolynomialScale.polynomial_lt_scale C 16 (by norm_num) 3
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((2 * Q : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max 2 (max NG (max NF NS)), by omega, ?_⟩
  intro N hN L hband
  have hgeom := hg N (by omega) L hband
  have hfar : 16 * (L + 1) ^ 3 < N := by exact_mod_cast hf N (by omega) L hband
  have hsize : 2 * Q * (L + 1) < N := by
    have hh := hs N (by omega) L hband
    simp only [pow_one] at hh
    exact_mod_cast hh
  refine ⟨by omega, hfar, ?_⟩
  intro ab hab
  have hbQ : ab.2 ≤ Q := le_sup (f := Prod.snd) hab
  have haQ : ab.1 ≤ Q := (hF ab hab).2.le.trans hbQ
  exact ⟨(Nat.mul_le_mul_right (L + 1) (by omega : ab.1 + ab.2 ≤ 2 * Q)).trans_lt hsize,
    by omega, by omega⟩

theorem uniform_disjoint (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.1.Coprime ab.2) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ × ℕ → ℕ,
      ∀ ab ∈ F, ∀ cd ∈ F, ab ≠ cd →
        Disjoint (CompatibleChannelEdges.edges N (H ab) ab.1 ab.2 L)
          (CompatibleChannelEdges.edges N (H cd) cd.1 cd.2 L) := by
  obtain ⟨N₀, hN₀, hg⟩ := uniform_geometry F (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1⟩) C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband H ab hab cd hcd hne
  obtain ⟨_hL, hfar, hdata⟩ := hg N hN L hband
  obtain ⟨hlargeA, haB, hbB⟩ := hdata ab hab
  obtain ⟨hlargeC, hcB, hdB⟩ := hdata cd hcd
  apply disjoint_left.mpr
  intro e heA heC
  obtain ⟨haeq, hbeq⟩ := same_channel (by omega) (hF ab hab).1 (hF cd hcd).1
    (hF ab hab).2.1 (hF cd hcd).2.1 (hF ab hab).2.2 (hF cd hcd).2.2
    hlargeA hlargeC haB hbB hcB hdB hfar (mem_filter.mp heA).1 (mem_filter.mp heC).1
  exact hne (Prod.ext haeq hbeq)

end PaperP1.FixedPrivateChannelDisjoint
