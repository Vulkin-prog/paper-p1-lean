module

public import PaperP1.Arithmetic.GoodEdgeCompression
public import PaperP1.Arithmetic.NormalizedPairGeometry
public import PaperP1.Arithmetic.PrivateWindowPrimes

/-! # The exact private-prime condition above a fixed cutoff is nondefectivity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedPrivateDefects

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.GoodEdgeCompression PaperP1.DefectivePredicate

theorem privateAbove_iff_nondefective {H : ℕ} (S : Finset ℕ)
    (hdist : ∀ n ∈ S, ∀ m ∈ S, n ≠ m → Nat.dist n m < H) :
    PrivateAbove (H : ℝ) S ↔ ∀ n ∈ S, ¬HDefective H n := by
  classical
  constructor
  · intro h n hn hdef
    obtain ⟨p, hp, hHp, hparity, _⟩ := h n hn
    exact hparity (hdef p hp (by exact_mod_cast hHp))
  · intro h n hn
    have hnot := h n hn
    simp only [HDefective, not_forall] at hnot
    obtain ⟨p, hp, hHp, hparity⟩ := hnot
    refine ⟨p, hp, by exact_mod_cast hHp, hparity, ?_⟩
    intro m hm hmn
    have hpn : p ∣ n := by
      by_contra hnotdvd
      exact hparity (by simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnotdvd])
    have hpm := PrivateWindowPrimes.not_dvd_of_dvd_and_dist_lt hpn hmn.symm hHp
      (hdist n hn m hm hmn.symm)
    simp [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hpm]

theorem normalized_dist_bound {a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hunit : (units a b x y L).Nonempty) {n m : ℕ}
    (hn : n ∈ NormalizedWindowSets.union a b x y L) (hm : m ∈ NormalizedWindowSets.union a b x y L) :
    Nat.dist n m ≤ 2 * (b * L) := by
  obtain ⟨u, hu⟩ := hunit
  have hnBounds := NormalizedPairGeometry.union_bounds hab hx hy u.1 u.2 (mem_units.mp hu) n hn
  have hmBounds := NormalizedPairGeometry.union_bounds hab hx hy u.1 u.2 (mem_units.mp hu) m hm
  rw [Nat.dist]
  omega

theorem normalized_private_iff {H a b x y L : ℕ} (hb : 0 < b) (hab : a ≤ b)
    (hx : 0 < x) (hy : 0 < y) (hunit : (units a b x y L).Nonempty)
    (hcut : 2 * b * (L + 1) ≤ H) :
    PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b x y L) ↔
      ∀ n ∈ NormalizedWindowSets.union a b x y L, ¬HDefective H n := by
  apply privateAbove_iff_nondefective
  intro n hn m hm _
  have hd := normalized_dist_bound hab hx hy hunit hn hm
  nlinarith

theorem normalized_bad_witness {H a b x y L : ℕ} (hb : 0 < b) (hab : a ≤ b)
    (hx : 0 < x) (hy : 0 < y) (hunit : (units a b x y L).Nonempty)
    (hcut : 2 * b * (L + 1) ≤ H)
    (hbad : ¬PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b x y L)) :
    ∃ n ∈ NormalizedWindowSets.union a b x y L, HDefective H n := by
  classical
  rw [normalized_private_iff hb hab hx hy hunit hcut] at hbad
  push Not at hbad
  exact hbad

end PaperP1.NormalizedPrivateDefects
