module

public import PaperP1.Arithmetic.DefectAffineBounds

@[expose] public section

/-! # Exact two-defect windows after a fixed real affine interval change -/

namespace PaperP1.DefectAffineWindows

open Finset DefectivePredicate DefectAffineIntervals TwoDefectHosts

/-- Integer starts y in [aN+b,2aN+b), with two defective integer vertices
inside [y-a, y-a+aL]. This is the affine image of the complete vertex window. -/
noncomputable def affineDyadicTwoDefectWindows
    (a shift : ℝ) (N H L : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 (affineHeight a shift (2 * N))).filter fun y =>
    a * N + shift ≤ (y : ℝ) ∧ (y : ℝ) < a * (2 * N : ℕ) + shift ∧
      ∃ n m : ℕ,
        (y : ℝ) - a ≤ n ∧ (n : ℝ) ≤ (y : ℝ) - a + a * L ∧
        (y : ℝ) - a ≤ m ∧ (m : ℝ) ≤ (y : ℝ) - a + a * L ∧
        n ≠ m ∧ HDefective H n ∧ HDefective H m

theorem mem_affineDyadicTwoDefectWindows {a shift : ℝ} {N H L y : ℕ} :
    y ∈ affineDyadicTwoDefectWindows a shift N H L ↔
      1 ≤ y ∧ y ≤ affineHeight a shift (2 * N) ∧
      a * N + shift ≤ (y : ℝ) ∧ (y : ℝ) < a * (2 * N : ℕ) + shift ∧
      ∃ n m : ℕ,
        (y : ℝ) - a ≤ n ∧ (n : ℝ) ≤ (y : ℝ) - a + a * L ∧
        (y : ℝ) - a ≤ m ∧ (m : ℝ) ≤ (y : ℝ) - a + a * L ∧
        n ≠ m ∧ HDefective H n ∧ HDefective H m := by
  classical
  simp [affineDyadicTwoDefectWindows, and_assoc]

theorem rounded_left_le_vertex
    {a : ℝ} {y n : ℕ} (hleft : (y : ℝ) - a ≤ n) :
    y - ⌊a⌋₊ ≤ n := by
  have hfloor : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  have hreal : (y : ℝ) < (n : ℝ) + ⌊a⌋₊ + 1 := by linarith
  have hnat : y < n + ⌊a⌋₊ + 1 := by exact_mod_cast hreal
  omega

theorem rounded_left_add_width_ge_vertex
    {a : ℝ} (ha : 0 ≤ a) {y n L : ℕ}
    (hy : ⌊a⌋₊ ≤ y)
    (hright : (n : ℝ) ≤ (y : ℝ) - a + a * L) :
    n ≤ (y - ⌊a⌋₊) + affineWidth a L := by
  have hfloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hwidth : a * L ≤ (affineWidth a L : ℝ) := Nat.le_ceil _
  have hbase : ((y - ⌊a⌋₊ : ℕ) : ℝ) = (y : ℝ) - ⌊a⌋₊ := Nat.cast_sub hy
  have hreal : (n : ℝ) ≤ ((y - ⌊a⌋₊ : ℕ) : ℝ) + affineWidth a L := by
    linarith
  exact_mod_cast hreal

theorem card_affineDyadicTwoDefectWindows_le
    {a shift : ℝ} (ha : 0 ≤ a) {N H L : ℕ}
    (hbase : (⌊a⌋₊ + 1 : ℕ) ≤ a * N + shift) :
    (affineDyadicTwoDefectWindows a shift N H L).card ≤
      (twoDefectStarts H (affineWidth a L) (affineHeight a shift (2 * N))).card := by
  classical
  have hlow : ∀ y ∈ affineDyadicTwoDefectWindows a shift N H L, ⌊a⌋₊ + 1 ≤ y := by
    intro y hy
    have h := (mem_affineDyadicTwoDefectWindows.mp hy).2.2.1
    have hreal : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ y := hbase.trans h
    exact_mod_cast hreal
  have hinj : Set.InjOn (fun y : ℕ => y - ⌊a⌋₊)
      (affineDyadicTwoDefectWindows a shift N H L : Set ℕ) := by
    intro y hy z hz heq
    change y - ⌊a⌋₊ = z - ⌊a⌋₊ at heq
    have hylo := hlow y hy
    have hzlo := hlow z hz
    omega
  have hsub :
      (affineDyadicTwoDefectWindows a shift N H L).image (fun y => y - ⌊a⌋₊) ⊆
        twoDefectStarts H (affineWidth a L) (affineHeight a shift (2 * N)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨_hy1, hyX, _hylo, _hyhi, n, m, hnlo, hnhi, hmlo, hmhi, hnm, hdn, hdm⟩ :=
      mem_affineDyadicTwoDefectWindows.mp hy
    have hyfloor : ⌊a⌋₊ ≤ y := by have := hlow y hy; omega
    have hnBase := rounded_left_le_vertex hnlo
    have hmBase := rounded_left_le_vertex hmlo
    have hnTop := rounded_left_add_width_ge_vertex ha hyfloor hnhi
    have hmTop := rounded_left_add_width_ge_vertex ha hyfloor hmhi
    let i := n - (y - ⌊a⌋₊)
    let j := m - (y - ⌊a⌋₊)
    have hi : i ≤ affineWidth a L := by dsimp [i]; omega
    have hj : j ≤ affineWidth a L := by dsimp [j]; omega
    have hnrep : y - ⌊a⌋₊ + i = n := by dsimp [i]; omega
    have hmrep : y - ⌊a⌋₊ + j = m := by dsimp [j]; omega
    apply mem_twoDefectStarts.mpr
    refine ⟨by have := hlow y hy; omega, by omega, i, hi, j, hj, ?_, ?_, ?_⟩
    · intro hij
      apply hnm
      omega
    · simpa only [hnrep] using hdn
    · simpa only [hmrep] using hdm
  calc
    _ = ((affineDyadicTwoDefectWindows a shift N H L).image (fun y => y - ⌊a⌋₊)).card :=
      (card_image_of_injOn hinj).symm
    _ ≤ _ := card_le_card hsub

/-- Fixed a>0 and real translation are chosen before the threshold. The
vertex endpoints are the literal affine images, without dropping the boundary. -/
theorem affine_dyadic_two_defect_windows_le_rpow_eventually
    (a shift D E : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H L : ℕ,
      (H : ℝ) ≤ D * Real.log N → (L : ℝ) ≤ E * Real.log N →
      ((affineDyadicTwoDefectWindows a shift N H L).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Ncore, hcore⟩ := DefectAffineBounds.affine_two_defect_cover_bound_eventually
    a shift 2 D E ha (by norm_num) hD hE ε hε
  refine ⟨max Ncore ⌈(((⌊a⌋₊ + 1 : ℕ) : ℝ) + |shift|) / a⌉₊, ?_⟩
  intro N hN H L hH hL
  have hNcore : Ncore ≤ N := (le_max_left _ _).trans hN
  have hthreshold : (((⌊a⌋₊ + 1 : ℕ) : ℝ) + |shift|) / a ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hbase : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ a * N + shift := by
    have hmul := (div_le_iff₀ ha).mp hthreshold
    nlinarith [neg_le_abs shift]
  have hcard := card_affineDyadicTwoDefectWindows_le (H := H) (L := L) ha.le hbase
  exact (by exact_mod_cast hcard :
    ((affineDyadicTwoDefectWindows a shift N H L).card : ℝ) ≤
      ((twoDefectStarts H (affineWidth a L) (affineHeight a shift (2 * N))).card : ℝ)).trans
        (hcore N hNcore H L (2 * N) hH hL (by norm_num))

end PaperP1.DefectAffineWindows

