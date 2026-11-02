module

public import PaperP1.Combinatorics.PlaneSupportCount
public import PaperP1.Arithmetic.OffsetLineCount
public import PaperP1.Combinatorics.OffsetVertexCover

/-! # Literal shared-prime offset supports on any primitive integer plane -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPlaneSupports

open Finset PaperP1.Arithmetic PaperP1.TripleCross PaperP1.PrimitiveTripleDirection
  PaperP1.OffsetLineData PaperP1.OffsetLinePopulation PaperP1.OffsetLineCount PaperP1.DefectivePredicate

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def plane (A : Fin 3 → ℤ) (h : ℤ) : Set (Fin 3 → ℤ) := {u | dot A u = -h}

def supports (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ) : Finset (Fin 3 → ℤ) :=
  points (offsets N L Y X (plane A h))

theorem mem_supports (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ)
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hY : ((L + 1 : ℕ) : ℝ) ≤ Y) (u : Fin 3 → ℤ) :
    u ∈ supports N L Y X A h ↔ ∃ p : ℕ, Nat.Prime p ∧ Y < (p : ℝ) ∧
      ∃ v : Fin 3 → Fin (L + 1), u = offsetVector v ∧ dot A (offsetVector v) = -h ∧
        ∀ i, p ∈ oddPrimeSupport (SaturationPrimes.value (X i) (v i)) := by
  rw [supports, chosen_points_iff_actual N L Y X (plane A h) hY]
  constructor
  · rintro ⟨p, hp, v, huv, hvplane, hodd⟩
    have hpdata := ((mem_pool N L Y X (plane A h) p).mp hp).2
    exact ⟨p, hpdata.1, hpdata.2.1, v, huv, hvplane, hodd⟩
  · rintro ⟨p, hp, hpy, v, huv, hvplane, hodd⟩
    have hpPool := (mem_pool_iff_actual N L Y X (plane A h) hN hLN hX p).mpr
      ⟨hp, hpy, v, hvplane, hodd⟩
    exact ⟨p, hpPool, v, huv, hvplane, hodd⟩

theorem on_plane (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ) :
    ∀ u ∈ supports N L Y X A h, dot A u = -h := by
  intro u hu
  obtain ⟨p, _, rfl⟩ := mem_image.mp hu
  exact offsets_on_line N L Y X (plane A h) p

theorem width (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ) :
    ∀ u ∈ supports N L Y X A h, ∀ v ∈ supports N L Y X A h, ∀ i, (u i - v i).natAbs ≤ L + 1 := by
  intro u hu v hv i
  obtain ⟨p, _, rfl⟩ := mem_image.mp hu
  obtain ⟨q, _, rfl⟩ := mem_image.mp hv
  exact point_difference_bound (offsets N L Y X (plane A h)) q p i

theorem coordinate_bound (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ) :
    ∀ u ∈ supports N L Y X A h, ∀ i, (u i).natAbs ≤ L + 1 := by
  intro u hu i
  obtain ⟨p, _, rfl⟩ := mem_image.mp hu
  have hi := (offsets N L Y X (plane A h) p i).isLt
  change (((offsets N L Y X (plane A h) p i).val : ℤ) - 1).natAbs ≤ L + 1
  have hz : |((offsets N L Y X (plane A h) p i).val : ℤ) - 1| ≤ (L + 1 : ℕ) :=
    abs_le.mpr ⟨by omega, by omega⟩
  rw [Int.abs_eq_natAbs] at hz
  exact_mod_cast hz

theorem covers_actual (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ)
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hY : ((L + 1 : ℕ) : ℝ) ≤ Y) (D : Finset (Fin 3 × ℤ)) :
    OffsetVertexCover.Covers (supports N L Y X A h) D ↔
      ∀ p : ℕ, Nat.Prime p → Y < (p : ℝ) → ∀ v : Fin 3 → Fin (L + 1),
        dot A (offsetVector v) = -h →
        (∀ i, p ∈ oddPrimeSupport (SaturationPrimes.value (X i) (v i))) →
        ∃ i : Fin 3, (i, offsetVector v i) ∈ D := by
  constructor
  · intro hc p hp hpy v hv hodd
    exact hc (offsetVector v) ((mem_supports N L Y X A h hN hLN hX hY _).mpr
      ⟨p, hp, hpy, v, rfl, hv, hodd⟩)
  · intro hc u hu
    obtain ⟨p, hp, hpy, v, rfl, hv, hodd⟩ := (mem_supports N L Y X A h hN hLN hX hY u).mp hu
    exact hc p hp hpy v hv hodd

theorem on_integer_line_subset (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ)
    (hY : ((L + 1 : ℕ) : ℝ) ≤ Y) (line : Set (Fin 3 → ℤ)) :
    (supports N L Y X A h).filter (fun u ↦ u ∈ line) ⊆ points (offsets N L Y X line) := by
  intro u hu
  obtain ⟨huS, huLine⟩ := mem_filter.mp hu
  obtain ⟨p, hp, v, huv, _hvPlane, hodd⟩ :=
    (chosen_points_iff_actual N L Y X (plane A h) hY u).mp huS
  have hpdata := (mem_pool N L Y X (plane A h) p).mp hp
  have hvLine : offsetVector v ∈ line := by simpa only [huv] using huLine
  have hpLine : p ∈ pool N L Y X line := (mem_pool N L Y X line p).mpr
    ⟨hpdata.1, hpdata.2.1, hpdata.2.2.1, v, hvLine, hodd⟩
  exact (chosen_points_iff_actual N L Y X line hY u).mpr ⟨p, hpLine, v, huv, hvLine, hodd⟩

def integerLine (a d : Fin 3 → ℤ) : Set (Fin 3 → ℤ) :=
  {u | ∃ t : ℤ, ∀ i, u i = a i + t * d i}

theorem integer_line_collinear (a d : Fin 3 → ℤ) : CollinearSet (integerLine a d) := by
  intro u hu v hv z hz i j
  obtain ⟨s, hs⟩ := hu
  obtain ⟨t, ht⟩ := hv
  obtain ⟨r, hr⟩ := hz
  rw [ht i, hs i, hr j, hs j, ht j, hr i]
  ring

theorem majorant_nonneg (N L : ℕ) (Y : ℝ) (hN : 10 ≤ N) (hY : 1 < Y) :
    0 ≤ sourceMajorant N L Y := by
  have hn : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hB : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)
  have hp : (1 : ℝ) ≤ 6 * N * ((L + 1 : ℕ) : ℝ) := by nlinarith only [hn, hB]
  have hlog := Real.log_nonneg hp
  have hlogY := Real.log_pos hY
  unfold sourceMajorant
  positivity

theorem finite_count (N L : ℕ) (Y : ℝ) (X : Fin 3 → ℕ) (A : Fin 3 → ℤ) (h : ℤ)
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hYB : ((L + 1 : ℕ) : ℝ) ≤ Y) (hY : 1 < Y) (hA : Primitive A) :
    ((supports N L Y X A h).card : ℝ) ≤ sourceMajorant N L Y +
      4 * (((L + 1 : ℕ) : ℝ) ^ 2) / height A := by
  apply PlaneSupportCount.finite_bound (L + 1) (supports N L Y X A h) A (-h)
    (sourceMajorant N L Y) hA (majorant_nonneg N L Y hN hY)
    (on_plane N L Y X A h) (width N L Y X A h)
  intro a d _hd
  exact (show (((supports N L Y X A h).filter fun u ↦ ∃ t : ℤ, ∀ i, u i = a i + t * d i).card : ℝ) ≤
    ((points (offsets N L Y X (integerLine a d))).card : ℝ) by
      exact_mod_cast card_le_card (on_integer_line_subset N L Y X A h hYB (integerLine a d))).trans
    (distinct_offsets_le_sourceMajorant N L Y X (integerLine a d) hN hLN hX hinj hdirect
      (integer_line_collinear a d) hY)

end PaperP1.OffsetPlaneSupports
