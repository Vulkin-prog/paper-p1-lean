module

public import PaperP1.Asymptotics.GeneralPlanarMotifCount
public import PaperP1.Combinatorics.TransverseMotifSelection
public import PaperP1.Model.TripleProbabilityBound
public import PaperP1.Arithmetic.TwoPointSquareClasses
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Companion T20.6: many transverse products on prescribed planes, with actual affine mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ManyPlanarSquareProducts

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TripleCross PaperP1.TransverseMotifs PaperP1.SmoothMotifCodes
  PaperP1.OrientedPlanarMotifCount

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Many (η : ℝ) (L H : ℕ) (X : Fin 3 → ℕ) : Prop :=
  ∃ G : Finset (Finset (Vertex L)),
    (↑G : Set (Finset (Vertex L))).PairwiseDisjoint id ∧
    η * (L + 1) ≤ (G.card : ℝ) ∧
    ∀ E ∈ G, Transverse E ∧ SquareOutside H X E

def RegularDirect (N L : ℕ) (X : Fin 3 → ℕ) : Prop :=
  Function.Injective X ∧
    (∀ i, X i ∈ dyadicBlock N ∧ Module.finrank F₂ (squareClassSpace (X i) L) = L) ∧
    Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L))

def mass (L : ℕ) (S : Finset (Fin 3 → ℕ)) : ℝ :=
  ∑ X ∈ S, infiniteJointMoment L (TripleProbabilityBound.tupleSet X)

def primitiveMass (L : ℕ) (S : Finset (Fin 3 → ℕ)) : ℝ :=
  mass L (S.filter (TripleProbabilityBound.Primitive L))

theorem primitive_mass_le (L : ℕ) (S : Finset (Fin 3 → ℕ)) :
    primitiveMass L S ≤ mass L S := by
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun X _ _ ↦ by
    exact infiniteJointMoment_nonneg L (TripleProbabilityBound.tupleSet X))

theorem mass_le {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    (S : Finset (Fin 3 → ℕ)) (hS : ∀ X ∈ S, RegularDirect N L X) :
    mass L S ≤ (S.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  calc
    _ ≤ ∑ _X ∈ S, ((2 ^ L : ℝ)⁻¹) ^ 2 := by
      apply sum_le_sum
      intro X hX
      have hr := hS X hX
      have h0 : 0 < X 0 := lt_of_lt_of_le hN (mem_Ico.mp (hr.2.1 0).1).1
      have h1 : 0 < X 1 := lt_of_lt_of_le hN (mem_Ico.mp (hr.2.1 1).1).1
      exact TripleProbabilityBound.triple_joint_le X h0 h1 hL
        ⟨fun hh ↦ (by decide : (0 : Fin 3) ≠ 1) (hr.1 hh),
          (hr.2.1 0).2, (hr.2.1 1).2, hr.2.2 (by decide)⟩
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem uniform_natural (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (D k : ℕ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ F : Finset Plane, F.card ≤ (L + 1) ^ k →
      (∀ p ∈ F, p.1 ≠ 0 ∧ (∀ j, (p.1 j).natAbs ≤ (L + 1) ^ k) ∧ p.2.natAbs ≤ (L + 1) ^ k) →
      ∀ S : Finset (Fin 3 → ℕ), (∀ X ∈ S, RegularDirect N L X) →
      (∀ X ∈ S, (∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2) ∧ Many η L H X) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧ mass L S ≤ (N : ℝ) ^ (-1 + ε) ∧
        primitiveMass L S ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨d, hd⟩ := exists_nat_gt (6 / η)
  have hdegree : 6 ≤ η * ((d : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hη).mp hd
    nlinarith only [hh, hη]
  obtain ⟨Bmin, hBmin⟩ := exists_nat_ge (6 / η)
  have hwidth : 6 ≤ η * (Bmin : ℝ) := by
    have hh := (div_le_iff₀ hη).mp hBmin
    linarith
  obtain ⟨NC, _hNC, hc⟩ := GeneralPlanarMotifCount.uniform_count C D d k (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C Bmin
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NC (max NG NA)), by omega, ?_⟩
  intro N hN L H hband hcut F hFcard hF S hS hcover
  obtain ⟨_hN2, hBminL, hBtwo, _hthin, _hBlo, _hBhi⟩ := hg N (by omega) L hband
  have hηB : 6 ≤ η * (L + 1) :=
    hwidth.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hBminL) hη.le)
  have hcount : (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 2) := by
    apply hc N (by omega) L H hband hcut F hFcard hF S
    · intro X hX
      have hr := hS X hX
      exact ⟨fun j ↦ (hr.2.1 j).1,
        fun j ↦ TwoPointSquareClasses.injective_evenMap_of_rank (X j) L (hr.2.1 j).2, hr.2.2⟩
    · intro X hX
      obtain ⟨⟨p, hp, hplane⟩, G, hdisj, hpop, hG⟩ := hcover X hX
      obtain ⟨E, hEd, hE⟩ := TransverseMotifSelection.select_three G hdisj η hη d hdegree hpop hηB
      exact ⟨p, hp, hplane, E, ⟨hEd, fun i ↦ (hG _ (hE i).1).1⟩,
        fun i ↦ ⟨(hE i).2, (hG _ (hE i).1).2⟩⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass : mass L S ≤ (N : ℝ) ^ (-1 + ε) := by
    calc
      _ ≤ (S.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := mass_le (by omega) (by omega) S hS
      _ ≤ (N : ℝ) ^ (1 + ε / 2) * ((((2 : ℝ) ^ C) ^ 2) * (N : ℝ) ^ (-2 : ℝ)) :=
        mul_le_mul hcount (CriticalChannelPowers.nominal_square_upper (by omega) hband)
          (sq_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = (((2 : ℝ) ^ C) ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by
        rw [← mul_assoc, mul_comm ((N : ℝ) ^ (1 + ε / 2)), mul_assoc, ← Real.rpow_add hn]
        congr 2
        ring
      _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
      _ = _ := by congr 1; ring
  refine ⟨hcount.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    (by linarith)), hmass, (primitive_mass_le L S).trans hmass⟩

/-- The real coefficient exponent and real cutoff constant in the source statement. -/
theorem companion_T20_6 (C C₀ η K ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ C₀ * (L + 1) →
      ∀ F : Finset Plane, (F.card : ℝ) ≤ (L + 1 : ℝ) ^ K →
      (∀ p ∈ F, p.1 ≠ 0 ∧ (∀ j, (↑(p.1 j).natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) ∧
        (p.2.natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) →
      ∀ S : Finset (Fin 3 → ℕ), (∀ X ∈ S, RegularDirect N L X) →
      (∀ X ∈ S, (∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2) ∧ Many η L H X) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧ mass L S ≤ (N : ℝ) ^ (-1 + ε) ∧
        primitiveMass L S ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨D, hD⟩ := exists_nat_ge C₀
  obtain ⟨k, hk⟩ := exists_nat_ge K
  obtain ⟨N₀, hN₀, hu⟩ := uniform_natural C η ε hη hε D k
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband hcut F hFcard hF S hS hcover
  have hpow : (L + 1 : ℝ) ^ K ≤ ((L + 1) ^ k : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) L; linarith : (1 : ℝ) ≤ L + 1) hk
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hh
  have hcutNat : H ≤ D * (L + 1) := by
    have hh := hcut.trans (mul_le_mul_of_nonneg_right hD (by positivity : (0 : ℝ) ≤ L + 1))
    exact_mod_cast hh
  apply hu N hN L H hband hcutNat F (by exact_mod_cast hFcard.trans hpow) ?_ S hS hcover
  intro p hp
  exact ⟨(hF p hp).1, fun j ↦ by exact_mod_cast ((hF p hp).2.1 j).trans hpow,
    by exact_mod_cast (hF p hp).2.2.trans hpow⟩

def ManyReal (η : ℝ) (L : ℕ) (H : ℝ) (X : Fin 3 → ℕ) : Prop :=
  ∃ G : Finset (Finset (Vertex L)),
    (↑G : Set (Finset (Vertex L))).PairwiseDisjoint id ∧
    η * (L + 1) ≤ (G.card : ℝ) ∧
    ∀ E ∈ G, Transverse E ∧ ∀ p ∈ code X E, (p : ℝ) ≤ H

theorem many_real_iff (η : ℝ) (L : ℕ) (H : ℝ) (hH : 0 ≤ H) (X : Fin 3 → ℕ) :
    ManyReal η L H X ↔ Many η L ⌊H⌋₊ X := by
  simp only [ManyReal, Many, SquareOutside, Nat.le_floor_iff hH]

/-- The literal population of hosts at the real cutoff H=C₀B. -/
def hosts (N L : ℕ) (C₀ η : ℝ) (F : Finset Plane) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 3 ↦ dyadicBlock N).filter fun X ↦
    RegularDirect N L X ∧ (∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2) ∧
      ManyReal η L (C₀ * (L + 1)) X

theorem hosts_data {N L : ℕ} {C₀ η : ℝ} {F : Finset Plane} {X : Fin 3 → ℕ}
    (hX : X ∈ hosts N L C₀ η F) :
    RegularDirect N L X ∧ (∃ p ∈ F, dot p.1 (fun j ↦ (X j : ℤ)) = p.2) ∧
      ManyReal η L (C₀ * (L + 1)) X := (mem_filter.mp hX).2

theorem source_population (C C₀ η K ε : ℝ) (hC₀ : 0 ≤ C₀) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset Plane, (F.card : ℝ) ≤ (L + 1 : ℝ) ^ K →
      (∀ p ∈ F, p.1 ≠ 0 ∧ (∀ j, (↑(p.1 j).natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) ∧
        (p.2.natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) →
      ((hosts N L C₀ η F).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧
        mass L (hosts N L C₀ η F) ≤ (N : ℝ) ^ (-1 + ε) ∧
        primitiveMass L (hosts N L C₀ η F) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := companion_T20_6 C C₀ η K ε hη hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hFcard hF
  have hcut : 0 ≤ C₀ * (L + 1) := mul_nonneg hC₀ (by positivity)
  exact hu N hN L ⌊C₀ * (L + 1)⌋₊ hband (Nat.floor_le hcut) F hFcard hF
    (hosts N L C₀ η F) (fun _ hX ↦ (hosts_data hX).1)
    (fun X hX ↦ ⟨(hosts_data hX).2.1, (many_real_iff η L _ hcut X).mp (hosts_data hX).2.2⟩)

end PaperP1.ManyPlanarSquareProducts
