module

public import PaperP1.Asymptotics.HomogeneousAlignedTargetTripleProbability
public import PaperP1.Asymptotics.HomogeneousPhysicalTargetTripleProbability
public import PaperP1.Asymptotics.HomogeneousEnlargedPairProbability
public import PaperP1.Asymptotics.EnlargedFiniteAlignedTargetTripleMass
public import PaperP1.Asymptotics.CompressedAlignedTripleMass
public import PaperP1.Model.SeparatedHomogeneousMass

/-! # Homogeneous aligned-target masses, retaining incompatible separated configurations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousEnlargedTripleMass

open Finset Filter PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.HomogeneousRunMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem distinct_uniform_mass {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (∑ T ∈ EnlargedAlignedTargetTripleMass.hosts N L a b J, probability L T) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := EnlargedAlignedTargetTripleMass.uniform_count a b J C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := HomogeneousAlignedTargetTripleProbability.uniform_point_bound ha hab hb2a hcop J C (ε / 2) (by positivity)
  refine ⟨max 10 (max NC NP), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (T : Finset ℕ) (hT : T ∈ EnlargedAlignedTargetTripleMass.hosts N L a b J) :
      probability L T ≤ (N : ℝ) ^ (-71 / 30 + ε / 2) := by
    obtain ⟨_hcard, ⟨r⟩⟩ := EnlargedAlignedTargetTripleMass.host_data hT
    rw [r.family_eq]
    exact hp N (by omega) L r.c r.d r.x r.y r.z r.t hband r.numerator_pos r.denominator_pos r.coprime
      r.denominator_height r.x_dyadic r.y_dyadic r.z_dyadic r.upper_interior r.lower_interior r.distinct_a r.distinct_b
      r.source_geometry r.i r.source_x r.offset r.offset_height r.target
  calc
    _ ≤ ∑ _T ∈ EnlargedAlignedTargetTripleMass.hosts N L a b J, (N : ℝ) ^ (-71 / 30 + ε / 2) := sum_le_sum hpoint
    _ = ((EnlargedAlignedTargetTripleMass.hosts N L a b J).card : ℝ) * (N : ℝ) ^ (-71 / 30 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + ε / 2) * (N : ℝ) ^ (-71 / 30 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem physical_uniform_mass {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → SeparatedHomogeneousMass.mass L (EnlargedPhysicalTargetTripleMass.hosts N L a b J) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := EnlargedPhysicalTargetTripleMass.uniform_count a b J C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := HomogeneousPhysicalTargetTripleProbability.uniform_point_bound ha hab hb2a hcop J C (ε / 2) (by positivity)
  refine ⟨max 10 (max NC NP), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (T : Finset ℕ) (hT : T ∈ (EnlargedPhysicalTargetTripleMass.hosts N L a b J).filter (SeparatedHomogeneousMass.Separated L)) :
      probability L T ≤ (N : ℝ) ^ (-5 / 2 + ε / 2) := by
    obtain ⟨hhost, hsep⟩ := mem_filter.mp hT
    obtain ⟨hcard, ⟨r⟩⟩ := EnlargedPhysicalTargetTripleMass.host_data hhost
    have hcardR : ({r.x, r.y, r.z} : Finset ℕ).card = 3 := by simpa only [r.family_eq] using hcard
    have hdistinct := RepeatedCoefficientUnionRank.triple_distinct hcardR
    have hxT : r.x ∈ T := (le_of_eq r.family_eq.symm) (by simp)
    have hyT : r.y ∈ T := (le_of_eq r.family_eq.symm) (by simp)
    have hzT : r.z ∈ T := (le_of_eq r.family_eq.symm) (by simp)
    have hsepX := hsep r.x hxT r.z hzT hdistinct.1
    have hsepY := hsep r.y hyT r.z hzT hdistinct.2
    rw [r.family_eq]
    exact hp N (by omega) L r.c r.d r.x r.y r.z r.t hband r.numerator_pos r.denominator_pos r.coprime
      r.denominator_height r.x_dyadic r.y_dyadic r.z_dyadic hsepX hsepY r.physical
      r.source_geometry r.i r.source_x r.offset r.offset_height r.target
  calc
    _ ≤ ∑ _T ∈ (EnlargedPhysicalTargetTripleMass.hosts N L a b J).filter (SeparatedHomogeneousMass.Separated L), (N : ℝ) ^ (-5 / 2 + ε / 2) := sum_le_sum hpoint
    _ = (((EnlargedPhysicalTargetTripleMass.hosts N L a b J).filter (SeparatedHomogeneousMass.Separated L)).card : ℝ) * (N : ℝ) ^ (-5 / 2 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + ε / 2) * (N : ℝ) ^ (-5 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right ((show (((EnlargedPhysicalTargetTripleMass.hosts N L a b J).filter (SeparatedHomogeneousMass.Separated L)).card : ℝ) ≤ (EnlargedPhysicalTargetTripleMass.hosts N L a b J).card by exact_mod_cast card_le_card (filter_subset _ _)).trans (hc N (by omega) L hband)) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem endpoint_uniform_mass {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b) (hab : a < b)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (∑ T ∈ EnlargedEndpointAlignedTripleMass.hosts N L a b J, probability L T) ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := EnlargedEndpointAlignedTripleMass.uniform_count ha (by omega : 0 < b) J C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := HomogeneousEnlargedPairProbability.uniform_coarse ha hb hab hcop C (ε / 2) (by positivity)
  refine ⟨max 10 (max NC NP), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (T : Finset ℕ) (hT : T ∈ EnlargedEndpointAlignedTripleMass.hosts N L a b J) :
      probability L T ≤ (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    obtain ⟨_hcard, ⟨r⟩⟩ := EnlargedEndpointAlignedTripleMass.host_data hT
    have hsub₀ : ({r.x, r.y} : Finset ℕ) ⊆ {r.x, r.y, r.z} := by
      intro n hn
      simp only [mem_insert, mem_singleton] at hn ⊢
      tauto
    have hsub : ({r.x, r.y} : Finset ℕ) ⊆ T := hsub₀.trans (le_of_eq r.family_eq.symm)
    exact (probability_antitone L hsub).trans
      (hp N (by omega) L r.x r.y hband r.x_dyadic r.y_dyadic r.source_geometry)
  calc
    _ ≤ ∑ _T ∈ EnlargedEndpointAlignedTripleMass.hosts N L a b J, (N : ℝ) ^ (-5 / 3 + ε / 2) := sum_le_sum hpoint
    _ = ((EnlargedEndpointAlignedTripleMass.hosts N L a b J).card : ℝ) * (N : ℝ) ^ (-5 / 3 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-5 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem all_uniform_mass {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SeparatedHomogeneousMass.mass L (EnlargedAllAlignedTargetTripleMass.hosts N L a b J) ≤
        (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NA, _hNA, haM⟩ := distinct_uniform_mass ha hab hb2a hcop J C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hbM⟩ := physical_uniform_mass ha hab hb2a hcop J C (ε / 2) (by positivity)
  obtain ⟨NE, _hNE, heM⟩ := endpoint_uniform_mass ha (by omega) hab hcop J C (ε / 2) (by positivity)
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption 3 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NA (max NB (max NE NP))), by omega, ?_⟩
  intro N hN L hband
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA := (SeparatedHomogeneousMass.le_total L (EnlargedAlignedTargetTripleMass.hosts N L a b J)).trans
    (haM N (by omega) L hband)
  have hB := (hbM N (by omega) L hband).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-3 / 2 : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2))
  have hE := (SeparatedHomogeneousMass.le_total L (EnlargedEndpointAlignedTripleMass.hosts N L a b J)).trans
    ((heM N (by omega) L hband).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-5 / 3 : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2)))
  have hInterior := SeparatedHomogeneousMass.union_le L
    (EnlargedAlignedTargetTripleMass.hosts N L a b J) (EnlargedPhysicalTargetTripleMass.hosts N L a b J)
  have hAll := SeparatedHomogeneousMass.union_le L
    (EnlargedInteriorAlignedTripleMass.hosts N L a b J) (EnlargedEndpointAlignedTripleMass.hosts N L a b J)
  change SeparatedHomogeneousMass.mass L (EnlargedInteriorAlignedTripleMass.hosts N L a b J) ≤ _ at hInterior
  change SeparatedHomogeneousMass.mass L (EnlargedAllAlignedTargetTripleMass.hosts N L a b J) ≤ _ at hAll
  have hsum : SeparatedHomogeneousMass.mass L (EnlargedAllAlignedTargetTripleMass.hosts N L a b J) ≤
      3 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by linarith only [hInterior, hAll, hA, hB, hE]
  exact hsum.trans (by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = (-41 / 30 : ℝ) + ε by ring] using hp N (by omega))

theorem finite_uniform_mass (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → SeparatedHomogeneousMass.mass L (EnlargedFiniteAlignedTargetTripleMass.hosts F J N L) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  have heach (ab : ℕ × ℕ) (hab : ab ∈ F) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SeparatedHomogeneousMass.mass L (EnlargedAllAlignedTargetTripleMass.hosts N L ab.1 ab.2 (J ab)) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    obtain ⟨ha, horder, hinterior, hcop⟩ := hF ab hab
    obtain ⟨N₀, _hN₀, hu⟩ := all_uniform_mass ha horder hinterior hcop (J ab) C (ε / 2) (by positivity)
    exact eventually_atTop.mpr ⟨N₀, fun N hN ↦ hu N hN⟩
  obtain ⟨NF, hf⟩ := eventually_atTop.mp ((Finset.eventually_all F).mpr heach)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (F.card : ℝ) (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NF NA), by omega, ?_⟩
  intro N hN L hband
  calc
    _ ≤ ∑ ab ∈ F, SeparatedHomogeneousMass.mass L (EnlargedAllAlignedTargetTripleMass.hosts N L ab.1 ab.2 (J ab)) :=
      SeparatedHomogeneousMass.biUnion_le L F
        (fun ab ↦ EnlargedAllAlignedTargetTripleMass.hosts N L ab.1 ab.2 (J ab))
    _ ≤ ∑ _ab ∈ F, (N : ℝ) ^ (-41 / 30 + ε / 2) :=
      sum_le_sum (fun ab hab ↦ hf N (by omega) ab hab L hband)
    _ = (F.card : ℝ) * (N : ℝ) ^ (-41 / 30 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem compressed_uniform_mass (F : Finset (ℕ × ℕ)) (D : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → SeparatedHomogeneousMass.mass L (CompressedAlignedTripleMass.hosts F D N L) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := CompressedAlignedTripleMass.uniform_inclusion F D (fun ab hab ↦
    ⟨(hF ab hab).1, (hF ab hab).1.trans (hF ab hab).2.1⟩) C
  obtain ⟨NM, _hNM, hm⟩ := finite_uniform_mass F (fun _ ↦ 5) hF C ε hε
  refine ⟨max 10 (max NI NM), by omega, ?_⟩
  intro N hN L hband
  exact (SeparatedHomogeneousMass.mono L (hi N (by omega) L hband)).trans (hm N (by omega) L hband)

end PaperP1.HomogeneousEnlargedTripleMass
