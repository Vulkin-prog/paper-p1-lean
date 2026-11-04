module

public import PaperP1.Arithmetic.ScaledSourceTargetData
public import PaperP1.Arithmetic.ExactMatchCongruences
public import PaperP1.Asymptotics.HomogeneousEnlargedTripleMass
public import PaperP1.Asymptotics.HomogeneousSeedPropagation

/-! # Homogeneous mass of an actual pair and a target aligned at scaled starts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledAlignedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Witness (F : Finset (ℕ × ℕ)) (Q D L : ℕ) (T : Finset ℕ) : Prop :=
  ∃ ab ∈ F, ∃ x y z d : ℕ, T = {x, y, z} ∧
    (NormalizedUnitCount.units ab.1 ab.2 x y L).Nonempty ∧ 0 < d ∧ d ≤ Q ∧
    CompressedTargetAlignment.Aligned D (ab.2 * x) (d * z) L

def hosts (F : Finset (ℕ × ℕ)) (Q D N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 3).filter (Witness F Q D L)

theorem uniform_inclusion (F : Finset (ℕ × ℕ)) (Q D : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1.Coprime ab.2 ∧ ab.2 ≤ Q) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      hosts F Q D N L ⊆ EnlargedFiniteAlignedTargetTripleMass.hosts F (fun _ ↦ 5) N L := by
  obtain ⟨NR, _hNR, hu⟩ := EnlargedFiniteAlignedTargetTripleMass.all_actual_sources F (fun _ ↦ 5)
    (fun ab hab ↦ (hF ab hab).1) C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (2 * (D + Q) + Q)
  refine ⟨max 10 (max NR NG), by omega, ?_⟩
  intro N hN L hcrit T hT
  obtain ⟨hpow, ab, hab, x, y, z, d, hfamily, hunit, hd, hdQ, halign⟩ := mem_filter.mp hT
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hpow
  have hx : x ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hy : y ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hz : z ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  obtain ⟨ha, hb, hcop, hbQ⟩ := hF ab hab
  obtain ⟨ij, hij⟩ := hunit
  obtain ⟨t, _ht, hbaseX, _hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop
    (by have := (mem_Ico.mp hx).1; omega : 2 ≤ x) ij.1 ij.2 (NormalizedUnitCount.mem_units.mp hij)
  obtain ⟨r, s, hr, hs, _hcoprs, hrB, hsB, hgeom⟩ := halign
  have hB := (hg N (by omega) L hcrit).2.1
  have hpowB : L + 1 ≤ (L + 1) ^ 2 := le_self_pow (by omega) (by decide : 2 ≠ 0)
  obtain ⟨c, e, h, hc, he, hce, heH, hh, heq⟩ := ScaledSourceTargetData.bounded ha hb hd
    (by have := (mem_Ico.mp hx).1; omega : 0 < x) ij.1 hbaseX hr hs hrB hsB
    (by omega) ((show d ≤ L + 1 by omega).trans hpowB) hgeom
  have hsource : EnlargedPairGeometry.Geometric ab.1 ab.2 x y L := by
    have hh := FixedChannelLinearCount.unit_alignment (a := ab.1) (b := ab.2) (L := L) (by omega : 0 < N)
      (xy := (x, y)) (mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, ⟨ij, hij⟩⟩)
    simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using hh
  let rep : EnlargedAllAlignedTargetTripleMass.Representation N L ab.1 ab.2 5 T :=
    ⟨x, y, z, t, c, e, ij.1, h, hfamily, hx, hy, hz, hc, he, hce, heH, hh, hbaseX, hsource, heq⟩
  exact hu N (by omega) L hcrit T hcard ⟨ab, hab, ⟨rep⟩⟩

theorem uniform_mass (F : Finset (ℕ × ℕ)) (Q D : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 ∧ ab.2 ≤ Q)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SeparatedHomogeneousMass.mass L (hosts F Q D N L) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := uniform_inclusion F Q D (fun ab hab ↦
    ⟨(hF ab hab).1, (hF ab hab).1.trans (hF ab hab).2.1, (hF ab hab).2.2.2.1, (hF ab hab).2.2.2.2⟩) C
  obtain ⟨NM, _hNM, hm⟩ := HomogeneousEnlargedTripleMass.finite_uniform_mass F (fun _ ↦ 5)
    (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1, (hF ab hab).2.2.1, (hF ab hab).2.2.2.1⟩) C ε hε
  refine ⟨max 10 (max NI NM), by omega, ?_⟩
  intro N hN L hcrit
  exact (SeparatedHomogeneousMass.mono L (hi N (by omega) L hcrit)).trans (hm N (by omega) L hcrit)

def extensions (F : Finset (ℕ × ℕ)) (Q D k N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard (3 + k)).filter fun I ↦
    SeparatedHomogeneousMass.Separated L I ∧ ∃ T ∈ hosts F Q D N L, T ⊆ I

theorem uniform_extensions (F : Finset (ℕ × ℕ)) (Q D k : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 ∧ ab.2 ≤ Q)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ I ∈ extensions F Q D k N L, HomogeneousRunMass.probability L I) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NP, hp⟩ := HomogeneousSeedPropagation.uniform_probability_mass 3 (by norm_num) k C (ε / 3) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := uniform_mass F Q D hF C (ε / 3) (by positivity)
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption ((3 + k).factorial : ℝ)
    (-41 / 30 + 2 * ε / 3) (ε / 3) (by positivity)
  refine ⟨max 10 (max NP (max NT NC)), by omega, ?_⟩
  intro N hN L hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let S := (hosts F Q D N L).filter (SeparatedHomogeneousMass.Separated L)
  have hS : ∀ T ∈ S, T ⊆ dyadicBlock N ∧ T.card = 3 := by
    intro T hT
    exact mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hT).1).1
  have hT : ∀ I ∈ extensions F Q D k N L,
      I ⊆ dyadicBlock N ∧ I.card = 3 + k ∧ ∃ T ∈ S, T ⊆ I := by
    intro I hI
    obtain ⟨hpow, hsep, T, hThost, hTI⟩ := mem_filter.mp hI
    refine ⟨(mem_powersetCard.mp hpow).1, (mem_powersetCard.mp hpow).2, T, ?_, hTI⟩
    exact mem_filter.mpr ⟨hThost, fun x hx y hy hxy ↦ hsep x (hTI hx) y (hTI hy) hxy⟩
  have hprop := hp N (by omega) L hcrit S hS (extensions F Q D k N L) hT
  calc
    _ ≤ ((3 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 3) * ∑ T ∈ S, HomogeneousRunMass.probability L T := hprop
    _ ≤ ((3 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (-41 / 30 + ε / 3) :=
      mul_le_mul_of_nonneg_left (ht N (by omega) L hcrit) (by positivity)
    _ = ((3 + k).factorial : ℝ) * (N : ℝ) ^ (-41 / 30 + 2 * ε / 3) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ (N : ℝ) ^ ((-41 / 30 + 2 * ε / 3) + ε / 3) := hc N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.ScaledAlignedTripleMass
