module

public import PaperP1.Asymptotics.EnlargedAlignedTargetTripleMass
public import PaperP1.Asymptotics.EnlargedPhysicalTargetTripleMass

/-! # Every interior aligned target, including repeated physical slopes and exact contacts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedInteriorAlignedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

structure Representation (N L a b J : ℕ) (T : Finset ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  t : ℕ
  c : ℕ
  d : ℕ
  i : Fin (L + 1)
  offset : ℤ
  family_eq : T = {x, y, z}
  x_dyadic : x ∈ dyadicBlock N
  y_dyadic : y ∈ dyadicBlock N
  z_dyadic : z ∈ dyadicBlock N
  numerator_pos : 0 < c
  denominator_pos : 0 < d
  coprime : c.Coprime d
  denominator_height : d ≤ (L + 1) ^ J
  offset_height : |offset| ≤ ((L + 1) ^ J : ℕ)
  source_x : startCompleteVertexLabel x L i = a * t
  source_geometry : EnlargedPairGeometry.Geometric a b x y L
  target : (d : ℤ) * z = (c : ℤ) * t + offset
  upper_interior : c < 2 * (a * d)
  lower_interior : b * d < 2 * c

def hosts (N L a b J : ℕ) : Finset (Finset ℕ) :=
  EnlargedAlignedTargetTripleMass.hosts N L a b J ∪ EnlargedPhysicalTargetTripleMass.hosts N L a b J

def mass (N L a b J : ℕ) : ℝ := ∑ T ∈ hosts N L a b J, infiniteJointMoment L T

theorem source_mem_hosts {N L a b J : ℕ} {T : Finset ℕ} (r : Representation N L a b J T)
    (hcard : T.card = 3) (hN : 2 ≤ N) (ha : 0 < a)
    (hsize : (a * EnlargedSourceTargetGeometry.sourceScale a b) * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) : T ∈ hosts N L a b J := by
  classical
  by_cases hphys : r.c = a * r.d ∨ r.c = b * r.d
  · let rp : EnlargedPhysicalTargetTripleMass.Representation N L a b J T :=
      ⟨r.x, r.y, r.z, r.t, r.c, r.d, r.i, r.offset, r.family_eq, r.x_dyadic, r.y_dyadic, r.z_dyadic,
        r.numerator_pos, r.denominator_pos, r.coprime, r.denominator_height, r.offset_height,
        r.source_x, r.source_geometry, r.target, hphys⟩
    exact mem_union_right _ (EnlargedPhysicalTargetTripleMass.source_mem_hosts rp hcard hN ha hsize)
  · let rd : EnlargedAlignedTargetTripleMass.Representation N L a b J T :=
      ⟨r.x, r.y, r.z, r.t, r.c, r.d, r.i, r.offset, r.family_eq, r.x_dyadic, r.y_dyadic, r.z_dyadic,
        r.numerator_pos, r.denominator_pos, r.coprime, r.denominator_height, r.offset_height,
        r.source_x, r.source_geometry, r.target, r.upper_interior, r.lower_interior,
        (fun hh ↦ hphys (Or.inl hh)), (fun hh ↦ hphys (Or.inr hh))⟩
    exact mem_union_left _ (EnlargedAlignedTargetTripleMass.source_mem_hosts rd hcard hN ha hsize)

theorem all_actual_sources (a b J : ℕ) (ha : 0 < a) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ T : Finset ℕ, T.card = 3 → Representation N L a b J T → T ∈ hosts N L a b J := by
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.source_size_eventually C (a * EnlargedSourceTargetGeometry.sourceScale a b) J
  refine ⟨max 10 NS, by omega, ?_⟩
  intro N hN L hband T hcard r
  exact source_mem_hosts r hcard (by omega) ha (hs N (by omega) L ((L + 1) ^ J) hband le_rfl)

theorem mass_le_sum (N L a b J : ℕ) : mass N L a b J ≤
    EnlargedAlignedTargetTripleMass.mass N L a b J + EnlargedPhysicalTargetTripleMass.mass N L a b J := by
  have hh := sum_union_inter (s₁ := EnlargedAlignedTargetTripleMass.hosts N L a b J) (s₂ := EnlargedPhysicalTargetTripleMass.hosts N L a b J)
    (f := fun T ↦ infiniteJointMoment L T)
  have hi : 0 ≤ ∑ T ∈ EnlargedAlignedTargetTripleMass.hosts N L a b J ∩ EnlargedPhysicalTargetTripleMass.hosts N L a b J,
      infiniteJointMoment L T := sum_nonneg (fun T _ ↦ infiniteJointMoment_nonneg L T)
  change mass N L a b J + (∑ T ∈ EnlargedAlignedTargetTripleMass.hosts N L a b J ∩ EnlargedPhysicalTargetTripleMass.hosts N L a b J,
    infiniteJointMoment L T) = EnlargedAlignedTargetTripleMass.mass N L a b J + EnlargedPhysicalTargetTripleMass.mass N L a b J at hh
  linarith only [hh, hi]

theorem uniform_mass {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L a b J ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NA, _hNA, haM⟩ := EnlargedAlignedTargetTripleMass.uniform_mass ha hab hb2a hcop J C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hbM⟩ := EnlargedPhysicalTargetTripleMass.uniform_mass ha hab hb2a hcop J C (ε / 2) (by positivity)
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NA (max NB NP)), by omega, ?_⟩
  intro N hN L hband
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-3 / 2 : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2)
  have hleft := haM N (by omega) L hband
  have hright := (hbM N (by omega) L hband).trans hpower
  have hsum : mass N L a b J ≤ 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    have hh := mass_le_sum N L a b J
    linarith only [hh, hleft, hright]
  exact hsum.trans (by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = (-41 / 30 : ℝ) + ε by ring] using hp N (by omega))

end PaperP1.EnlargedInteriorAlignedTripleMass
