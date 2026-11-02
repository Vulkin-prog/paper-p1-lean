module

public import PaperP1.Asymptotics.InteriorAlignedTripleMass
public import PaperP1.Asymptotics.EndpointAlignedTripleMass

/-! # Every polynomial-height affine aligned target of an exact source channel has sharp total mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllAlignedTargetTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

structure Representation (N L a b J : ℕ) (T : Finset ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  t : ℕ
  c : ℕ
  d : ℕ
  i : Fin (L + 1)
  j : Fin (L + 1)
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
  source_y : startCompleteVertexLabel y L j = b * t
  target : (d : ℤ) * z = (c : ℤ) * t + offset

def hosts (N L a b J : ℕ) : Finset (Finset ℕ) :=
  InteriorAlignedTripleMass.hosts N L a b J ∪ EndpointAlignedTripleMass.hosts N L a b J

def mass (N L a b J : ℕ) : ℝ := ∑ T ∈ hosts N L a b J, infiniteJointMoment L T

theorem source_mem_hosts {N L a b J : ℕ} {T : Finset ℕ} (r : Representation N L a b J T)
    (hcard : T.card = 3) (hN : 2 ≤ N) (ha : 0 < a)
    (hsize : a * (2 * (L + 1) ^ J * ((L + 1) + 1)) + (L + 1) < N) : T ∈ hosts N L a b J := by
  classical
  by_cases hnear : EndpointAlignedTriplePool.Near N a b (EndpointAlignedTriplePool.radius L J) r.t
  · let re : EndpointAlignedTripleMass.Representation N L a b J T :=
      ⟨r.x, r.y, r.z, r.t, r.c, r.d, r.i, r.j, r.offset, r.family_eq, r.x_dyadic, r.y_dyadic, r.z_dyadic,
        r.numerator_pos, r.denominator_pos, r.coprime, r.denominator_height, r.offset_height,
        r.source_x, r.source_y, r.target, hnear⟩
    exact mem_union_right _ (EndpointAlignedTripleMass.source_mem_hosts re hcard hN ha hsize)
  · dsimp only [EndpointAlignedTriplePool.Near] at hnear
    have hawayA : ((L + 1 : ℕ) : ℤ) + 2 * ((L + 1) ^ J : ℕ) < |(a : ℤ) * r.t - N| := by
      have hh := lt_of_not_ge (not_or.mp hnear).1
      simpa only [EndpointAlignedTriplePool.radius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hh
    have hawayB : ((L + 1 : ℕ) : ℤ) + 2 * ((L + 1) ^ J : ℕ) < |(b : ℤ) * r.t - 2 * N| := by
      have hh := lt_of_not_ge (not_or.mp hnear).2
      simpa only [EndpointAlignedTriplePool.radius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hh
    have hsrcA := (ActualDyadicInterior.source_parameter_bounds (by omega : 0 < N) r.x_dyadic r.i r.source_x).1
    have hsrcB := (ActualDyadicInterior.source_parameter_bounds (by omega : 0 < N) r.y_dyadic r.j r.source_y).2
    have ht := ActualDyadicInterior.parameter_large (by omega : 0 < N) r.x_dyadic r.i r.source_x hsize
    have hratio := DyadicTargetInterior.strict_interior_of_no_endpoints r.denominator_pos hsrcA hsrcB
      (mem_Ico.mp r.z_dyadic).1 (mem_Ico.mp r.z_dyadic).2.le r.denominator_height r.offset_height r.target ht hawayA hawayB
    have hTop : r.c < 2 * (a * r.d) := by simpa only [Nat.mul_assoc] using hratio.2
    let ri : InteriorAlignedTripleMass.Representation N L a b J T :=
      ⟨r.x, r.y, r.z, r.t, r.c, r.d, r.i, r.j, r.offset, r.family_eq, r.x_dyadic, r.y_dyadic, r.z_dyadic,
        r.numerator_pos, r.denominator_pos, r.coprime, r.denominator_height, r.offset_height,
        r.source_x, r.source_y, r.target, hTop, hratio.1⟩
    exact mem_union_left _ (InteriorAlignedTripleMass.source_mem_hosts ri hcard hN ha hsize)

theorem all_actual_sources (a b J : ℕ) (ha : 0 < a) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ T : Finset ℕ, T.card = 3 → Representation N L a b J T → T ∈ hosts N L a b J := by
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.source_size_eventually C a J
  refine ⟨max 10 NS, by omega, ?_⟩
  intro N hN L hband T hcard r
  exact source_mem_hosts r hcard (by omega) ha (hs N (by omega) L ((L + 1) ^ J) hband le_rfl)

theorem mass_le_sum (N L a b J : ℕ) : mass N L a b J ≤
    InteriorAlignedTripleMass.mass N L a b J + EndpointAlignedTripleMass.mass N L a b J := by
  have hh := sum_union_inter (s₁ := InteriorAlignedTripleMass.hosts N L a b J) (s₂ := EndpointAlignedTripleMass.hosts N L a b J)
    (f := fun T ↦ infiniteJointMoment L T)
  have hi : 0 ≤ ∑ T ∈ InteriorAlignedTripleMass.hosts N L a b J ∩ EndpointAlignedTripleMass.hosts N L a b J,
      infiniteJointMoment L T := sum_nonneg (fun T _ ↦ infiniteJointMoment_nonneg L T)
  change mass N L a b J + (∑ T ∈ InteriorAlignedTripleMass.hosts N L a b J ∩ EndpointAlignedTripleMass.hosts N L a b J,
    infiniteJointMoment L T) = InteriorAlignedTripleMass.mass N L a b J + EndpointAlignedTripleMass.mass N L a b J at hh
  linarith only [hh, hi]

theorem uniform_mass {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L a b J ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  have hb : 3 ≤ b := by omega
  obtain ⟨NA, _hNA, haM⟩ := InteriorAlignedTripleMass.uniform_mass ha hab hb2a hcop J C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hbM⟩ := EndpointAlignedTripleMass.uniform_mass ha hb hab hcop J C (ε / 2) (by positivity)
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NA (max NB NP)), by omega, ?_⟩
  intro N hN L hband
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (-5 / 3 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-5 / 3 : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2)
  have hleft := haM N (by omega) L hband
  have hright := (hbM N (by omega) L hband).trans hpower
  have hsum : mass N L a b J ≤ 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    have hh := mass_le_sum N L a b J
    linarith only [hh, hleft, hright]
  exact hsum.trans (by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = (-41 / 30 : ℝ) + ε by ring] using hp N (by omega))

end PaperP1.AllAlignedTargetTripleMass
