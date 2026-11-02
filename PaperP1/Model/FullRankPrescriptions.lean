module

public import PaperP1.Model.ContactFamilySeeds
public import PaperP1.Model.RegularStarts

/-! # Every prescribed tuple atom is uniform at full effective rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FullRankPrescriptions

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem joint_of_full_rank {s L : ℕ} (x : Fin s → ℕ) (c : ℕ → Fin L → F₂)
    (hfull : Module.finrank F₂ (⨆ i, squareClassSpace (x i) L : Submodule F₂ (ℕ →₀ F₂)) = s * L) :
    PrescribedTupleMass.joint L c x = (2 ^ (s * L) : ℝ)⁻¹ := by
  let M := (univ.sup x) + L
  have hcut : ∀ i, x i + L ≤ M := fun i ↦ Nat.add_le_add_right (le_sup (f := x) (mem_univ i)) L
  have hmass := CompatibleWindowPrescriptions.source_mass_affine x (fun i ↦ c (x i)) hcut
  change PrescribedTupleMass.joint L c x = _ at hmass
  rw [hmass]
  have hrank : Module.finrank F₂ (effectiveRowSpace (familyStartSystem M L x)) =
      Fintype.card (Fin s × Fin L) := by
    rw [effectiveRowSpace_familyStartSystem, ← PrescribedTupleRank.total_rank_eq_rows x hcut, hfull,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    uniformSolutionMass_of_full_effective_rank (familyStartSystem M L x) hrank (fun p ↦ c (x p.1) p.2)

theorem contact_on_regular_union {N L x : ℕ} (hx : 0 < x)
    (hreg : x ∈ RegularStarts.regularStarts N (2 * L)) (c : ℕ → Fin L → F₂) :
    PrescribedTupleMass.joint L c (ContactPairMass.pair x (x + L)) = (2 ^ (2 * L) : ℝ)⁻¹ := by
  apply joint_of_full_rank
  rw [ContactPairMass.pair_span, ContactWindowSpan.joined_space hx]
  exact (RegularStarts.mem_regularStarts.mp hreg).2

theorem actual_contact_on_regular_union {N L x : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hreg : x ∈ RegularStarts.regularStarts N (2 * L)) :
    infiniteJointMoment L {x, x + L} = (2 ^ (2 * L) : ℝ)⁻¹ := by
  rw [← ContactFamilySeeds.prescribed_contact L hL x]
  exact contact_on_regular_union hx hreg (fun _ ↦ startRhs L)

end PaperP1.FullRankPrescriptions
