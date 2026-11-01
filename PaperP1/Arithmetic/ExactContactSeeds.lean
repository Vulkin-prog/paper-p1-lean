module

public import PaperP1.Asymptotics.ContactSeedMass

/-! # Literal finite two-coordinate exact-contact seed families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactContactSeeds

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass PaperP1.ContactPairMass

def starts (N L : ℕ) : Finset ℕ := (Ico N (2 * N)).filter fun x ↦ x + L ∈ Ico N (2 * N)

def seeds (N L : ℕ) : Finset (Fin 2 → ℕ) := (starts N L).image fun x ↦ pair x (x + L)

theorem mem_seeds (N L : ℕ) (x : Fin 2 → ℕ) :
    x ∈ seeds N L ↔ x 0 ∈ Ico N (2 * N) ∧ x 1 ∈ Ico N (2 * N) ∧ x 1 = x 0 + L := by
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    obtain ⟨hz, hzt⟩ := mem_filter.mp hz
    exact ⟨hz, hzt, rfl⟩
  · rintro ⟨hzero, hone, heq⟩
    apply mem_image.mpr
    refine ⟨x 0, mem_filter.mpr ⟨hzero, heq ▸ hone⟩, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact heq.symm

theorem seed_coordinates (N L : ℕ) : ∀ x ∈ seeds N L, ∀ i, x i ∈ Ico N (2 * N) := by
  intro x hx
  obtain ⟨hzero, hone, _⟩ := (mem_seeds N L x).mp hx
  exact Fin.forall_fin_two.mpr ⟨hzero, hone⟩

theorem seed_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
        (∑ x ∈ seeds N L, joint L c x) ≤ ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀⟩ := ContactSeedMass.forward_sum C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband c
  calc
    _ ≤ ∑ x ∈ starts N L, joint L c (pair x (x + L)) :=
      sum_image_le_of_nonneg (fun x _ ↦ joint_nonneg c x)
    _ ≤ ∑ x ∈ Ico N (2 * N), joint L c (pair x (x + L)) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x _ _ ↦ joint_nonneg c _)
    _ ≤ _ := hN₀ N hN L hband c

end PaperP1.ExactContactSeeds
