module

public import PaperP1.Arithmetic.ExactContactSeeds
public import PaperP1.Model.SingletonSeedMass
public import PaperP1.Model.PrescribedTuplePositions
public import Mathlib.Tactic.FinCases

/-! # Literal defective and contacting ordered tuples are covered by actual positioned seeds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BadSeedFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.RegularStarts PaperP1.Model
  PaperP1.PrescribedTupleMass

local instance badSeedFamiliesDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def population (N r : ℕ) : Finset (Fin r → ℕ) := Fintype.piFinset fun _ ↦ Ico N (2 * N)

def defectFamilies (N L r : ℕ) := (population N r).filter fun x ↦
  Function.Injective x ∧ ∃ i, x i ∈ irregularStarts N L

def contactFamilies (N L r : ℕ) := (population N r).filter fun x ↦
  Function.Injective x ∧ ∃ i j, i ≠ j ∧ Nat.dist (x i) (x j) ≤ L

def activeContacts (N L r : ℕ) := (contactFamilies N L r).filter fun x ↦
  0 < joint L (fun _ ↦ startRhs L) x

theorem mem_defectFamilies (N L r : ℕ) (x : Fin r → ℕ) :
    x ∈ defectFamilies N L r ↔ (∀ i, x i ∈ Ico N (2 * N)) ∧ Function.Injective x ∧
      ∃ i, x i ∈ irregularStarts N L := by
  simp only [defectFamilies, mem_filter, population, Fintype.mem_piFinset]

theorem mem_contactFamilies (N L r : ℕ) (x : Fin r → ℕ) :
    x ∈ contactFamilies N L r ↔ (∀ i, x i ∈ Ico N (2 * N)) ∧ Function.Injective x ∧
      ∃ i j, i ≠ j ∧ Nat.dist (x i) (x j) ≤ L := by
  simp only [contactFamilies, mem_filter, population, Fintype.mem_piFinset]

theorem defect_cover (N L k : ℕ) :
    defectFamilies N L (1 + k) ⊆ TuplePositions.allPositions (Ico N (2 * N))
      (SingletonSeedMass.seeds (irregularStarts N L)) k := by
  intro x hx
  obtain ⟨hcoords, hinj, i, hi⟩ := (mem_defectFamilies N L (1 + k) x).mp hx
  let f : Fin 1 → Fin (1 + k) := fun _ ↦ i
  apply TuplePositions.of_injected_seed _ _
    (SingletonSeedMass.seeds_coordinates _ _ (fun _ hy ↦ (mem_irregularStarts.mp hy).1))
    x hcoords hinj f (fun _ _ _ ↦ Subsingleton.elim _ _)
  exact mem_image.mpr ⟨x i, hi, rfl⟩

theorem ordered_contact_cover {N L k : ℕ} (x : Fin (2 + k) → ℕ) (hL : 0 < L)
    (hcoords : ∀ i, x i ∈ Ico N (2 * N)) (hinj : Function.Injective x)
    (hpos : 0 < joint L (fun _ ↦ startRhs L) x)
    (i j : Fin (2 + k)) (hij : x i < x j) (hclose : Nat.dist (x i) (x j) ≤ L) :
    x ∈ TuplePositions.allPositions (Ico N (2 * N)) (ExactContactSeeds.seeds N L) k := by
  have hsep := PrescribedTuplePositions.positive_run_separation x hL hpos i j hij
  rw [Nat.dist_eq_sub_of_le hij.le] at hclose
  have hend : x j = x i + L := by omega
  have hijindex : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
  let f : Fin 2 → Fin (2 + k) := ![i, j]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  apply TuplePositions.of_injected_seed _ _ (ExactContactSeeds.seed_coordinates N L) x hcoords hinj f hf
  exact (ExactContactSeeds.mem_seeds N L _).mpr ⟨hcoords i, hcoords j, hend⟩

theorem contact_cover (N L k : ℕ) (hL : 0 < L) :
    activeContacts N L (2 + k) ⊆
      TuplePositions.allPositions (Ico N (2 * N)) (ExactContactSeeds.seeds N L) k := by
  intro x hx
  obtain ⟨hx, hpos⟩ := mem_filter.mp hx
  obtain ⟨hcoords, hinj, i, j, hij, hclose⟩ := (mem_contactFamilies N L (2 + k) x).mp hx
  rcases lt_or_gt_of_ne (hinj.ne hij) with hlt | hgt
  · exact ordered_contact_cover x hL hcoords hinj hpos i j hlt hclose
  · exact ordered_contact_cover x hL hcoords hinj hpos j i hgt (by rwa [Nat.dist_comm])

theorem contact_mass_eq_active (N L r : ℕ) :
    (∑ x ∈ contactFamilies N L r, joint L (fun _ ↦ startRhs L) x) =
      ∑ x ∈ activeContacts N L r, joint L (fun _ ↦ startRhs L) x := by
  symm
  apply sum_subset (filter_subset _ _)
  intro x hx hxnot
  have hnonneg := joint_nonneg (fun _ ↦ startRhs L) x
  have hnotpos : ¬0 < joint L (fun _ ↦ startRhs L) x := fun h ↦ hxnot (mem_filter.mpr ⟨hx, h⟩)
  linarith

end PaperP1.BadSeedFamilies
