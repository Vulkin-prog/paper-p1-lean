module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Tactic.Ring.Basic

/-!
# Expansion at the first excluded prefix

The finite identity in article Lemma 5.1 (`p1:stop:polynomial`). A hereditary
family contains all subsets of each of its members. The ordered boundary is
formed by excluded sets whose prefix obtained by deleting the maximum is kept.
Boundary sets need not be inclusion-minimal excluded sets.

The proof works in a commutative semiring: no probability, independence,
additive inverses, scalar algebra structure, or asymptotics is required.
-/

@[expose] public section

open scoped BigOperators

namespace PaperP1.Algebra

variable {ι R : Type*} [LinearOrder ι] [CommSemiring R]

/-- Delete the greatest element, using a definition also valid on the empty set. -/
def properPrefix (I : Finset ι) : Finset ι :=
  I.filter fun x => ∃ y ∈ I, x < y

/-- A hereditary family of finite sets. -/
def Hereditary (D : Finset ι → Prop) : Prop :=
  ∀ ⦃I J⦄, J ⊆ I → D I → D J

/-- First excluded prefixes in the prescribed order. -/
def OrderedBoundary (D : Finset ι → Prop) (I : Finset ι) : Prop :=
  ¬ D I ∧ D (properPrefix I)

/-- Elements of the ground set strictly after every element of the prefix. -/
def orderedSuffix (G I : Finset ι) : Finset ι :=
  G.filter fun y => ∀ x ∈ I, x < y

/-- Retained subsets of the finite ground set. -/
noncomputable def retainedSets (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) := by
  classical
  exact G.powerset.filter D

/-- The ordered boundary restricted to the finite ground set. -/
noncomputable def boundarySets (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) := by
  classical
  exact G.powerset.filter (OrderedBoundary D)

/-- Polynomial retained by a hereditary family. -/
noncomputable def retainedPolynomial (G : Finset ι) (D : Finset ι → Prop)
    (u : ι → R) : R := by
  classical
  exact ∑ I ∈ G.powerset, if D I then ∏ x ∈ I, u x else 0

/-- The suffix is left unexpanded at the first excluded prefix. -/
noncomputable def boundaryPolynomial (G : Finset ι) (D : Finset ι → Prop)
    (u : ι → R) : R := by
  classical
  exact ∑ I ∈ G.powerset, if OrderedBoundary D I then
    (∏ x ∈ I, u x) * ∏ y ∈ orderedSuffix G I, (1 + u y) else 0

/-- Sets whose first exclusion is caused by adding the new greatest element. -/
noncomputable def newBoundaryPolynomial (G : Finset ι) (D : Finset ι → Prop)
    (u : ι → R) (a : ι) : R := by
  classical
  exact ∑ I ∈ G.powerset, if D I ∧ ¬ D (insert a I) then
    u a * ∏ x ∈ I, u x else 0

theorem properPrefix_insert_max {I : Finset ι} {a : ι}
    (ha : ∀ x ∈ I, x < a) : properPrefix (insert a I) = I := by
  ext x
  simp only [properPrefix, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hxa | hx, y, hya | hy, hxy⟩
    · subst x
      subst y
      exact False.elim ((lt_irrefl a) hxy)
    · exact False.elim (lt_asymm (hxa ▸ hxy) (ha y hy))
    · exact hx
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, a, Or.inl rfl, ha x hx⟩

/-- The prefix definition is exactly deletion of the maximum on a nonempty set. -/
theorem properPrefix_eq_erase_max (I : Finset ι) (hI : I.Nonempty) :
    properPrefix I = I.erase (I.max' hI) := by
  ext x
  simp only [properPrefix, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    exact ⟨ne_of_lt (lt_of_lt_of_le hxy (I.le_max' y hy)), hx⟩
  · rintro ⟨hne, hx⟩
    exact ⟨hx, I.max' hI, I.max'_mem hI, lt_of_le_of_ne (I.le_max' x hx) hne⟩

/-- Boundary sets are nonempty because the empty set is retained. -/
theorem orderedBoundary_nonempty {D : Finset ι → Prop} {I : Finset ι}
    (h_empty : D ∅) (hI : OrderedBoundary D I) : I.Nonempty := by
  by_contra h
  exact hI.1 (Finset.not_nonempty_iff_eq_empty.mp h ▸ h_empty)

theorem orderedBoundary_iff_erase_max (D : Finset ι → Prop) (I : Finset ι)
    (hI : I.Nonempty) :
    OrderedBoundary D I ↔ ¬ D I ∧ D (I.erase (I.max' hI)) := by
  rw [OrderedBoundary, properPrefix_eq_erase_max I hI]

theorem orderedSuffix_eq_filter_max (G I : Finset ι) (hI : I.Nonempty) :
    orderedSuffix G I = G.filter (fun y => I.max' hI < y) := by
  ext y
  simp only [orderedSuffix, Finset.mem_filter, and_congr_right_iff]
  intro _
  constructor
  · intro h
    exact h _ (I.max'_mem hI)
  · intro h x hx
    exact lt_of_le_of_lt (I.le_max' x hx) h

theorem orderedSuffix_insert_ground {G I : Finset ι} {a : ι}
    (hI : I ⊆ G) (ha : ∀ x ∈ G, x < a) :
    orderedSuffix (insert a G) I = insert a (orderedSuffix G I) := by
  ext y
  simp only [orderedSuffix, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hya | hy, h⟩
    · exact Or.inl hya
    · exact Or.inr ⟨hy, h⟩
  · rintro (rfl | ⟨hy, h⟩)
    · exact ⟨Or.inl rfl, fun x hx => ha x (hI hx)⟩
    · exact ⟨Or.inr hy, h⟩

theorem orderedSuffix_insert_max {G I : Finset ι} {a : ι}
    (ha : ∀ x ∈ G, x < a) :
    orderedSuffix (insert a G) (insert a I) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hy, h⟩ := Finset.mem_filter.mp hy
  have hay := h a (Finset.mem_insert_self a I)
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact (lt_irrefl _) hay
  · exact lt_asymm hay (ha y hy)

theorem retainedPolynomial_insert_max (G : Finset ι) (D : Finset ι → Prop)
    (u : ι → R) {a : ι} (ha : a ∉ G) (hD : Hereditary D) :
    retainedPolynomial (insert a G) D u + newBoundaryPolynomial G D u a =
      retainedPolynomial G D u * (1 + u a) := by
  classical
  unfold retainedPolynomial newBoundaryPolynomial
  rw [Finset.sum_powerset_insert ha, Finset.sum_mul]
  rw [add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  have hai : a ∉ I := fun h => ha (Finset.mem_powerset.mp hI h)
  rw [Finset.prod_insert hai]
  by_cases hi : D I
  · by_cases hj : D (insert a I) <;> simp [hi, hj] <;> ring1
  · have hj : ¬ D (insert a I) := fun h => hi (hD (Finset.subset_insert a I) h)
    simp [hi, hj]

theorem boundaryPolynomial_insert_max (G : Finset ι) (D : Finset ι → Prop)
    (u : ι → R) {a : ι} (ha : ∀ x ∈ G, x < a) :
    boundaryPolynomial (insert a G) D u =
      boundaryPolynomial G D u * (1 + u a) + newBoundaryPolynomial G D u a := by
  classical
  have haG : a ∉ G := fun h => (lt_irrefl a) (ha a h)
  unfold boundaryPolynomial newBoundaryPolynomial
  rw [Finset.sum_powerset_insert haG, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro I hI
    have hIG := Finset.mem_powerset.mp hI
    rw [orderedSuffix_insert_ground hIG ha]
    have has : a ∉ orderedSuffix G I := fun h => haG (Finset.mem_filter.mp h).1
    rw [Finset.prod_insert has]
    split_ifs <;> simp [mul_comm, mul_left_comm]
  · apply Finset.sum_congr rfl
    intro I hI
    have hIG := Finset.mem_powerset.mp hI
    have hai : a ∉ I := fun h => haG (hIG h)
    rw [orderedSuffix_insert_max ha]
    rw [OrderedBoundary, properPrefix_insert_max (fun x hx => ha x (hIG hx))]
    rw [Finset.prod_empty, mul_one, Finset.prod_insert hai]
    by_cases hi : D I <;> by_cases hj : D (insert a I) <;> simp [hi, hj]

/-- General first-excluded-prefix identity before inserting a scalar parameter. -/
theorem first_excluded_prefix (G : Finset ι) (D : Finset ι → Prop)
    (u : ι → R) (hD : Hereditary D) (h_empty : D ∅) :
    (∏ x ∈ G, (1 + u x)) =
      retainedPolynomial G D u + boundaryPolynomial G D u := by
  classical
  induction G using Finset.induction_on_max with
  | empty => simp [retainedPolynomial, boundaryPolynomial, OrderedBoundary, h_empty]
  | @insert a G ha ih =>
    have haG : a ∉ G := fun h => (lt_irrefl a) (ha a h)
    rw [Finset.prod_insert haG, ih, boundaryPolynomial_insert_max G D u ha]
    calc
      (1 + u a) * (retainedPolynomial G D u + boundaryPolynomial G D u) =
          retainedPolynomial G D u * (1 + u a) +
            boundaryPolynomial G D u * (1 + u a) := by ring1
      _ = retainedPolynomial (insert a G) D u +
          (boundaryPolynomial G D u * (1 + u a) + newBoundaryPolynomial G D u a) := by
        rw [← retainedPolynomial_insert_max G D u haG hD]
        ring1

/-- Article Lemma 5.1: the full polynomial statement, over any commutative semiring.

The first sum is over retained sets and the second over their ordered boundary.
For each boundary set the suffix lies strictly above its maximum, as proved in
`orderedSuffix_eq_filter_max`. The empty product convention is provided by `Finset.prod`.
-/
theorem stopped_expansion (G : Finset ι) (D : Finset ι → Prop)
    (u : ι → R) (t : R) (hD : Hereditary D) (h_empty : D ∅) :
    (∏ x ∈ G, (1 + t * u x)) =
      (∑ I ∈ retainedSets G D, t ^ I.card * ∏ x ∈ I, u x) +
      ∑ I ∈ boundarySets G D,
        (t ^ I.card * ∏ x ∈ I, u x) *
          ∏ y ∈ orderedSuffix G I, (1 + t * u y) := by
  classical
  simpa [retainedSets, boundarySets, retainedPolynomial, boundaryPolynomial, Finset.sum_filter,
    Finset.prod_mul_distrib] using
    first_excluded_prefix G D (fun x => t * u x) hD h_empty

end PaperP1.Algebra
