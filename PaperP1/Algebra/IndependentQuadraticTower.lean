module

public import PaperP1.Algebra.FiniteQuadraticTower
public import PaperP1.Algebra.QuadraticSquareDescent
public import Mathlib.Data.List.Basic

/-! # Independent square classes make the actual finite quadratic tower a field -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.IndependentQuadraticTower

open PaperP1.FiniteQuadraticTower

def Independent {K : Type u} [CommRing K] (s : List K) : Prop :=
  ∀ t : List K, t.Sublist s → t ≠ [] → ¬ IsSquare t.prod

theorem tail_independent {K : Type u} [CommRing K] {a : K} {s : List K}
    (hs : Independent (a :: s)) : Independent s := by
  intro t ht hne
  exact hs t (ht.cons a) hne

theorem sublist_square_step {K : Type u} [CommRing K] (a g : K) (s : List K) :
    ((∃ t : List K, t.Sublist s ∧ IsSquare (g * t.prod)) ∨
      (∃ t : List K, t.Sublist s ∧ IsSquare ((a * g) * t.prod))) ↔
      ∃ t : List K, t.Sublist (a :: s) ∧ IsSquare (g * t.prod) := by
  constructor
  · rintro (⟨t, ht, hs⟩ | ⟨t, ht, hs⟩)
    · exact ⟨t, ht.cons a, hs⟩
    · refine ⟨a :: t, ht.cons_cons a, ?_⟩
      convert hs using 1
      simp only [List.prod_cons]
      ring
  · rintro ⟨t, ht, hs⟩
    rcases List.sublist_cons_iff.mp ht with htail | ⟨r, rfl, hr⟩
    · exact Or.inl ⟨t, htail, hs⟩
    · refine Or.inr ⟨r, hr, ?_⟩
      convert hs using 1
      simp only [List.prod_cons]
      ring

theorem field_and_square_descent (K : Type u) [Field K] [CharZero K] (s : List K) :
    Independent s → IsField (Tower K s) ∧
      ∀ g : K, IsSquare (algebraMap K (Tower K s) g) ↔
        ∃ t : List K, t.Sublist s ∧ IsSquare (g * t.prod) := by
  induction s with
  | nil =>
    intro _hs
    refine ⟨Field.toIsField K, ?_⟩
    intro g
    constructor
    · intro hg
      change IsSquare g at hg
      exact ⟨[], List.Sublist.refl [], by simpa only [List.prod_nil, mul_one] using hg⟩
    · rintro ⟨t, ht, hg⟩
      have hzero : t = [] := List.sublist_nil.mp ht
      subst t
      change IsSquare g
      simpa only [List.prod_nil, mul_one] using hg
  | cons a s ih =>
    intro hs
    obtain ⟨hfield, hdescent⟩ := ih (tail_independent hs)
    let : Field (Tower K s) := hfield.toField
    have ha : ¬ IsSquare (algebraMap K (Tower K s) a) := by
      intro hsq
      obtain ⟨t, ht, hprod⟩ := (hdescent a).mp hsq
      exact hs (a :: t) (ht.cons_cons a) (List.cons_ne_nil _ _) hprod
    let : Fact (¬ IsSquare (algebraMap K (Tower K s) a)) := ⟨ha⟩
    refine ⟨Field.toIsField (Tower K (a :: s)), ?_⟩
    intro g
    change IsSquare (algebraMap (Tower K s) (Tower K (a :: s)) (algebraMap K (Tower K s) g)) ↔ _
    rw [QuadraticSquareDescent.square_iff _ _ (BiquadraticNorm.nonsquare_ne_zero _ ha),
      ← map_mul, hdescent g, hdescent (a * g)]
    exact sublist_square_step a g s

theorem isField (K : Type u) [Field K] [CharZero K] (s : List K) (hs : Independent s) :
    IsField (Tower K s) := (field_and_square_descent K s hs).1

theorem square_descent (K : Type u) [Field K] [CharZero K] (s : List K) (hs : Independent s) (g : K) :
    IsSquare (algebraMap K (Tower K s) g) ↔
      ∃ t : List K, t.Sublist s ∧ IsSquare (g * t.prod) := (field_and_square_descent K s hs).2 g

end PaperP1.IndependentQuadraticTower
