module

public import PaperP1.PNT.SobolevCS

/-!
Selected from AlexKontorovich/PrimeNumberTheoremAnd, PrimeNumberTheoremAnd/Sobolev.lean,
commit 127b50e33f6033e2147921167a117af96d9ba4ea, Git blob 1f98bcbccc7ba3b9c9ee02ec95404731085368f9,
source lines 117–132, Apache-2.0. Adaptation: P1 namespaces,
Lean 4.36 module/public declarations and named instances.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNT.trunc

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}


instance pntSobolevTruncInstance1 : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance pntSobolevTruncInstance2 : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp]
lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end PaperP1.PNT.trunc
