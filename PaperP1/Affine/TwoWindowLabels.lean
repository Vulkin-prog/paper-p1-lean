module

public import PaperP1.Arithmetic.EvenSquareClasses
public import PaperP1.Arithmetic.PrivateWindowPrimes

/-! # The disjoint formal vertex copies of two complete windows

The label definition is selected from Paper C, `PaperC/Affine/TwoStartSystem.lean`,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Git blob
94e01496f72b742b4f85e6c2630de078e3cddb41, by Vulkin-prog, Apache-2.0.
The uniqueness proof below uses the already checked P1 private-prime lemma.
No old two-start probability or geometric interface is imported.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open PaperP1.Arithmetic

def twoStartCompleteVertexLabel (x y L : ℕ) : Sum (Fin (L + 1)) (Fin (L + 1)) → ℕ
  | Sum.inl v => startCompleteVertexLabel x L v
  | Sum.inr v => startCompleteVertexLabel y L v

theorem parityVec_ne_zero_unique_in_start {x L p : ℕ}
    (hx : 1 ≤ x) (hp : L + 1 < p) {v w : Fin (L + 1)}
    (hv : parityVec (startCompleteVertexLabel x L v) p ≠ 0)
    (hw : parityVec (startCompleteVertexLabel x L w) p ≠ 0) : v = w := by
  have hxpos : 0 < x := by omega
  by_contra hne
  apply hw
  rw [startCompleteVertexLabel_eq_offset hxpos]
  exact PrivateWindowPrimes.parity_other_vertex_zero hp v w hne
    (by simpa only [startCompleteVertexLabel_eq_offset hxpos] using hv)

end PaperP1.Affine
