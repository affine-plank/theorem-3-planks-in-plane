/- Three planks covering a convex planar set with nonempty interior
have total relative width ≥ 1. -/
module
public import Plane.Proof
@[expose] public section
set_option autoImplicit false

namespace Plane
open scoped BigOperators

abbrev Point := ℝ × ℝ

/-- A plank represented by a nonconstant affine function
f(x,y) = ax + by + c. -/
abbrev Plank :=
  {f : Point →ᵃ[ℝ] ℝ // ∃ x y, f x ≠ f y}

/-- Its points lie between the parallel lines
where the function equals 0 and 1. -/
instance : Coe Plank (Set Point) :=
  ⟨fun P => {x | 0 ≤ P.val x ∧ P.val x ≤ 1}⟩

/-- Plank width divided by body width in the same direction.
`P.val '' K` is the image of K on the real line;
its diameter is the shadow's length. -/
noncomputable def relativeWidth (K : Set Point) (P : Plank) : ℝ :=
  1 / Metric.diam (P.val '' K)

/-- If three planks cover K, their relative widths sum to at least one.
`Fin 3` indexes the planks by 0, 1 and 2. -/
theorem three_planks_cover_body
    (K : Set Point) (convex : Convex ℝ K)
    (interior_nonempty : (interior K).Nonempty)
    (P : Fin 3 → Plank)
    (covers : K ⊆ ⋃ i, (P i : Set Point)) :
    1 ≤ ∑ i, relativeWidth K (P i) := by
  exact _root_.PlaneProof.three_planks_cover_convex
    K convex interior_nonempty (fun i => (P i).val)
    (fun i => (P i).property) covers

end Plane
