/- The eight minimal ways to cover a six-cycle by vertices and edges.
This catalogue supplements the paper; the width theorem does not use it. -/
module
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Image
@[expose] public section
set_option autoImplicit false

namespace Plane.CapCatalogue

abbrev Node := Fin 6
abbrev Pattern := Finset Node × Finset Node

/-- Edge `i` joins vertices `i` and `i + 1`, with indices modulo six. -/
def Covers (singletons edges : Finset Node) : Prop :=
  ∀ i : Node, i ∈ singletons ∨ i ∈ edges ∨ i - 1 ∈ edges

instance (s e : Finset Node) : Decidable (Covers s e) :=
  inferInstanceAs (Decidable (∀ i : Node, i ∈ s ∨ i ∈ e ∨ i - 1 ∈ e))

/-- A cover from which no selected vertex or edge can be removed. -/
def Minimal (singletons edges : Finset Node) : Prop :=
  Covers singletons edges ∧
    (∀ i ∈ singletons, ¬ Covers (singletons.erase i) edges) ∧
    (∀ i ∈ edges, ¬ Covers singletons (edges.erase i))

instance (s e : Finset Node) : Decidable (Minimal s e) := by
  unfold Minimal
  infer_instance

/-- Rows A–H of the paper, written as (selected vertices, selected edges). -/
def representatives : List Pattern :=
  [({0, 1, 2, 3, 4, 5}, ∅), ({2, 3, 4, 5}, {0}),
   ({3, 4, 5}, {0, 1}), ({4, 5}, {0, 2}),
   ({2, 5}, {0, 3}), ({5}, {0, 1, 3}),
   (∅, {0, 2, 4}), (∅, {0, 1, 3, 4})]

/-- Rotation `i ↦ r + i`, or reflection `i ↦ r - i`.
Under reflection edge `i` starts at `r - i - 1`. -/
def transform (p : Pattern) (r : Node) (reflect : Bool) : Pattern :=
  (p.1.image fun i => if reflect then r - i else r + i,
   p.2.image fun i => if reflect then r - i - 1 else r + i)

def orbit (p : Pattern) : Finset Pattern :=
  Finset.univ.image fun g : Node × Bool => transform p g.1 g.2

def catalogue : Finset Pattern := representatives.toFinset.biUnion orbit

/-- Exact enumeration of all pairs of vertex and edge subsets, checked by the kernel. -/
theorem minimal_patterns :
    (Finset.univ.filter fun p : Pattern => Minimal p.1 p.2) = catalogue := by
  decide +kernel

/-- Every minimal cover, and only a minimal cover, is a symmetry of a displayed row. -/
theorem classification (singletons edges : Finset Node) :
    Minimal singletons edges ↔ (singletons, edges) ∈ catalogue := by
  rw [← minimal_patterns]
  simp

theorem pattern_count : catalogue.card = 39 := by decide +kernel

theorem representative_count : representatives.length = 8 := rfl

theorem orbit_sizes : representatives.map (fun p => (orbit p).card) =
    [1, 6, 6, 6, 3, 12, 2, 3] := by decide +kernel

/-- The eight rows represent different symmetry classes. -/
theorem disjoint_orbits : representatives.Pairwise
    (fun p q => Disjoint (orbit p) (orbit q)) := by decide +kernel

end Plane.CapCatalogue
