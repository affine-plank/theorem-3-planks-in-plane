# The affine plank conjecture for three planks in the plane

[![Proof checks](https://github.com/affine-plank/theorem-3-planks-in-plane/actions/workflows/proof.yml/badge.svg)](https://github.com/affine-plank/theorem-3-planks-in-plane/actions/workflows/proof.yml)

Three planks covering a convex body in the plane have total relative width
at least one.

- [Plane.lean](Plane.lean): definitions and theorem statement.
- [Plane/Proof.lean](Plane/Proof.lean): complete Lean proof, with a reading guide.
- [Paper](https://zazbrown.com/research/paper/affine-plank/three-planks-in-the-plane/):
  mathematical proof.

With [Lean installed](https://lean-lang.org/install/), check the proof from the
repository root:

```sh
lake exe cache get
lake build
```

To replay the proof through Lean's kernel:

```sh
lake env leanchecker --fresh Plane
```

For a [Comparator check](verification/README.md), including the permitted
axioms, see `verification/`.

Check the supplementary [cap catalogue](Plane/CapCatalogue.lean) separately:

```sh
lake build +Plane.CapCatalogue
```
