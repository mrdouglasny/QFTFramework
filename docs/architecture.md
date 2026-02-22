# QFTFramework Architecture

## Overview

QFTFramework is a shared Lean 4 library providing foundations for formalizing
quantum field theory. It is designed to be imported by concrete QFT projects
(OSforGFF, aqft2, pphi2, OSreconstruction) while remaining independent of
any particular theory or spacetime.

## Layer Structure

```
Layer 1: SpacetimeData
  ├── Spacetime.Euclidean  (ℝ^d: Schwartz test functions, Euclidean group)
  ├── Spacetime.Torus      (ℝ × T^{d-1}_L: cylinder spacetime)
  └── Spacetime.Lattice    (aℤ^d: discrete lattice)

Layer 2: TheoryData
  ├── QFTActionData        (Lagrangian: masses, couplings, gauge group)
  └── CFTData              (Bootstrap: central charge, OPE coefficients)

Layer 3: QFTData = SpacetimeData + TheoryData → Measure

Layer 4: Axiomatic Systems
  ├── Axioms.OsterwalderSchrader  (OS0-OS4, OSTheory)
  ├── Axioms.Wightman             (future: W1-W5)
  └── Axioms.HaagKastler          (future: A1-A5)
```

## Key Design Decisions

### Separation of Concerns
- **SpacetimeData**: geometry, test functions, distributions, symmetries
- **TheoryData**: field content, couplings (independent of spacetime)
- **QFTData**: combines the two to produce a measure

This enables the same theory (e.g., φ⁴) to be placed on different spacetimes,
and the same spacetime to host different theories.

### Complex Actions via Reweighting
QFTData always carries a real ProbabilityMeasure. A `weight : FieldConfig → ℂ`
handles complex actions (theta terms, Chern-Simons). OS axioms require
`hasRealAction` (weight = 1).

### Clustering via cocompact Filter
OS4 clustering uses `Filter.cocompact` on `TransVec`:
- ℝ^d: nontrivial (correlations decay as ‖a‖ → ∞)
- T^d: vacuously true (compact space)
- ℝ^k × T^{d-k}: only noncompact directions matter

## Source Projects

Definitions are drawn from:
- **OSforGFF** (`dimensions` branch): QFTFramework structure, flat/torus/lattice instances
- **aqft2** (`multidim` branch): SpacetimeData/TheoryData/QFTData hierarchy design
- **gaussian-field**: DyninMityaginSpace, nuclear Fréchet spaces (planned dependency)
- **ModularPhysics**: HaagKastler, Wightman, CFT patterns
- **OSreconstruction**: Minkowski geometry, Poincaré group, reconstruction theorem
- **pphi2**: Cylinder spacetime, Fourier mode test functions

## Dependencies

- **Mathlib**: Analysis, MeasureTheory, Topology
- **gaussian-field** (planned): Nuclear space infrastructure, Gaussian measure construction

## Future Work

- [ ] SpacetimeData instances that build on actual proofs
- [ ] Wightman axioms (from OSreconstruction patterns)
- [ ] Haag-Kastler axioms (from ModularPhysics patterns)
- [ ] CFT axioms
- [ ] Reconstruction theorems connecting axiomatic systems
- [ ] gaussian-field as a dependency for nuclear space infrastructure
