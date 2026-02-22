# QFTFramework — Abstract Axioms for Quantum Field Theory in Lean 4

QFTFramework defines the abstract structures needed to formalize quantum field theories and their axiomatic properties. It is spacetime-agnostic and theory-agnostic: the same definitions work for flat R^d, cylinders, tori, and lattices, and for free fields, phi^4, O(N) models, and beyond.

## Architecture

The framework is organized in four layers:

```
Layer 1: SpacetimeData    -- where the QFT lives (geometry, symmetries)
Layer 2: TheoryData       -- what the QFT is (field content, couplings)
Layer 3: QFTData          -- the QFT itself (measure + generating functional)
Layer 4: OSTheory         -- proof that it satisfies OS axioms
```

Each layer is independent of the ones below it. A `SpacetimeData` knows nothing about which theory will be placed on it; a `TheoryData` knows nothing about which spacetime it will live on. They combine in `QFTData` to produce a probability measure, and `OSTheory` adds proof obligations.

## Main definitions

### SpacetimeData

Packages the geometric, topological, and symmetry data for a spacetime:

```
structure SpacetimeData where
  TestFun : Type              -- real test functions (Schwartz, smooth periodic, etc.)
  TestFunC : Type             -- complex test functions
  toComplex : TestFun ->L[R] TestFunC
  FieldConfig : Type          -- field configurations (distributions)
  eval : FieldConfig -> TestFun -> R       -- distribution pairing <omega, f>
  eval_measurable : ...
  SymGroup : Type             -- symmetry group (Euclidean, translations, etc.)
  symAction : SymGroup -> TestFunC -> TestFunC
  TransVec : Type             -- translation vectors (subgroup of SymGroup)
  translateEmbed : TransVec -> SymGroup
  timeReflection : TestFun ->L[R] TestFun  -- (t, x) -> (-t, x)
  positiveTimeSubmodule : Submodule R TestFun
  timeShift : R -> FieldConfig -> FieldConfig
```

Built-in spacetime instances:

| Spacetime | File | Test functions | Status |
|-----------|------|---------------|--------|
| R^d | `Spacetime/Euclidean.lean` | `SchwartzMap (EuclideanSpace R (Fin d)) R` | Concrete types |
| R x T^{d-1}_L | `Spacetime/Torus.lean` | Axiomatized (`TestFunctionTorus`) | Axiomatized |
| aZ^d | `Spacetime/Lattice.lean` | `(Fin d -> Z) -> R` | Concrete types |

The torus test functions are axiomatized because Mathlib does not provide Schwartz-type spaces on mixed R x torus domains. The [GFF](https://github.com/mrdouglasny/GFF) repo fills these slots with concrete types from [gaussian-field](https://github.com/mrdouglasny/gaussian-field).

### TheoryData

Abstract theory specification, independent of spacetime:

```
structure TheoryData where
  InternalSymGroup : Type     -- global symmetry (Unit, ZMod 2, O(N), ...)
  nBosonic : N                -- number of bosonic field species
  nFermionic : N              -- number of fermionic field species
```

Extended by `QFTActionData` (Lagrangian: masses, couplings, gauge group) and `CFTData` (conformal bootstrap: central charge, OPE coefficients).

Standard instances:

```
freeScalar (m : R) : QFTActionData          -- 1 boson, no interactions
phi4Theory (m lam : R) : QFTActionData      -- 1 scalar, V(phi) = lam * phi^4, Z2 symmetry
oNModel (N : N) (m lam : R) : QFTActionData -- N scalars, O(N) symmetry, quartic coupling
```

### QFTData

Combines spacetime + theory into a concrete QFT:

```
structure QFTData (S : SpacetimeData) (T : TheoryData) where
  measure : ProbabilityMeasure S.FieldConfig
  weight : S.FieldConfig -> C       -- complex reweighting (1 for real actions)
  weight_integrable : Integrable weight measure.toMeasure
  genFunC : S.TestFunC -> C         -- generating functional Z[J]
```

The `weight` field handles complex actions (theta terms, finite-density QCD) via reweighting: the base measure is always real and positive, and `weight = exp(-i S_I)` encodes the imaginary part of the action.

### OSTheory — Osterwalder-Schrader Axioms

```
structure OSTheory (S : SpacetimeData) (T : TheoryData) extends QFTData S T where
  real_action : hasRealAction         -- weight = 1
  os0 : OS0_Analyticity S toQFTData  -- Z[J] analytic in test function coefficients
  os1 : OS1_Regularity S toQFTData   -- |Z[f]| <= exp(c * N(f))
  os2 : OS2_Invariance S toQFTData   -- Z[f] = Z[g . f] for g in SymGroup
  os3 : OS3_ReflectionPositivity S toQFTData  -- sum c_i c_j Re(Z[f_i - Theta f_j]) >= 0
  os4_clustering : OS4_Clustering S toQFTData -- correlations decay (via cocompact filter)
  os4_ergodicity : OS4_Ergodicity S toQFTData -- time averages converge
```

OS4 clustering uses `Filter.cocompact` on `TransVec`, which automatically handles different spacetime topologies: nontrivial on R^d, vacuously true on compact spaces like T^d.

## File structure

```
QFTFramework/
  QFTFramework.lean                     -- root import
  QFTFramework/
    SpacetimeData.lean                  -- geometry + symmetry + time structure
    TheoryData.lean                     -- field content + couplings + standard theories
    QFTData.lean                        -- measure + generating functional
    Spacetime/
      Euclidean.lean                    -- R^d with Euclidean group E(d)
      Torus.lean                        -- R x T^{d-1}_L (axiomatized test functions)
      Lattice.lean                      -- aZ^d with hypercubic symmetry
    Axioms/
      OsterwalderSchrader.lean          -- OS0-OS4 + OSTheory bundle
```

## Downstream projects

- **[gaussian-field](https://github.com/mrdouglasny/gaussian-field)** — Proves the functional analysis theorems (nuclear spaces, Gaussian measures) that QFTFramework's abstract slots require.

- **[GFF](https://github.com/mrdouglasny/GFF)** — Bridges gaussian-field and QFTFramework: fills `SpacetimeData` with concrete nuclear tensor products, constructs `QFTData` using Gaussian measures, and states `OSTheory` for the free field on cylinders, tori, and R^d.

## Building

```
lake update
lake build
```

Requires Lean v4.28.0 and Mathlib.

## References

- Osterwalder and Schrader, *Axioms for Euclidean Green's functions* I & II
- Glimm and Jaffe, *Quantum Physics*, Chapters 6 and 19
