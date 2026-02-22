# Multidimensional Generalization Plan

**Branch:** `multidim` (based on `general-measure`)  
**Goal:** Prove OS axioms for the GFF in parametric dimension d, introducing `SpacetimeData`, `TheoryData`/`QFTActionData`/`CFTData`, and `QFTData` structures from the start.

## Lessons from the Previous Attempt (`multidimensional` branch)

The previous approach tried to make every definition parametric in `d : ℕ` by mechanically replacing `STDimension` → `d` through 50 files. This led to:
- A cascade of `(hd : d = 4)` hypotheses propagating through ~40 declarations
- Tension between algebraic properties (work for any d given integrability) and analytic properties (need d=4 for specific formulas)
- No clear separation between what's geometric and what's field-theoretic

**Key insight:** The right abstraction isn't "replace 4 with d" — it's "separate the abstract OS axiom framework from the concrete Euclidean/GFF construction."

## Architecture: Two Structures

### `SpacetimeData` — What a spacetime provides

```lean
/-- Data package for a spacetime on which OS axioms can be stated.
    This bundles the geometric, topological, and symmetry data
    needed to formulate OS0–OS4 without fixing ℝ^d. -/
structure SpacetimeData where
  -- Test function spaces
  TestFun : Type*
  TestFunℂ : Type*
  [instTestACG : AddCommGroup TestFun]
  [instTestModule : Module ℝ TestFun]
  [instTestTopSpace : TopologicalSpace TestFun]
  [instTestℂACG : AddCommGroup TestFunℂ]
  [instTestℂModule : Module ℂ TestFunℂ]
  [instTestℂTopSpace : TopologicalSpace TestFunℂ]
  toComplex : TestFun →L[ℝ] TestFunℂ  -- embedding ℝ-valued → ℂ-valued

  -- Distribution space (field configurations)
  FieldConfig : Type*
  [instFieldConfigMeasSpace : MeasurableSpace FieldConfig]
  eval : FieldConfig → TestFun → ℝ       -- ⟨ω, f⟩
  eval_measurable : ∀ f, Measurable (fun ω => eval ω f)

  -- Symmetry group (Euclidean group for ℝ^d, translations for torus, etc.)
  SymGroup : Type*
  symAction : SymGroup → TestFunℂ → TestFunℂ

  -- Translation subgroup of SymGroup, with metric structure.
  -- For ℝ^d: the translation part of E(d) = O(d) ⋉ ℝ^d, isomorphic to ℝ^d
  -- For torus: translations in (ℝ/ℤ)^d
  -- For ℝ^k × T^{d-k}: translations in ℝ^k × T^{d-k}
  -- The topology of TransVec determines which directions are compact vs noncompact.
  -- OS4 clustering uses Filter.cocompact on TransVec, so it is nontrivial only
  -- along noncompact directions (and vacuously true for fully compact spaces).
  TransVec : Type*  -- translation vectors
  [instTransVecNorm : NormedAddCommGroup TransVec]
  translateEmbed : TransVec → SymGroup  -- embedding into symmetry group
  -- Derived: translate acts on test functions via symAction ∘ translateEmbed

  -- Heat kernel K_t : the fundamental solution of the heat equation ∂_t u = Δu.
  -- This is purely geometric (depends on the Laplacian/metric of the space).
  -- For ℝ^d: K_t(x,y) = (4πt)^{-d/2} exp(-‖x-y‖²/4t)
  -- For torus: K_t(x,y) = Σ_n exp(-4π²|n|²t) e^{2πi n·(x-y)}
  -- For manifolds: spectral expansion K_t(x,y) = Σ_k e^{-λ_k t} φ_k(x) φ_k(y)
  -- The free covariance is derived via Schwinger representation:
  --   C_m(f,g) = ∫₀^∞ e^{-m²t} ⟨f, K_t g⟩ dt
  heatKernel : ℝ → TestFun → TestFun  -- t ↦ (f ↦ K_t * f), the heat semigroup on test functions

  -- Time structure for OS axioms
  timeReflection : TestFun →L[ℝ] TestFun
  timeReflection_involutive : Function.Involutive timeReflection
  PositiveTimeFun : Type*  -- subtype of test functions supported at t > 0
  ptfToTestFun : PositiveTimeFun → TestFun  -- coercion
  timeShift : ℝ → FieldConfig → FieldConfig  -- time translations on distributions (for ergodicity)
```

### `TheoryData` — Abstract theory specification

A QFT can be specified in different ways: by a Lagrangian action (with explicit
field content and couplings), by CFT axioms (central charge, OPE data), by
bootstrap constraints, by a lattice model, etc. `TheoryData` captures what all
these specifications share: the internal symmetry and the broad field content.

```lean
/-- Abstract specification of a quantum field theory's content.
    This is the most general notion — a theory can be specified
    by an action (QFTActionData), by CFT axioms (CFTData),
    by bootstrap constraints, or by other means.
    The common structure is the internal (global) symmetry group
    and the number of bosonic/fermionic field species. -/
structure TheoryData where
  -- Internal (global) symmetry group.
  -- Examples: Unit (trivial), ZMod 2 (Ising ℤ₂), OrthogonalGroup n ℝ (O(N) model)
  InternalSymGroup : Type*
  [instInternalSym : Group InternalSymGroup]
  -- Number of bosonic and fermionic field species
  -- (for a scalar: nBosonic = 1, nFermionic = 0;
  --  for QED: nBosonic = 1 (photon), nFermionic = 1 (electron))
  nBosonic : ℕ
  nFermionic : ℕ
```

### `QFTActionData extends TheoryData` — Lagrangian specification

A theory defined by an explicit Euclidean action with field content and couplings.

```lean
/-- A QFT specified by a Euclidean action S_E[φ,ψ,A].
    Lists the coupling constants that appear in the Lagrangian.
    The same action data can be placed on different spacetimes. -/
structure QFTActionData extends TheoryData where
  -- Gauge sector
  gaugeGroup : Type*     -- gauge group (e.g., Unit for no gauge, SU n, U n, etc.)
  [instGaugeGroup : Group gaugeGroup]

  -- Scalar sector
  scalarMassSq : Fin nBosonic → ℝ                          -- m²_i for each scalar
  scalarPotential : (Fin nBosonic → ℝ) → ℝ                 -- V(φ₁,...,φₙ), e.g. λ|φ|⁴

  -- Fermion sector
  fermionMass : Fin nFermionic → ℝ                          -- Dirac masses
  yukawaCoeff : Fin nFermionic → Fin nFermionic → Fin nBosonic → ℝ  -- Yukawa y_{ij}^a

  -- Gauge couplings
  gaugeCoupling : ℝ                                         -- gauge coupling g
  gaugeChargeScalar : Fin nBosonic → gaugeGroup → gaugeGroup
  gaugeChargeFermion : Fin nFermionic → gaugeGroup → gaugeGroup

-- The Euclidean action for QFTActionData T on spacetime S:
-- S_E[φ,ψ,A] = ∫ [ ½ Σᵢ (|∇φᵢ|² + m²ᵢ φᵢ²) + V(φ)
--               + Σᵢ ψ̄ᵢ(D̸ + mᵢ)ψᵢ + Σᵢⱼₐ yᵢⱼᵃ ψ̄ᵢ φₐ ψⱼ
--               + (1/4g²) Tr F² ] dμ
```

### `CFTData extends TheoryData` — Conformal bootstrap specification

A theory defined by conformal field theory data: central charge, primary
operators with conformal dimensions, and OPE coefficients. This is the natural
language for 2D CFTs (minimal models, WZW, Liouville) and for theories defined
via the conformal bootstrap in higher dimensions.

```lean
/-- A QFT specified by conformal bootstrap data.
    In the Euclidean signature, conformal symmetry constrains the
    correlation functions to be determined by the OPE data. -/
structure CFTData extends TheoryData where
  -- Central charge
  centralCharge : ℝ

  -- Primary operator spectrum
  PrimaryIndex : Type*  -- indexing type for primaries (could be Fin n or ℕ)
  conformalDim : PrimaryIndex → ℝ      -- scaling dimension Δ_i
  spin : PrimaryIndex → ℕ              -- spin ℓ_i

  -- OPE coefficients C_{ijk}: structure constants of the operator algebra
  opeCoeff : PrimaryIndex → PrimaryIndex → PrimaryIndex → ℝ

  -- The identity operator is a primary with Δ = 0
  unitOp : PrimaryIndex
  unitOp_dim : conformalDim unitOp = 0
  unitOp_spin : spin unitOp = 0

  -- Unitarity bound: Δ ≥ (d-2)/2 for scalars (dimension-dependent, so stated abstractly)
  dim_nonneg : ∀ i, 0 ≤ conformalDim i

  -- OPE symmetry
  opeCoeff_symm_12 : ∀ i j k, opeCoeff i j k = opeCoeff j i k
```

Examples:
```lean
/-- Free massive scalar: 1 boson, no fermions, trivial symmetry. -/
noncomputable def freeScalar (m : ℝ) (hm : 0 < m) : QFTActionData where
  InternalSymGroup := Unit
  nBosonic := 1
  nFermionic := 0
  gaugeGroup := Unit
  scalarMassSq := fun _ => m ^ 2
  scalarPotential := fun _ => 0    -- free theory: no interaction
  fermionMass := Fin.elim0
  yukawaCoeff := fun i => Fin.elim0 i
  gaugeCoupling := 0
  gaugeChargeScalar := fun _ g => g
  gaugeChargeFermion := fun i => Fin.elim0 i

/-- φ⁴ theory: 1 scalar with quartic self-coupling, ℤ₂ symmetry φ → -φ. -/
noncomputable def phi4 (m : ℝ) (hm : 0 < m) (λ : ℝ) (hλ : 0 ≤ λ) : QFTActionData where
  InternalSymGroup := ZMod 2
  nBosonic := 1
  nFermionic := 0
  gaugeGroup := Unit
  scalarMassSq := fun _ => m ^ 2
  scalarPotential := fun φ => λ * (φ 0) ^ 4
  fermionMass := Fin.elim0
  yukawaCoeff := fun i => Fin.elim0 i
  gaugeCoupling := 0
  gaugeChargeScalar := fun _ g => g
  gaugeChargeFermion := fun i => Fin.elim0 i

/-- 2D Ising CFT: c = 1/2, three primaries (1, σ, ε). -/
noncomputable def ising2D : CFTData where
  InternalSymGroup := ZMod 2
  nBosonic := 0
  nFermionic := 1   -- Majorana fermion (c = 1/2)
  centralCharge := 1 / 2
  PrimaryIndex := Fin 3  -- 𝟙, σ, ε
  conformalDim := ![0, 1/8, 1]         -- Δ_𝟙 = 0, Δ_σ = 1/8, Δ_ε = 1
  spin := ![0, 0, 0]                   -- all scalars
  opeCoeff := fun i j k => sorry        -- known exactly, but complex to write out
  unitOp := 0
  unitOp_dim := by simp [Matrix.cons_val_zero]
  unitOp_spin := by simp [Matrix.cons_val_zero]
  dim_nonneg := fun i => by fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  opeCoeff_symm_12 := sorry
```

### `QFTData` — A QFT = spacetime + theory → measure

The generating functional can be defined in two ways:

1. **Real action (Euclidean QFT):** The measure $d\mu = e^{-S_E[\phi]} \mathcal{D}\phi$
   is a genuine probability measure, and the generating functional is
   $Z[J] = \int e^{i\langle\omega, J\rangle} d\mu(\omega)$.
   OS axioms apply directly.

2. **Complex action:** When $S = S_R + iS_I$ has an imaginary part (e.g., theta
   terms $e^{i\theta Q}$, Chern-Simons, finite-density QCD), the "measure"
   is not positive. The standard approach is **reweighting**: define a real
   base measure $d\mu_0 = e^{-S_R} \mathcal{D}\phi$ and a complex weight
   function $w(\phi) = e^{-iS_I[\phi]}$, so that expectations become
   $\langle O \rangle = \frac{\int O \cdot w \, d\mu_0}{\int w \, d\mu_0}$.

The OS axioms (especially reflection positivity) require a real positive
measure — theories with genuinely complex actions don't satisfy them in
the standard form. We encode this as follows:

- `QFTData` always has a real `ProbabilityMeasure` (the base/Euclidean measure).
- An optional `weight : FieldConfig → ℂ` handles complex actions via reweighting.
- For real-action theories (the OS axiom case), `weight = 1` identically.
- `genFunℂ` is defined using the weight:
  $Z[J] = \int w(\omega) \, e^{i\langle\omega, J\rangle} \, d\mu(\omega)$.

This design correctly separates "has a measure" (always) from "satisfies OS
axioms" (only when weight = 1, i.e., real action).

```lean
/-- A quantum field theory: combines spacetime geometry with theory specification
    to produce a probability measure and generating functional.
    The `weight` function handles complex actions via reweighting:
    for real-action Euclidean theories, weight = 1. -/
structure QFTData (S : SpacetimeData) (T : TheoryData) where
  measure : ProbabilityMeasure S.FieldConfig
  -- Complex weight function for reweighting.
  -- For real-action theories: weight ω = 1 (and genFunℂ reduces to a CF).
  -- For complex-action theories: weight ω = exp(-i S_I[ω]).
  weight : S.FieldConfig → ℂ
  weight_integrable : Integrable weight measure.toMeasure
  -- The complex generating functional Z[J], defined via reweighting:
  -- Z[J] = ∫ weight(ω) exp(i⟨ω, J⟩) dμ(ω)
  genFunℂ : S.TestFunℂ → ℂ

-- For real-action theories, weight = 1 and we recover the standard CF formula.
-- This is a Prop-valued predicate, not data — keeps QFTData lean.
def QFTData.hasRealAction {S : SpacetimeData} {T : TheoryData}
    (Q : QFTData S T) : Prop :=
  ∀ ω, Q.weight ω = 1

-- The real generating functional (characteristic functional of the base measure):
noncomputable def QFTData.genFunR {S : SpacetimeData} {T : TheoryData}
    (Q : QFTData S T) (f : S.TestFun) : ℂ :=
  ∫ ω, Q.weight ω * Complex.exp (Complex.I * (S.eval ω f : ℂ)) ∂Q.measure.toMeasure
```

## OS Axioms as a Structure Extending QFTData

OS axioms require a real positive measure (reflection positivity is a
positivity condition). Only theories with `hasRealAction` can satisfy them.

```lean
/-- A quantum field theory satisfying all Osterwalder-Schrader axioms.
    Extends QFTData with OS0–OS4 as proof obligations.
    Requires hasRealAction (weight = 1), since reflection positivity
    needs a genuine positive measure.
    The master theorem constructs an instance of this structure. -/
structure OSTheory (S : SpacetimeData) (T : TheoryData) extends QFTData S T where
  -- The OS axioms require weight = 1 (real action)
  real_action : toQFTData.hasRealAction
  -- OS0: Analyticity of the generating functional
  os0_analyticity :
    ∀ (n : ℕ) (J : Fin n → S.TestFunℂ),
      AnalyticOn ℂ (fun z : Fin n → ℂ => genFunℂ (∑ i, z i • J i)) Set.univ

  -- OS1: Regularity (exponential bounds)
  os1_regularity :
    ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
      ∀ (f : S.TestFunℂ), ‖genFunℂ f‖ ≤ Real.exp (c * S.testFunℂNorm f)

  -- OS2: Symmetry invariance (Euclidean invariance for ℝ^d)
  os2_invariance :
    ∀ (g : S.SymGroup) (f : S.TestFunℂ), genFunℂ f = genFunℂ (S.symAction g f)

  -- OS3: Reflection positivity
  os3_reflection_positivity :
    ∀ (n : ℕ) (f : Fin n → S.PositiveTimeFun) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j *
        (toQFTData.genFunR S (S.ptfToTestFun (f i)
          - S.timeReflection (S.ptfToTestFun (f j)))).re

  -- OS4: Clustering (distant test functions become independent)
  -- Uses Filter.cocompact on TransVec:
  --   ℝ^d: ‖a‖ → ∞ (nontrivial clustering)
  --   T^d: vacuously true (compact, cocompact = ⊥)
  --   ℝ^k × T^{d-k}: only ℝ^k directions grow
  os4_clustering :
    ∀ (f g : S.TestFun),
      Filter.Tendsto
        (fun a : S.TransVec =>
          toQFTData.genFunR S (f + S.symActionR (S.translateEmbed a) g)
            - toQFTData.genFunR S f * toQFTData.genFunR S g)
        (Filter.cocompact S.TransVec)
        (nhds 0)

  -- OS4: Ergodicity (time averages converge to expectations)
  os4_ergodicity :
    ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → S.TestFunℂ),
      let A : S.FieldConfig → ℂ := fun ω =>
        ∑ j, z j * Complex.exp (S.evalℂ ω (f j))
      Filter.Tendsto
        (fun T : ℝ =>
          ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
            A (S.timeShift s ω) - ∫ ω', A ω' ∂measure.toMeasure‖^2 ∂measure.toMeasure)
        Filter.atTop (nhds 0)
```

The master theorem then has the clean signature:
```lean
-- QFTActionData extends TheoryData, so (freeScalar m hm).toTheoryData : TheoryData
theorem gff_os_theory (m : ℝ) (hm : 0 < m) :
    OSTheory euclidean4D (freeScalar m hm).toTheoryData := ...

-- Future: action-based theories
-- theorem phi4_2d_os (m : ℝ) (hm : 0 < m) (λ : ℝ) (hλ : 0 ≤ λ) (hλ_small : λ < ε) :
--     OSTheory (euclideanDim 2) (phi4 m hm λ hλ).toTheoryData := ...

-- Future: CFT-based theories (OS axioms from conformal bootstrap)
-- theorem ising_2d_os : OSTheory (euclideanDim 2) ising2D.toTheoryData := ...
```

## Concrete Instance: Euclidean ℝ^4

```lean
noncomputable def euclidean4D : SpacetimeData where
  TestFun := SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ
  TestFunℂ := SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℂ
  FieldConfig := WeakDual ℝ (SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ)
  eval := fun ω f => ω f
  SymGroup := QFT.E  -- the Euclidean group O(4) ⋉ ℝ^4
  symAction := QFT.euclidean_action
  TransVec := EuclideanSpace ℝ (Fin 4)  -- translation vectors ≅ ℝ^4
  translateEmbed := fun a => ⟨1, a⟩  -- pure translation in O(4) ⋉ ℝ^4
  timeReflection := QFT.compTimeReflectionReal
  PositiveTimeFun := QFT.PositiveTimeTestFunction
  -- ...
```

## Implementation Plan

### Phase 0: Define structures (new files, no changes to existing)

Create three new files:
1. **`OSforGFF/SpacetimeData.lean`** — `SpacetimeData` structure
2. **`OSforGFF/TheoryData.lean`** — `TheoryData`, `QFTActionData`, `CFTData`, and instances (`freeScalar`, `phi4`, `ising2D`)
3. **`OSforGFF/QFTData.lean`** — `QFTData`, `OSTheory`, abstract OS axiom definitions

These files import nothing from the project (only Mathlib). The existing `OS_Axioms.lean` and `Basic.lean` remain untouched.

### Phase 1: Build the bridge (new file, no changes to existing)

Create **`OSforGFF/EuclideanInstance.lean`**:
- Define `euclidean4D : SpacetimeData`
- Define `gffQFTData (m : ℝ) [Fact (0 < m)] : QFTData euclidean4D (freeScalar m hm).toTheoryData`
- Prove equivalence lemmas:
  ```lean
  -- Show the abstract OS axioms reduce to the concrete ones
  theorem abstract_OS0_iff_concrete (m : ℝ) [Fact (0 < m)] :
      OS0_Analyticity euclidean4D (gffQFTData m) ↔
      OSforGFF.OS0_Analyticity (μ_GFF m) := ...
  ```

### Phase 2: Lift the master theorem

Create **`OSforGFF/GFFmaster_abstract.lean`**:
- Use the bridge lemmas to prove `SatisfiesAllOS_abstract euclidean4D (gffQFTData m)`
- This is a thin wrapper that calls existing proofs through the bridge

### Phase 3: Parametric Euclidean instance

Create **`OSforGFF/EuclideanInstance_d.lean`**:
- Define `euclideanDim (d : ℕ) [Fact (0 < d)] [Fact (2 ≤ d)] : SpacetimeData`
- This needs the covariance kernel to be integrable (dimension-dependent)
- For proofs that work in any dimension: wire through directly
- For proofs that need d=4: provide as hypotheses or use a typeclass

### Phase 4: Generalize individual axiom proofs

For each OS axiom proof file, assess whether it generalizes:

| Axiom | File | Effort | Notes |
|-------|------|--------|-------|
| OS0 | OS0_GFF.lean | Low | Uses covariance opaquely, should generalize to any `QFTData` with Gaussian generating functional |
| OS1 | OS1_GFF.lean | Medium | Has `STDimension ≥ 3` checks; needs kernel integrability hypothesis |
| OS2 | OS2_GFF.lean | Low | Follows from covariance Euclidean invariance; could abstract to "covariance is sym-invariant" |
| OS3 | OS3_GFF.lean + support | High | Deepest dimension dependence: mixed representation has `(2π)^d` factors, Fourier normalization, spatial decomposition |
| OS4 | OS4_Clustering.lean | Medium | Uses `Fin.sum_univ_four`, spatial decay; generalizes if we assume covariance decay |
| OS4 | OS4_Ergodicity.lean | Low | Mostly abstract; works from clustering |

## File Dependency Layers

```
Layer 0 (Mathlib only):
  SpacetimeData.lean, TheoryData.lean, QFTData.lean

Layer 1 (abstract OS):
  OS_Axioms_abstract.lean  — defines OS0–OS4 on SpacetimeData/QFTData/TheoryData

Layer 2 (Euclidean geometry):
  Euclidean.lean, DiscreteSymmetry.lean, SpacetimeDecomp.lean,
  PositiveTimeTestFunction_real.lean, TimeTranslation.lean

Layer 3 (Euclidean covariance, fixed d=4):
  Covariance.lean, CovarianceMomentum.lean, CovarianceR.lean, Parseval.lean,
  BesselFunction.lean, FourierTransforms.lean, FunctionalAnalysis.lean

Layer 4 (GFF construction, fixed d=4):
  GaussianFieldBridge.lean, GFFMconstruct.lean, GaussianFreeField.lean,
  GFFIsGaussian.lean, GaussianMoments.lean

Layer 5 (OS proofs, fixed d=4):
  OS0_GFF.lean, OS1_GFF.lean, OS2_GFF.lean, OS3_*.lean, OS4_*.lean

Layer 6 (Master assembly):
  GFFmaster.lean  — concrete d=4 master theorem
  GFFmaster_abstract.lean  — abstract master theorem via bridge
```

## What NOT to Do

1. **Don't change existing concrete code.** The existing d=4 proofs are complete and correct. The abstraction layer goes on top.
2. **Don't parametrize `CovarianceMomentum.lean` or `OS3_MixedRep.lean`.** These are inherently dimension-specific (Fourier normalization, Bessel formulas). They stay as d=4 implementations.
3. **Don't force all axiom proofs to be abstract.** Some (OS3) may always need dimension-specific arguments. The abstract framework provides the *interface*; concrete instances provide the *implementation*.

## What Changes vs. Previous Attempt

| Aspect | `multidimensional` branch | This plan |
|--------|--------------------------|-----------|
| Approach | Replace `STDim=4` with `d:ℕ` everywhere | Abstract interface on top of concrete d=4 |
| Files changed | ~40 | ~5 new, 0 existing modified |
| Risk of breakage | High (cascading type changes) | None (additive only) |
| d=2 support | Requires re-proving everything for d=2 | Define `euclideanDim 2 : SpacetimeData`, provide proofs |
| Torus support | Would need another complete rework | Define `torusSpacetime : SpacetimeData`, provide proofs |

## Open Design Questions

1. **Should `SpacetimeData` be a structure or a class?** Structure is simpler and avoids instance search issues. Class enables `variable [SpacetimeData S]` syntax but risks diamond problems.

2. **How much covariance data belongs in `SpacetimeData` vs `QFTData`?** The covariance is determined by the Laplacian (geometry) and the mass (physics). Currently the plan puts it in `QFTData` implicitly through the generating functional. But for proving OS3, we need the bilinear form `C(f,g)` explicitly.

3. **Should `QFTData` require Gaussianity?** The OS axioms apply to any QFT, not just Gaussian. But for our proofs, we only verify them for Gaussian measures. Could have `QFTData` be general and `GaussianQFTData extends QFTData` with the CF formula.

4. **How to handle `PositiveTimeFun`?** Currently a subtype with a membership proof. In the abstract setting, it could be any submodule of `TestFun`. The key property needed is that `timeReflection` maps `PositiveTimeFun` to "negative-time" functions.

5. **Complex actions and the weight function.** The `weight : FieldConfig → ℂ`
   design handles several important cases:
   - **Theta terms:** $w(\phi) = e^{i\theta Q[\phi]}$ where $Q$ is topological charge.
   - **Chern-Simons:** After gauge-fixing, the effective action can be complex.
   - **Fermion determinant sign problems:** $w(\phi) = \det(D + m) / |\det(D + m)|$.
   - **Reweighting / importance sampling:** Any $w$ with $\int |w| d\mu < \infty$.

   For generating functionals with complex actions, OS axioms don't hold
   directly. Alternative reconstruction theorems exist (e.g., for Chern-Simons
   via surgery/TQFT axioms), but are outside the current scope.

   Design choice: `weight_integrable` could be strengthened to
   `weight_memLp : MemLp weight 2 measure.toMeasure` if we need L² estimates
   for reweighted expectations. For now, L¹ suffices.
