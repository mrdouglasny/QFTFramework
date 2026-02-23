# Comparison of OS Axiom Formulations

## Overview

The Osterwalder-Schrader axioms have been formalized in three Lean 4
projects using two different mathematical frameworks. This document
compares the formulation choices.

### Projects

- **OSforGFF**: OS axioms for the Gaussian free field (d=4 fixed,
  dimension-parametric on `dimensions` branch)
- **QFTFramework**: Abstract OS axioms parametrized over `SpacetimeData`
  and `QFTData`
- **OSreconstruction**: OS axioms in the Schwinger function formalism,
  targeting the Wightman reconstruction theorem

### Formalisms

| | OSforGFF / QFTFramework | OSreconstruction |
|---|---|---|
| Central object | Generating functional Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω) | Schwinger functions S_n(f₁,...,fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ |
| Axiom labeling | OS0–OS4 (Glimm-Jaffe) | E0–E4 (OS I/II papers) |
| Parametrization | OSforGFF: d=4 fixed; QFTFramework: abstract SpacetimeData | Parametric d with `[NeZero d]` |

The generating functional formalism packages all n-point functions into
a single object Z[J]. The Schwinger function formalism works with the
individual n-point functions S_n directly. The two are related by
functional differentiation: S_n is the n-th functional derivative of Z.

## OS0 / E0 — Analyticity vs Temperedness

This is the biggest formulation choice.

**OSforGFF and QFTFramework** define OS0 as analyticity of the generating
functional: the map (z₁,...,zₙ) ↦ Z[Σᵢ zᵢJᵢ] is entire (analytic on
all of ℂⁿ) for any finite collection of complex test functions Jᵢ.

    def OS0_Analyticity (Q : QFTData S T) : Prop :=
      ∀ (n : ℕ) (J : Fin n → S.TestFunℂ),
        AnalyticOn ℂ (fun z : Fin n → ℂ =>
          Q.genFunℂ (∑ i, z i • J i)) Set.univ

This uses Mathlib's `AnalyticOn` over `ℂ` on `Set.univ`.

**OSreconstruction** defines E0 as temperedness: each Schwinger function
is a continuous linear functional on Schwartz space.

    E0_tempered : ∀ n, Continuous (S n)

Analyticity appears later via Wick rotation machinery and the forward
tube domain, not as a standalone axiom on Schwinger functions.

**Discussion.** Analyticity of the generating functional is a
*consequence* of the regularity bound (OS1) plus the measure-theoretic
definition of Z. Stating it as a separate axiom (OS0) is redundant if
OS1 is strong enough, but convenient for direct use. The temperedness
condition (E0) is weaker and is what the original OS papers require at
the Schwinger function level.

## OS1 / E0' — Regularity

Three different formulations with increasing abstraction.

**OSforGFF** uses a concrete Lp bound (Glimm-Jaffe form): there exist
p ∈ [1,2] and c > 0 such that

    ‖Z[f]‖ ≤ exp(c · (∫ ‖f‖ + ∫ ‖f‖ᵖ))

with a two-point integrability condition when p = 2.

    def OS1_Regularity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
      ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
        (∀ (f : TestFunctionℂ),
          ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
            Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^p ∂volume))) ∧
        (p = 2 → TwoPointIntegrable dμ_config)

**QFTFramework** uses an abstract seminorm bound for OS1:

    def OS1_Regularity (Q : QFTData S T) : Prop :=
      ∃ (c : ℝ) (N : S.TestFunℂ → ℝ), c > 0 ∧
        ∀ (f : S.TestFunℂ), ‖Q.genFunℂ f‖ ≤ Real.exp (c * N f)

where N is an unspecified functional. This is the most general form,
accommodating different test function spaces (Schwartz, periodic,
lattice) where the specific norm may differ.

QFTFramework also defines OS1' as a separate condition on Schwinger
functions, following the OS II "linear growth condition":

    def OS1'_SchwingerGrowth (Q : QFTData S T) : Prop :=
      ∃ (α β : ℝ) (γ : ℝ) (p : S.TestFun → ℝ),
        α > 0 ∧ β > 0 ∧ 0 ≤ γ ∧
        (∀ (n : ℕ) (f : Fin n → S.TestFun),
          ‖schwingerFunction S Q n f‖ ≤
            α * β ^ n * (↑n.factorial : ℝ) ^ γ * ∏ i, p (f i))

This is not required by `OSTheory` (the base axiom bundle) but is
required by `OSReconstructible`, which extends `OSTheory` with OS1'
as an additional proof obligation. The separation reflects the fact
that OS0 + OS1 imply OS1' in principle (via Cauchy estimates on the
entire generating functional plus nuclearity of Schwartz space), but
the proof requires nuclear space infrastructure not yet in Mathlib.
For specific theories, OS1' can be verified directly:
- GFF: γ = 1/2 (Wick's theorem gives (n-1)!! ≤ n!^{1/2})
- P(Φ)₂: γ depends on polynomial degree (via hypercontractivity)

**OSreconstruction** uses the factorial growth condition from OS II
(the E0' condition needed for reconstruction), formulated as a separate
`OSLinearGrowthCondition` structure:

    structure OSLinearGrowthCondition (d : ℕ) [NeZero d]
        (OS : OsterwalderSchraderAxioms d) where
      sobolev_index : ℕ
      alpha : ℝ
      beta : ℝ
      gamma : ℝ
      alpha_pos : alpha > 0
      beta_pos : beta > 0
      growth_estimate : ∀ (n : ℕ) (f : SchwartzNPoint d n),
        ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
          SchwartzMap.seminorm ℝ sobolev_index sobolev_index f

This controls growth in n (number of field insertions), not just in the
test function. The factorial bound α · βⁿ · (n!)^γ · seminorm(f) is
the strongest condition — it is what is actually needed to reconstruct
Wightman functions via analytic continuation.

**Discussion.** The formulations reflect different goals. OSforGFF's
Lp bound is tuned to the GFF construction where the specific norm
matters. QFTFramework provides both OS1 (abstract generating functional
bound) and OS1' (Schwinger function growth), with OS1' separated into
`OSReconstructible` for theories targeting reconstruction.
OSreconstruction's factorial growth is necessary and sufficient for
reconstruction. For P(Φ)₂, the OSforGFF-style bound with p close to 1
is what one actually proves (via hypercontractivity).

The implication chain is: OS0 + OS1 (Lp bound) ⟹ OS1' (factorial
growth) ⟹ E0 (temperedness). The first implication uses Cauchy
estimates on the entire generating functional plus nuclearity; the
second is immediate.

## OS2 / E1 — Euclidean Invariance

**OSforGFF**: Invariance under the full Euclidean group E(d):

    def OS2_EuclideanInvariance (dμ_config : ...) : Prop :=
      ∀ (g : QFT.E) (f : TestFunctionℂ),
        GJGeneratingFunctionalℂ dμ_config f =
        GJGeneratingFunctionalℂ dμ_config (QFT.euclidean_action g f)

**QFTFramework**: Invariance under an abstract symmetry group:

    def OS2_Invariance (Q : QFTData S T) : Prop :=
      ∀ (g : S.SymGroup) (f : S.TestFunℂ),
        Q.genFunℂ f = Q.genFunℂ (S.symAction g f)

The `SymGroup` could be the Euclidean group E(d), the translation group,
the hypercubic group (for lattice spacetimes), etc.

**OSreconstruction**: Split into two separate conditions:

    E1_translation_invariant : ∀ (n : ℕ) (a : SpacetimeDim d) ...
      S n f = S n g    -- where g is the translate of f by a

    E1_rotation_invariant : ∀ (n : ℕ) (R : Matrix ...),
      R.transpose * R = 1 → R.det = 1 → ...
      S n f = S n g    -- where g is the rotation of f by R

Notably, OSreconstruction restricts to proper rotations (det R = 1),
i.e., SO(d+1) rather than O(d+1). Parity invariance is not assumed,
since it is not implied by the Wightman axioms in general.

## OS3 / E2 — Reflection Positivity

**OSforGFF and QFTFramework**: Formulated with finite linear combinations
of positive-time test functions and the generating functional:

    def OS3_ReflectionPositivity (Q : QFTData S T) : Prop :=
      ∀ (n : ℕ) (f : Fin n → S.positiveTimeSubmodule) (c : Fin n → ℝ),
        0 ≤ ∑ i, ∑ j, c i * c j *
          (Q.genFunR ((f i).val - S.timeReflection ((f j).val))).re

The matrix Mᵢⱼ = Re(Z[fᵢ - Θfⱼ]) must be positive semidefinite for
all choices of positive-time test functions fᵢ and real coefficients cᵢ.

**OSreconstruction**: Formulated with the Borchers algebra — sequences
of n-point test functions with the OS inner product:

    E2_reflection_positive : ∀ (F : BorchersSequence d),
      (∀ n, ∀ x : NPointDomain d n,
        (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion d n) →
      (OSInnerProduct d S F F).re ≥ 0

where OSInnerProduct uses `osConjTensorProduct` (time reflection +
complex conjugation on the left factor, then tensor product):

    def OSInnerProduct (S : SchwingerFunctions d)
        (F G : BorchersSequence d) : ℂ :=
      ∑ n ∈ Finset.range (F.bound + 1),
        ∑ m ∈ Finset.range (G.bound + 1),
          S (n + m) ((F.funcs n).osConjTensorProduct (G.funcs m))

**Discussion.** The Borchers algebra formulation is more general —
it tests positivity against all elements of the tensor algebra, not
just linear combinations of exponentials. The two formulations are
equivalent when the generating functional exists and determines all
Schwinger functions, but the Borchers version is the one needed for
reconstruction.

## E3 — Permutation Symmetry

Only OSreconstruction includes this axiom:

    E3_symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
      (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
      S n f = S n g

This states that Schwinger functions are symmetric under permutation
of their spacetime arguments. In the generating functional formalism
(OSforGFF / QFTFramework), this is automatic: Z[J] encodes all n-point
functions symmetrically. But for n-point Schwinger functions it must be
stated explicitly.

## OS4 / E4 — Clustering and Ergodicity

**OSforGFF** provides three variants:

1. *Clustering* (ε-δ): ∀ f g, ∀ ε > 0, ∃ R > 0 such that ‖a‖ > R ⟹
   |Z[f + τₐg] - Z[f]·Z[g]| < ε. Translates in all spacetime directions.

2. *Ergodicity* (L²): Time averages (1/T)∫₀ᵀ A(φ(t+·)) dt converge
   to E[A] in L²(μ) as T → ∞. Formulated for exponential observables.

3. *Polynomial clustering*: Explicit decay rate c·(1+s)^(-α) for
   time-separated correlators.

**QFTFramework**: Clustering uses `Filter.cocompact`:

    def OS4_Clustering (Q : QFTData S T) : Prop :=
      ∀ (f g : S.TestFun),
        Tendsto
          (fun a : S.TransVec =>
            Q.genFunR (f + S.translate a g)
            - Q.genFunR f * Q.genFunR g)
          (Filter.cocompact S.TransVec)
          (nhds 0)

This is elegant: on compact spaces (torus) the cocompact filter is ⊥,
so clustering holds vacuously. On ℝ^d it reduces to ‖a‖ → ∞.

Ergodicity uses the a.e. characterization:

    def OS4_Ergodicity (Q : QFTData S T) : Prop :=
      ∀ (A : S.FieldConfig → ℝ),
        Integrable A Q.measure.toMeasure →
        (∀ t : ℝ, ∀ᵐ ω ∂Q.measure.toMeasure,
          A (S.timeShift t ω) = A ω) →
        ∀ᵐ ω ∂Q.measure.toMeasure,
          A ω = ∫ ω', A ω' ∂Q.measure.toMeasure

Any time-shift-invariant integrable function equals its expectation a.e.

**OSreconstruction**: Clustering on Schwinger functions with spatial
translations only (a₀ = 0):

    E4_cluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n)
        (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 →
          (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ...
          ‖S (n + m) (f.tensorProduct g_a)
            - S n f * S m g‖ < ε

**Discussion.** OSreconstruction restricts to spatial translations
(`a 0 = 0`), which is physically correct: Euclidean time translations
correspond to imaginary Minkowski time and should not appear in the
clustering condition. The other projects translate in all spacetime
directions, which is stronger but non-standard. OSreconstruction also
formulates clustering on pairs of Schwinger functions (S_{n+m} factorizes),
while the others use the generating functional.

## Bundled Axiom Structures

**OSforGFF**: `SatisfiesAllOS` bundles OS0–OS4 (clustering + ergodicity)
as a `Prop` structure over a `ProbabilityMeasure FieldConfiguration`.

**QFTFramework**: Two levels of bundling:
- `OSTheory S T` extends `QFTData S T` with OS0–OS4 plus `hasRealAction`
  (weight = 1, needed because complex-action theories do not satisfy
  reflection positivity).
- `OSReconstructible S T` extends `OSTheory S T` with OS1' (Schwinger
  function factorial growth), providing everything needed for Wightman
  reconstruction.

**OSreconstruction**: `OsterwalderSchraderAxioms d` carries the Schwinger
functions themselves as data, plus E0–E4 as proof obligations. The
`OSLinearGrowthCondition` is a separate structure that extends the base
axioms.

## Summary

| Axiom | OSforGFF | QFTFramework | OSreconstruction |
|---|---|---|---|
| OS0/E0 | AnalyticOn ℂ (entire) | AnalyticOn ℂ (entire) | Continuous (tempered) |
| OS1/E0' | Lp bound, p ∈ [1,2] | Abstract exp(c·N(f)) | Factorial growth α·βⁿ·(n!)^γ |
| OS1' | (not separate) | Schwinger growth (in OSReconstructible) | (= E0', in OSLinearGrowthCondition) |
| OS2/E1 | E(d) invariance | Abstract SymGroup | SO(d+1) + translations (split) |
| OS3/E2 | Finite sums, gen. functional | Finite sums, gen. functional | Borchers algebra |
| E3 | (automatic) | (automatic) | Permutation symmetry |
| OS4/E4 | ε-δ all directions + L² ergodicity | cocompact filter + a.e. ergodicity | Spatial-only ε-δ |
| Bundle | SatisfiesAllOS (Prop) | OSTheory / OSReconstructible | OsterwalderSchraderAxioms (data) |
