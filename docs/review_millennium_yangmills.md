# Review: LeanMillenniumPrizeProblems Yang-Mills Formalization

Repository: [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
Files: `Problems/YangMills/Quantum.lean`, `Problems/YangMills/Millennium.lean`

## Overview

This formalization states the Clay Millennium Prize problem "Yang-Mills
Existence and Mass Gap" in Lean 4. It defines Wightman axioms for QFT,
bundles them into a `QuantumYangMillsTheory` structure parameterized by a
compact simple gauge group G, and asks for existence of such a theory with
a spectral mass gap.

The final problem statement is:

    def YangMillsExistenceAndMassGap (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
      ∃ (qft : QuantumYangMillsTheory G) (Δ : ℝ),
        ClayExistence qft ∧ HasMassGapSpectrum G qft Δ ∧ FiniteMassSpectrum G qft

## Positive Aspects

### Clean Wightman Axiom Formulation

The `WightmanAxioms` class states all five axioms clearly:

- **W1 (Poincare covariance)**: Abstract `poincare_group` with unitary
  representation, action on test functions, and covariance condition
  `Φ(g·f) = U(g) Φ(f) U(g)⁻¹`.

- **W2 (Spectral condition)**: Self-adjoint positive Hamiltonian with
  nonnegative spectrum and spatial translation representation.

- **W3 (Vacuum)**: Unique ground state annihilated by Hamiltonian,
  invariant under Poincare group and spatial translations.

- **W4 (Cyclicity)**: `Dense (fieldGeneratedSubmodule Φ vacuum)` — the
  vacuum is cyclic for the field algebra.

- **W5 (Locality)**: Field operators commute at spacelike separation,
  using the Minkowski metric to define the causal structure.

This is a reasonable encoding of the standard Wightman axioms from
Streater-Wightman. The use of `SchwartzMap Spacetime ℝ` for test functions
and `H →L[ℝ] H` for bounded operators is appropriate.

### Good Use of Lean Idioms

- Typeclass instances for `CompactSimpleGaugeGroup` bundle the required
  algebraic and topological structure cleanly.
- The `conjugateOperator` function for `U A U⁻¹` correctly uses
  `LinearIsometryEquiv` for unitary operators.
- `fieldGeneratedSubmodule` uses `Submodule.span` appropriately.
- Attribute instances propagate Hilbert space structure through the
  `QuantumYangMillsTheory` bundle.

### Additional Physical Structure

Beyond the bare Wightman axioms, the formalization includes:

- **Stress-energy tensor** with symmetry and conservation law.
- **Operator product expansion** data with finite support.
- **Clustering property** with exponential decay of correlations.
- **Mass gap** in both quadratic form and spectral versions.
- **Two equivalent mass gap definitions** (`HasMassGap` via quadratic
  forms, `HasMassGapSpectrum` via spectral disjointness), though the
  equivalence is not proved.

### Syntactic Gauge-Invariant Polynomials

The inductive type `GaugeInvariantLocalPolynomial` is a creative approach
to representing the space of local gauge-invariant operators without
formalizing the full differential geometry of gauge bundles:

    inductive GaugeInvariantLocalPolynomial (G : Type) : Type
      | curvature | covDeriv | add | mul | trace | ...

This sidesteps the need for principal bundles, connections, and curvature
tensors, which would require substantial differential geometry infrastructure.

## Negative Aspects

### The Theory Is Not Constrained to Be Yang-Mills

This is the most serious issue. The formalization asks for existence of a
`QuantumYangMillsTheory G` but does not adequately constrain the theory to
actually be a Yang-Mills theory. Several components that should enforce this
are left unspecified:

**1. `ShortDistanceAgreement` has unconstrained predictions.**
The Clay writeup requires the theory to agree with Yang-Mills perturbation
theory at short distances. In the formalization:

    structure ShortDistanceAgreement ... where
      scale : ℝ → SchwartzSpace → SchwartzSpace
      prediction : ℝ → List SchwartzSpace → ℝ
      agrees : ...

The `prediction` function is existentially quantified with no constraint
that it equals the actual perturbative Yang-Mills predictions. Any theory
trivially satisfies this by choosing `prediction` to match its own
short-distance behavior.

**2. `GaugeInvariantLocalPolynomial` is purely syntactic.**
The inductive type has constructors like `curvature` and `covDeriv`, but
these are just labels. There is no condition that the operator assigned to
`curvature` actually behaves like a field strength tensor, satisfies
Bianchi identities, or has the correct engineering dimension.

**3. `LocalOperatorAssignment` only requires injectivity.**
The condition `Function.Injective op` ensures distinct syntactic polynomials
map to distinct operators, but says nothing about whether these operators
have the algebraic or analytic properties expected of gauge-invariant
local operators in a Yang-Mills theory.

**Consequence**: A massive free scalar field theory could potentially
satisfy this formalization (modulo the gauge group constraint). Concretely:
take any compact simple G (e.g., SU(2)), define `localOperators` to
injectively assign free-field operators to the syntactic polynomial labels,
set `prediction` to match the free field's short-distance behavior, and
provide trivial stress-energy and OPE data. The only genuine obstruction
is that `CompactSimpleGaugeGroup` requires `non_abelian`, which prevents
using the trivial group — but this is a constraint on G, not on the
dynamics of the theory.

### Poincare Group Is Abstract

The `poincare_group` in `WightmanAxioms` is an abstract type with a
`Group` instance:

    poincare_group : Type
    [poincare_structure : Group poincare_group]

There is no condition that this is actually the Poincare group
ISO(3,1) = SO⁺(3,1) ⋉ ℝ⁴. It could be any group. Similarly,
`action_on_tests` could be any group action, not necessarily the
geometric action of Poincare transformations on Schwartz functions.

In the standard Wightman axioms, the Poincare group is a specific
Lie group with specific generators (translations, rotations, boosts)
and its representation carries specific physical meaning (energy-momentum,
angular momentum). Abstracting this away loses the connection to
relativistic spacetime geometry.

### Hilbert Space Is Real, Not Complex

The formalization uses `InnerProductSpace ℝ H` throughout. Standard
quantum field theory requires a complex Hilbert space with
`InnerProductSpace ℂ H`. This affects:

- The inner product `⟨ψ, φ⟩` should be sesquilinear (conjugate-linear
  in one argument), not bilinear.
- Unitary operators should be complex-linear isometries.
- The spectrum of the Hamiltonian is defined via `spectrum ℝ`, but
  self-adjointness and the spectral theorem require the complex setting.

This is likely a pragmatic choice (Mathlib's complex inner product space
infrastructure may have been less developed), but it is a mathematical
inaccuracy.

### No Vacuum Uniqueness

Wightman axiom W3 typically requires the vacuum to be the *unique*
(up to phase) Poincare-invariant state. The formalization states:

    vacuum_invariant : ∀ g, unitary_rep g vacuum = vacuum

but does not assert uniqueness. Without uniqueness, the theory could
have multiple vacua, which changes the physical content significantly
(in particular, the mass gap statement becomes ambiguous).

### Spacetime Is Fixed to d=4

`Spacetime` is hard-coded as `EuclideanSpace ℝ (Fin 4)`. This is
appropriate for the Clay problem (which specifically asks about 4D),
but makes the Wightman axiom formulation non-reusable for other
dimensions. A parametric `d` would allow the same axioms to be used
for d=2 (where solutions exist) or d=3.

### No Connection Between Mass Gap Definitions

Two mass gap definitions are given:

    def HasMassGap ... : Prop :=          -- quadratic form version
    def HasMassGapSpectrum ... : Prop :=   -- spectral version

The equivalence of these (which follows from the spectral theorem for
self-adjoint operators) is not proved. The problem statement uses
`HasMassGapSpectrum` but `ClusteringProperty` is stated separately
without connecting it to either mass gap definition.

### `MassGapImpliesClustering` Is Stated but Not Used

The proposition `MassGapImpliesClustering` is defined but is not
required in `YangMillsExistenceAndMassGap`. The Clay writeup discusses
clustering as a consequence of the mass gap, but in the formalization
it is just a free-standing definition.

## Comparison with OSreconstruction

The [OSreconstruction](https://github.com/mdouglas/OSreconstruction) project
provides an independent Lean 4 formalization of Wightman axioms, with
substantially more mathematical infrastructure. A detailed comparison
highlights the strengths and weaknesses of the Millennium formalization.

### Spacetime and Geometry

| | LeanMillenniumPrizeProblems | OSreconstruction |
|---|---|---|
| Spacetime | `EuclideanSpace ℝ (Fin 4)` (fixed d=4) | `MinkowskiSpace d = Fin (d+1) → ℝ` (parametric) |
| Metric | `MinkowskiMetric` as a function (+,-,-,-) | `minkowskiInner` via metric matrix η, with full causal structure |
| Causal structure | Spacelike separation via `MinkowskiMetric(x-y)(x-y) < 0` | `IsTimelike`, `IsSpacelike`, `IsLightlike`, `IsCausal`, light cones |
| Signature | (+,-,-,-) | (-,+,+,...,+) (mostly positive, particle physics) |

OSreconstruction has a complete Minkowski geometry with forward/backward
light cones, causal classification, and the metric as a matrix with
proved algebraic properties (η² = I, det η = -1). The Millennium
formalization has only the bare metric function.

### Symmetry Groups

| | LeanMillenniumPrizeProblems | OSreconstruction |
|---|---|---|
| Poincare group | Abstract type with `Group` instance | `PoincareGroup d` = semidirect product of `LorentzGroup d` and translations |
| Lorentz group | Not defined | `LorentzGroup d` = matrices preserving η, with det = ±1, \|Λ₀₀\| ≥ 1 |
| Restricted subgroup | Not defined | `Restricted` = proper orthochronous SO⁺(1,d) |
| Group action | Abstract `action_on_tests` | Geometric: g·x = Λx + a on Minkowski space |

This is one of the most significant differences. OSreconstruction defines
the actual Poincare group as the semidirect product ISO(1,d) with concrete
matrix Lorentz transformations, proves closure under multiplication of
orthochronous elements (using a Cauchy-Schwarz / hyperbolic bound argument),
and defines parity and time reversal as specific matrices. The Millennium
formalization leaves the Poincare group completely abstract.

### Hilbert Space and Operators

| | LeanMillenniumPrizeProblems | OSreconstruction |
|---|---|---|
| Scalar field | `InnerProductSpace ℝ H` | `InnerProductSpace ℂ H` |
| Operators | `H →L[ℂ] H` (bounded) | Unbounded: `operator : S → (H → H)` with dense domain |
| Domain | Not specified | `DenseSubspace H` with explicit domain invariance |
| Matrix elements | Not defined | `matrixElement`: f ↦ ⟨χ, φ(f)ψ⟩ with continuity |
| Poincare rep | `H ≃ₗᵢ[ℝ] H` (real isometry) | `PoincareRepresentation d H` with `U : PoincareGroup d → (H →L[ℂ] H)` |

OSreconstruction correctly uses a complex Hilbert space and models quantum
fields as unbounded operator-valued distributions with an explicit dense
invariant domain — this matches the mathematical physics literature
(Streater-Wightman). The Millennium formalization uses bounded operators
on a real Hilbert space, which is simpler but mathematically incorrect
for QFT (quantum fields are typically unbounded).

### Wightman Axioms

Both formalize W1-W5, but with different levels of detail:

**W1 (Covariance)**: The Millennium version uses abstract group action on
test functions. OSreconstruction defines `IsCovariantWeak` via matrix
elements: ⟨U(g)χ, φ(f)U(g)ψ⟩ = ⟨χ, φ(g·f)ψ⟩, which is the correct
weak formulation for unbounded operators.

**W2 (Spectral condition)**: The Millennium version requires a positive
self-adjoint Hamiltonian with nonneg spectrum. OSreconstruction defines
`SpectralCondition` with both energy non-negativity and a mass-shell
condition ⟨ψ, H²ψ⟩ ≥ Σᵢ ⟨ψ, Pᵢ²ψ⟩, encoding the full forward light
cone condition on the energy-momentum spectrum.

**W3 (Vacuum)**: The Millennium version has Poincare invariance but no
uniqueness. OSreconstruction has `VacuumUnique` requiring all
time-translation-invariant vectors to be proportional to Ω.

**W5 (Locality)**: Both require spacelike commutativity. OSreconstruction's
`IsLocal` specifies the commutator condition on the dense domain D, which
is the correct formulation for unbounded operators.

### Additional Infrastructure

OSreconstruction includes substantial infrastructure absent from the
Millennium formalization:

- **Wightman functions**: n-point functions W_n(f₁,...,fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩
  with Hermiticity, positivity, and translation invariance properties
- **Analytic continuation**: Forward tube, extended forward tube, and
  holomorphicity of Wightman functions (the Bargmann-Hall-Wightman theorem
  framework)
- **Reconstruction theorem**: Statement that Wightman functions satisfying
  temperedness, covariance, spectrum condition, locality, and positive
  definiteness uniquely determine a `WightmanQFT`
- **Nuclear spaces**: `NuclearSpace` typeclass, proof that Schwartz space
  is nuclear (Dynin-Mityagin characterization)
- **Schwartz tensor products**: Full tensor product algebra for multi-point
  test functions with Borchers conjugation
- **Momentum operators**: Hamiltonian H = P₀ and spatial momentum as
  generators of the translation group via Stone's theorem

### Assessment

The Millennium formalization prioritizes stating the problem cleanly
in ~400 lines. OSreconstruction prioritizes mathematical correctness
and completeness in ~10,000+ lines across 69 files. For the specific
purpose of stating the Clay problem, the Millennium approach is adequate
(modulo the issues noted above). For actually *proving* anything about
Wightman QFT — reconstruction theorems, analytic continuation, spectral
theory — OSreconstruction's infrastructure is necessary.

The key mathematical accuracy improvements in OSreconstruction are:
complex Hilbert spaces, unbounded operators with dense domains, concrete
Poincare group as a semidirect product, vacuum uniqueness, and the full
forward light cone spectral condition. These are not cosmetic differences
— they affect whether theorems can be correctly stated and proved.

## Summary

The formalization is a reasonable first attempt at stating the Yang-Mills
Millennium Prize problem in Lean 4. The Wightman axioms are cleanly
encoded and the mass gap is stated in two natural forms.

The main weakness is that the formalization does not actually constrain
the theory to be a gauge theory. The Wightman axioms govern gauge-invariant
observables, so gauge symmetry is not visible at the level of the physical
Hilbert space and field operators — it is a property of the *construction*,
not of the resulting axiomatic QFT. The `CompactSimpleGaugeGroup G`
parameter labels the theory but imposes no dynamical constraint.

More precisely, the Millennium problem asks for *pure* Yang-Mills theory:
a gauge field with no coupled matter (no quarks, no scalars, no other
fields). Pure YM with compact simple gauge group G is the unique
renormalizable 4d gauge theory with that gauge group and no matter content.
Yang-Mills coupled to matter (quarks, Higgs, etc.) forms a much larger
class — indeed, the Standard Model is a Yang-Mills theory coupled to
matter, and this is the only known class of physically relevant 4d QFTs.
The formalization does not distinguish pure YM from YM-plus-matter;
there is no constraint on the field content or on the absence of matter
representations of G.

The `ShortDistanceAgreement` structure was intended to fill this role
(requiring agreement with perturbative Yang-Mills predictions at short
distances), but the `prediction` function is left unconstrained. Similarly,
`GaugeInvariantLocalPolynomial` provides syntactic labels (`curvature`,
`covDeriv`, `trace`) without semantic content — the operator assigned to
`curvature` need not have any relation to a field strength tensor.

There are two ways to show a constructed theory is pure Yang-Mills:

1. **Test short-distance behavior**: Compute gauge-invariant correlation
   functions (e.g., Wilson loops, correlators of Tr F²) and verify they
   match the detailed predictions of perturbative pure YM at short
   distances — specific anomalous dimensions, OPE coefficients, and
   beta function. This requires formalizing perturbative renormalization
   of Yang-Mills theory to pin down what `ShortDistanceAgreement` should
   actually check.

2. **Work with a matching construction**: Build the theory via a
   construction that clearly corresponds to perturbative pure YM — e.g.,
   a lattice gauge theory with the Wilson action for gauge group G and
   no matter fields, or a continuum construction starting from the
   classical YM action on a principal G-bundle. The construction itself
   encodes the field content and dynamics; the Wightman axioms are then
   *consequences* to be verified, not the defining property.

Either approach is a substantial project. The Millennium formalization
takes neither route, leaving the connection to pure YM purely semantic.

The comparison with OSreconstruction shows that substantially more
infrastructure is needed for a mathematically rigorous Wightman framework:
complex Hilbert spaces, unbounded operator-valued distributions, concrete
Poincare group geometry, and analytic continuation machinery.
