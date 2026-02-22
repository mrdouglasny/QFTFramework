/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import QFTFramework.QFTData
import Mathlib.Analysis.Analytic.Basic

/-!
# Osterwalder-Schrader Axioms — Generic Formulation

This file defines the Osterwalder-Schrader axioms (OS0–OS4) parametrized over
`SpacetimeData` and `QFTData`, so that the same axiom definitions apply to
flat ℝ^d, cylinder ℝ × T^{d-1}_L, lattice aℤ^d, and any future spacetime.

## Main Definitions

* `OS0_Analyticity` — Analyticity of the generating functional
* `OS1_Regularity` — Exponential regularity bound
* `OS1'_SchwingerGrowth` — Factorial growth bound on Schwinger functions
* `OS2_Invariance` — Symmetry group invariance
* `OS3_ReflectionPositivity` — Reflection positivity
* `OS4_Clustering` — Clustering (correlation decay)
* `OS4_Ergodicity` — Ergodicity (time-average convergence)
* `OSTheory` — Bundle of all axioms, extending `QFTData`
* `OSReconstructible` — Extends `OSTheory` with Schwinger growth for reconstruction

## References

* Osterwalder–Schrader, *Axioms for Euclidean Green's functions* I & II
* Glimm–Jaffe, *Quantum Physics*, Ch. 6, 19
-/

open MeasureTheory Complex Filter
open scoped BigOperators

noncomputable section

variable (S : SpacetimeData) {T : TheoryData}

/-! ## OS-0: Analyticity -/

/-- OS0 (Analyticity): The complex generating functional is analytic in the
test function coefficients.

For any finite collection of complex test functions J₁, …, Jₙ, the map
(z₁, …, zₙ) ↦ Z_ℂ[∑ᵢ zᵢ Jᵢ] is analytic on ℂⁿ. -/
def OS0_Analyticity (Q : QFTData S T) : Prop :=
  ∀ (n : ℕ) (J : Fin n → S.TestFunℂ),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      Q.genFunℂ (∑ i, z i • J i)) Set.univ

/-! ## OS-1: Regularity -/

/-- OS1 (Regularity): The complex generating functional satisfies an
exponential bound controlled by a seminorm-like functional N. -/
def OS1_Regularity (Q : QFTData S T) : Prop :=
  ∃ (c : ℝ) (N : S.TestFunℂ → ℝ), c > 0 ∧
    ∀ (f : S.TestFunℂ), ‖Q.genFunℂ f‖ ≤ Real.exp (c * N f)

/-! ## OS-1': Schwinger Function Growth (Linear Growth Condition)

The "linear growth condition" of Osterwalder-Schrader II. This bounds
the n-point Schwinger functions S_n with factorial growth in n and
linear dependence on a seminorm of the test function. This condition is
needed for the Wightman reconstruction theorem.

For theories constructed via a measure (GFF, P(Φ)₂), OS1' follows
from OS0 + OS1 via Cauchy estimates on the entire generating functional,
plus nuclearity of the test function space. However the proof requires
nuclear space infrastructure, so we state it as a separate condition. -/

/-- Schwinger functions S_n: the n-point correlation functions.
S_n(f₁, …, fₙ) = ∫ ⟨ω, f₁⟩ ⋯ ⟨ω, fₙ⟩ dμ(ω). -/
noncomputable def schwingerFunction (Q : QFTData S T) (n : ℕ)
    (f : Fin n → S.TestFun) : ℝ :=
  ∫ ω, ∏ i, S.eval ω (f i) ∂Q.measure.toMeasure

/-- OS1' (Schwinger Function Growth): The n-point Schwinger functions
satisfy a factorial growth bound.

There exist constants α > 0, β > 0, γ ≥ 0 and a seminorm p on
test functions such that for all n and all test functions fᵢ:

  |S_n(f₁, …, fₙ)| ≤ α · βⁿ · (n!)^γ · ∏ᵢ p(fᵢ)

This is the "linear growth condition" of OS II — "linear" refers to
the dependence on each fᵢ being through a single seminorm (linear in f),
while the growth in n is controlled by the factorial bound.

For the GFF: γ = 1/2 suffices (Wick's theorem gives (n-1)!! ≤ n!^{1/2}).
For P(Φ)₂: γ depends on the polynomial degree (via hypercontractivity). -/
def OS1'_SchwingerGrowth (Q : QFTData S T) : Prop :=
  ∃ (α β : ℝ) (γ : ℝ) (p : S.TestFun → ℝ),
    α > 0 ∧ β > 0 ∧ 0 ≤ γ ∧
    (∀ (n : ℕ) (f : Fin n → S.TestFun),
      ‖schwingerFunction S Q n f‖ ≤
        α * β ^ n * (↑n.factorial : ℝ) ^ γ * ∏ i, p (f i))

/-! ## OS-2: Symmetry Invariance -/

/-- OS2 (Symmetry Invariance): The generating functional is invariant under
the symmetry group of the spacetime.

Z_ℂ[f] = Z_ℂ[g · f] for all g in the symmetry group. -/
def OS2_Invariance (Q : QFTData S T) : Prop :=
  ∀ (g : S.SymGroup) (f : S.TestFunℂ),
    Q.genFunℂ f = Q.genFunℂ (S.symAction g f)

/-! ## OS-3: Reflection Positivity -/

/-- OS3 (Reflection Positivity): For any finite collection of positive-time
test functions fᵢ and real coefficients cᵢ, the reflection matrix is
positive semidefinite:

∑ᵢ ∑ⱼ cᵢ cⱼ Re(Z[fᵢ - Θ fⱼ]) ≥ 0

where Θ is the time reflection operator. -/
def OS3_ReflectionPositivity (Q : QFTData S T) : Prop :=
  ∀ (n : ℕ) (f : Fin n → S.positiveTimeSubmodule) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (Q.genFunR ((f i).val - S.timeReflection ((f j).val))).re

/-! ## OS-4: Clustering and Ergodicity -/

/-- OS4 Clustering: Correlations between spatially separated regions decay.

For all real test functions f, g:
  Z[f + τ_a(g)] → Z[f] · Z[g] as ‖a‖ → ∞

where τ_a translates test functions by the translation vector a.

Uses `Filter.cocompact` on `TransVec`:
- ℝ^d: ‖a‖ → ∞ (nontrivial clustering)
- T^d: vacuously true (compact, cocompact = ⊥)
- ℝ^k × T^{d-k}: only ℝ^k directions matter -/
def OS4_Clustering (Q : QFTData S T) : Prop :=
  ∀ (f g : S.TestFun),
    Tendsto
      (fun a : S.TransVec =>
        Q.genFunR (f + S.translate a g)
        - Q.genFunR f * Q.genFunR g)
      (Filter.cocompact S.TransVec)
      (nhds 0)

/-- OS4 Ergodicity: The time translation group acts ergodically on (FieldConfig, μ).

Any time-shift-invariant integrable function is a.e. equal to its expectation.
This is equivalent to uniqueness of the vacuum state. -/
def OS4_Ergodicity (Q : QFTData S T) : Prop :=
  ∀ (A : S.FieldConfig → ℝ),
    Integrable A Q.measure.toMeasure →
    (∀ t : ℝ, ∀ᵐ ω ∂Q.measure.toMeasure,
      A (S.timeShift t ω) = A ω) →
    ∀ᵐ ω ∂Q.measure.toMeasure,
      A ω = ∫ ω', A ω' ∂Q.measure.toMeasure

/-! ## Bundled Axiom Structures -/

/-- A quantum field theory satisfying all Osterwalder-Schrader axioms.

Extends `QFTData` with OS0–OS4 as proof obligations.
Requires `hasRealAction` (weight = 1), since reflection positivity
needs a genuine positive measure. -/
structure OSTheory (S : SpacetimeData) (T : TheoryData)
    extends QFTData S T where
  /-- The OS axioms require weight = 1 (real action) -/
  real_action : toQFTData.hasRealAction
  /-- OS0: Analyticity -/
  os0 : OS0_Analyticity S toQFTData
  /-- OS1: Regularity -/
  os1 : OS1_Regularity S toQFTData
  /-- OS2: Symmetry invariance -/
  os2 : OS2_Invariance S toQFTData
  /-- OS3: Reflection positivity -/
  os3 : OS3_ReflectionPositivity S toQFTData
  /-- OS4: Clustering -/
  os4_clustering : OS4_Clustering S toQFTData
  /-- OS4: Ergodicity -/
  os4_ergodicity : OS4_Ergodicity S toQFTData

/-- An OS theory with the additional Schwinger function growth bound
needed for the Wightman reconstruction theorem.

OS0 + OS1 imply OS1' (via Cauchy estimates + nuclearity of the test
function space), but the proof requires nuclear space infrastructure.
For now we state OS1' as a separate condition.

For specific theories, OS1' is verified directly:
- GFF: Wick's theorem gives γ = 1/2
- P(Φ)₂: hypercontractivity gives finite γ depending on the degree -/
structure OSReconstructible (S : SpacetimeData) (T : TheoryData)
    extends OSTheory S T where
  /-- OS1': Schwinger function factorial growth bound -/
  os1' : OS1'_SchwingerGrowth S toOSTheory.toQFTData

end
