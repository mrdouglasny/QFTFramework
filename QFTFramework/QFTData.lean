/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import QFTFramework.SpacetimeData
import QFTFramework.TheoryData

/-!
# QFTData — A QFT = Spacetime + Theory → Measure

A quantum field theory combines spacetime geometry (`SpacetimeData`) with
theory specification (`TheoryData`) to produce a probability measure on
field configurations and a generating functional.

## Complex Actions

The generating functional can come from:

1. **Real action (Euclidean QFT):** The measure dμ = e^{-S_E[φ]} Dφ is a
   genuine probability measure. OS axioms apply directly.

2. **Complex action:** When S = S_R + iS_I (theta terms, Chern-Simons,
   finite-density QCD), the "measure" is not positive. We use **reweighting**:
   define a real base measure dμ₀ = e^{-S_R} Dφ and a complex weight
   w(φ) = e^{-iS_I[φ]}, so expectations become
   ⟨O⟩ = (∫ O · w dμ₀) / (∫ w dμ₀).

Design:
- `QFTData` always has a real `ProbabilityMeasure` (the base measure).
- An optional `weight : FieldConfig → ℂ` handles complex actions.
- For real-action theories, `weight = 1` identically.
- OS axioms require `hasRealAction` (weight = 1).

## References

* aqft2/docs/multidim_plan.md
-/

open MeasureTheory Complex
open scoped BigOperators

/-- A quantum field theory: combines spacetime geometry with theory specification
to produce a probability measure and generating functional. -/
structure QFTData (S : SpacetimeData) (T : TheoryData) where
  /-- Probability measure on field configurations -/
  measure : ProbabilityMeasure S.FieldConfig
  /-- Complex weight function for reweighting.
      For real-action theories: weight ω = 1.
      For complex-action theories: weight ω = exp(-i S_I[ω]). -/
  weight : S.FieldConfig → ℂ
  /-- Weight function is integrable -/
  weight_integrable : Integrable weight measure.toMeasure
  /-- The complex generating functional Z[J] -/
  genFunℂ : S.TestFunℂ → ℂ

namespace QFTData

variable {S : SpacetimeData} {T : TheoryData}

/-- A QFT has a real action when weight = 1 everywhere.
This is required for OS axioms (reflection positivity needs a positive measure). -/
def hasRealAction (Q : QFTData S T) : Prop :=
  ∀ ω, Q.weight ω = 1

/-- The real generating functional (characteristic functional of the base measure).
Z[f] = ∫ w(ω) exp(i⟨ω, f⟩) dμ(ω) -/
noncomputable def genFunR (Q : QFTData S T) (f : S.TestFun) : ℂ :=
  ∫ ω, Q.weight ω * exp (I * (S.eval ω f : ℂ)) ∂Q.measure.toMeasure

end QFTData
