/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# SpacetimeData — Geometric Data for QFT

This file defines `SpacetimeData`, a structure packaging the geometric,
topological, and symmetry data of a spacetime on which quantum field theories
can be formulated. This is independent of any particular theory (Lagrangian,
CFT data, etc.).

## Design

The key separation principle: `SpacetimeData` captures *where* a QFT lives
(geometry, test functions, distributions, symmetries), while `TheoryData`
captures *what* the QFT is (field content, couplings). The two combine
in `QFTData` to produce a measure and generating functional.

## Supported spacetime types

1. **Flat Euclidean** ℝ^d — Schwartz test functions, Euclidean group
2. **Cylinder** ℝ × T^{d-1}_L — for P(Φ)₂ on ℝ × S¹
3. **Lattice** aℤ^d — discrete lattice with spacing a > 0
4. **Minkowski** ℝ^{1,d} — for Wightman QFT (future)

## References

* Glimm and Jaffe, *Quantum Physics*, Ch. 6
* Osterwalder and Schrader, *Axioms for Euclidean Green's functions*
* aqft2/docs/multidim_plan.md — detailed design rationale
-/

open MeasureTheory Complex
open scoped BigOperators

/-- Data package for a spacetime on which OS axioms can be stated.

This bundles the geometric, topological, and symmetry data needed to
formulate OS0–OS4 without fixing a particular spacetime manifold.

The fields are organized into:
- **Test function spaces**: where smeared fields live
- **Distribution space**: where field configurations live
- **Symmetry group**: Euclidean, translation, hypercubic, etc.
- **Translation subgroup**: for clustering/ergodicity
- **Time structure**: reflection, positive time, time translations -/
structure SpacetimeData where
  -- Test function spaces
  /-- Real-valued test functions (Schwartz on ℝ^d, smooth periodic on torus, etc.) -/
  TestFun : Type
  /-- Complex-valued test functions -/
  TestFunℂ : Type
  [instACG_TF : AddCommGroup TestFun]
  [instMod_TF : Module ℝ TestFun]
  [instTS_TF : TopologicalSpace TestFun]
  [instACG_TFℂ : AddCommGroup TestFunℂ]
  [instMod_TFℂ : Module ℂ TestFunℂ]
  [instTS_TFℂ : TopologicalSpace TestFunℂ]
  /-- Embedding of real test functions into complex ones -/
  toComplex : TestFun →L[ℝ] TestFunℂ

  -- Distribution space (field configurations)
  /-- Field configurations: tempered distributions, lattice fields, etc. -/
  FieldConfig : Type
  [instMS_FC : MeasurableSpace FieldConfig]
  [instTS_FC : TopologicalSpace FieldConfig]
  /-- Distribution pairing ⟨ω, f⟩ -/
  eval : FieldConfig → TestFun → ℝ
  /-- Each evaluation map ω ↦ ⟨ω, f⟩ is measurable -/
  eval_measurable : ∀ f, Measurable (fun ω => eval ω f)

  -- Symmetry group (Euclidean group for ℝ^d, translations for torus, etc.)
  /-- The full symmetry group -/
  SymGroup : Type
  [instGrp_SG : Group SymGroup]
  /-- Action of the symmetry group on complex test functions -/
  symAction : SymGroup → TestFunℂ → TestFunℂ

  -- Translation subgroup with metric structure
  -- For ℝ^d: the translation part of E(d) ≅ ℝ^d
  -- For torus: translations in ℝ/Lℤ × ... (compact directions)
  -- OS4 clustering uses Filter.cocompact on TransVec
  /-- Translation vectors (subgroup of symmetry group) -/
  TransVec : Type
  [instNACG_TV : NormedAddCommGroup TransVec]
  /-- Embedding translations into the full symmetry group -/
  translateEmbed : TransVec → SymGroup

  -- Time structure for OS axioms
  /-- Time reflection operator on real test functions: (t, x⃗) ↦ (-t, x⃗) -/
  timeReflection : TestFun →L[ℝ] TestFun
  /-- Submodule of real test functions supported at positive time -/
  positiveTimeSubmodule : Submodule ℝ TestFun
  /-- Time translation acting on field configurations (for ergodicity) -/
  timeShift : ℝ → FieldConfig → FieldConfig

namespace SpacetimeData

-- Make instances available when working with a spacetime
attribute [instance] instACG_TF instMod_TF instTS_TF instACG_TFℂ instMod_TFℂ instTS_TFℂ
attribute [instance] instMS_FC instTS_FC instGrp_SG instNACG_TV

/-- Positive-time test function type (subtype of the submodule) -/
abbrev PositiveTimeFun (S : SpacetimeData) := S.positiveTimeSubmodule

/-- Translate a complex test function by a translation vector. -/
noncomputable def translateTestFunℂ (S : SpacetimeData) (a : S.TransVec)
    (f : S.TestFunℂ) : S.TestFunℂ :=
  S.symAction (S.translateEmbed a) f

end SpacetimeData
