/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Cylinder/Torus Spacetime ℝ × T^{d-1}_L

The cylinder spacetime ℝ × T^{d-1}_L, where T_L = AddCircle L is the
torus of period L. This is the natural spacetime for P(Φ)₂ on ℝ × S¹_L
and more general theories on partially compactified spaces.

## Design Notes

- Time is continuous (ℝ), spatial coordinates are periodic (AddCircle L)
- Test functions are axiomatized: Schwartz-type function spaces on torus
  domains are not available in Mathlib. In pphi2, these are given concretely
  via Fourier mode decomposition.
- The metric is the product of the standard ℝ metric and the torus metric.
-/

open MeasureTheory

noncomputable section

/-- Cylinder spacetime: ℝ (time) × T^{d-1}_L (spatial torus).
For d = 2, L > 0, this gives ℝ × S¹_L, the spacetime for P(Φ)₂. -/
abbrev SpaceTimeTorus (d : ℕ) (L : ℝ) := ℝ × (Fin (d - 1) → AddCircle L)

/-- Extract the time component from a torus spacetime point. -/
def getTimeComponentTorus {d : ℕ} {L : ℝ} (x : SpaceTimeTorus d L) : ℝ := x.1

instance {d : ℕ} {L : ℝ} : Inhabited (SpaceTimeTorus d L) :=
  ⟨(0, fun _ => 0)⟩

/-! ## Axiomatized function spaces

SchwartzMap does not support torus domains in Mathlib. We axiomatize the
test function and field configuration spaces, along with their required
algebraic and topological structure. -/

/-- Test functions on the cylinder: smooth on the torus,
Schwartz-class decay in the time direction. -/
axiom TestFunctionTorus (d : ℕ) (L : ℝ) : Type

/-- Complex-valued test functions on the cylinder. -/
axiom TestFunctionTorusℂ (d : ℕ) (L : ℝ) : Type

/-- Field configurations (distributions) on the cylinder. -/
axiom FieldConfigurationTorus (d : ℕ) (L : ℝ) : Type

-- Algebraic instances (axiomatized)
@[instance] axiom instAddCommGroupTestFunctionTorus (d : ℕ) (L : ℝ) :
  AddCommGroup (TestFunctionTorus d L)
@[instance] axiom instModuleTestFunctionTorus (d : ℕ) (L : ℝ) :
  Module ℝ (TestFunctionTorus d L)
@[instance] axiom instTopologicalSpaceTestFunctionTorus (d : ℕ) (L : ℝ) :
  TopologicalSpace (TestFunctionTorus d L)

@[instance] axiom instAddCommGroupTestFunctionTorusℂ (d : ℕ) (L : ℝ) :
  AddCommGroup (TestFunctionTorusℂ d L)
@[instance] axiom instModuleTestFunctionTorusℂ (d : ℕ) (L : ℝ) :
  Module ℂ (TestFunctionTorusℂ d L)

@[instance] axiom instMeasurableSpaceFieldConfigurationTorus (d : ℕ) (L : ℝ) :
  MeasurableSpace (FieldConfigurationTorus d L)
@[instance] axiom instTopologicalSpaceFieldConfigurationTorus (d : ℕ) (L : ℝ) :
  TopologicalSpace (FieldConfigurationTorus d L)

/-! ## Axiomatized operations -/

axiom distributionPairingTorus {d : ℕ} {L : ℝ} :
  FieldConfigurationTorus d L → TestFunctionTorus d L → ℝ

axiom distributionPairingTorusℂ {d : ℕ} {L : ℝ} :
  FieldConfigurationTorus d L → TestFunctionTorusℂ d L → ℂ

axiom timeReflectionTorus (d : ℕ) (L : ℝ) :
  TestFunctionTorus d L →L[ℝ] TestFunctionTorus d L

axiom positiveTimeSubmoduleTorus (d : ℕ) (L : ℝ) :
  Submodule ℝ (TestFunctionTorus d L)

axiom timeTranslationDistTorus {d : ℕ} {L : ℝ} :
  ℝ → FieldConfigurationTorus d L → FieldConfigurationTorus d L

axiom translateTestFunTorus {d : ℕ} {L : ℝ} :
  SpaceTimeTorus d L → TestFunctionTorus d L → TestFunctionTorus d L

/-- Symmetry group for ℝ × T^{d-1}_L: translations of ℝ × T^{d-1}. -/
axiom SymmetryGroupTorus (d : ℕ) (L : ℝ) : Type

@[instance] axiom instGroupSymmetryGroupTorus (d : ℕ) (L : ℝ) :
  Group (SymmetryGroupTorus d L)

axiom symmetryActionTorus {d : ℕ} {L : ℝ} :
  SymmetryGroupTorus d L → TestFunctionTorusℂ d L → TestFunctionTorusℂ d L

end
