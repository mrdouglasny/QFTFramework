/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Euclidean Spacetime ℝ^d

Core type definitions for flat Euclidean spacetime, parametric in dimension d.
These mirror the definitions in OSforGFF/Basic.lean but are parametric from
the start.

## Main Definitions

* `SpaceTime d` — Euclidean space ℝ^d
* `TestFunction d` — Schwartz functions 𝓢(ℝ^d, ℝ)
* `FieldConfiguration d` — Tempered distributions S'(ℝ^d)
* `EuclideanGroup d` — The Euclidean group E(d) = O(d) ⋊ ℝ^d
-/

open MeasureTheory

noncomputable section

variable (d : ℕ) [Fact (0 < d)]

/-- Euclidean spacetime ℝ^d with standard inner product. -/
abbrev SpaceTime (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Real-valued Schwartz functions on ℝ^d. -/
abbrev TestFunction (d : ℕ) := SchwartzMap (SpaceTime d) ℝ

/-- Complex-valued Schwartz functions on ℝ^d. -/
abbrev TestFunctionℂ (d : ℕ) := SchwartzMap (SpaceTime d) ℂ

/-- Field configurations as tempered distributions: the weak dual of Schwartz space. -/
abbrev FieldConfiguration (d : ℕ) := WeakDual ℝ (SchwartzMap (SpaceTime d) ℝ)

/-- Lebesgue measure on spacetime. -/
abbrev spaceTimeVolume (d : ℕ) : Measure (SpaceTime d) := volume

/-- The time coordinate (index 0). -/
def getTimeComponent {d : ℕ} [Fact (0 < d)] (x : SpaceTime d) : ℝ :=
  x ⟨0, Fact.out⟩

/-- Orthogonal group O(d): linear isometries of ℝ^d. -/
abbrev OrthogonalGroup (d : ℕ) :=
  LinearIsometry (RingHom.id ℝ) (SpaceTime d) (SpaceTime d)

/-- The Euclidean group E(d) = O(d) ⋊ ℝ^d (rotations + translations). -/
structure EuclideanGroup (d : ℕ) where
  /-- Orthogonal transformation (rotation/reflection) -/
  R : OrthogonalGroup d
  /-- Translation vector -/
  t : SpaceTime d

/-- Action of the Euclidean group on spacetime: x ↦ Rx + t. -/
def EuclideanGroup.act {d : ℕ} (g : EuclideanGroup d) (x : SpaceTime d) : SpaceTime d :=
  g.R x + g.t

instance {d : ℕ} : One (EuclideanGroup d) :=
  ⟨⟨1, 0⟩⟩

instance {d : ℕ} : Inhabited (EuclideanGroup d) :=
  ⟨1⟩

/-- Measurable space on field configurations (Borel σ-algebra). -/
instance {d : ℕ} : MeasurableSpace (FieldConfiguration d) := borel _

end
