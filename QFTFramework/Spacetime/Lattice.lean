/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Lattice Spacetime aℤ^d

The discrete lattice spacetime aℤ^d, where lattice points are integer-valued
vectors embedded into ℝ^d at positions a·n.

## Design Notes

- Lattice spacing `a` enters via the embedding, not as a type parameter
- The metric is inherited from ℝ^d: dist(n,m) = ‖a·n - a·m‖
- TimeParam = ℤ (discrete time steps)
- The symmetry group is translations ℤ^d ⋊ hypercubic group
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ} [Fact (0 < d)]

/-- Lattice spacetime: integer-valued coordinate vectors. -/
abbrev SpaceTimeLattice (d : ℕ) := Fin d → ℤ

instance : Inhabited (SpaceTimeLattice d) := ⟨fun _ => 0⟩

instance : AddCommGroup (SpaceTimeLattice d) := Pi.addCommGroup

/-- Test functions on the lattice: real-valued functions on ℤ^d. -/
abbrev TestFunctionLattice (d : ℕ) := (Fin d → ℤ) → ℝ

/-- Complex test functions on the lattice. -/
abbrev TestFunctionLatticeℂ (d : ℕ) := (Fin d → ℤ) → ℂ

/-- Field configurations on the lattice: real values at each lattice site. -/
abbrev FieldConfigurationLattice (d : ℕ) := (Fin d → ℤ) → ℝ

instance : MeasurableSpace (FieldConfigurationLattice d) := borel _

/-- Lattice distribution pairing: ⟨φ, f⟩ = ∑_n φ(n) · f(n). -/
def latticeDistributionPairing (φ : FieldConfigurationLattice d)
    (f : TestFunctionLattice d) : ℝ :=
  ∑' n, φ n * f n

/-- Complex lattice pairing: ⟨φ, f⟩_ℂ = ∑_n φ(n) · f(n). -/
def latticeDistributionPairingℂ (φ : FieldConfigurationLattice d)
    (f : TestFunctionLatticeℂ d) : ℂ :=
  ∑' n, (φ n : ℂ) * f n

/-- Time reflection on the lattice: negate the time coordinate (index 0). -/
def latticeTimeReflection (f : TestFunctionLattice d) : TestFunctionLattice d :=
  fun n => f (Function.update n ⟨0, Fact.out⟩ (-n ⟨0, Fact.out⟩))

/-- Time reflection as a continuous linear map. -/
def latticeTimeReflectionCLM : TestFunctionLattice d →L[ℝ] TestFunctionLattice d :=
  { toLinearMap :=
    { toFun := latticeTimeReflection
      map_add' := by intro f g; ext n; simp [latticeTimeReflection]
      map_smul' := by intro c f; ext n; simp [latticeTimeReflection] }
    cont := by
      apply continuous_pi
      intro n
      exact continuous_apply _ }

/-- Submodule of positive-time lattice test functions:
f is supported on {n | n₀ > 0}. -/
def latticePositiveTimeSubmodule : Submodule ℝ (TestFunctionLattice d) where
  carrier := { f | ∀ n : SpaceTimeLattice d, n ⟨0, Fact.out⟩ ≤ 0 → f n = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    intro n hn
    rw [hf n hn, hg n hn, add_zero]
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    intro n hn
    rw [hf n hn, mul_zero]

/-- Time translation on lattice field configurations. -/
def latticeTimeTranslation (s : ℤ) (φ : FieldConfigurationLattice d) :
    FieldConfigurationLattice d :=
  fun n => φ (Function.update n ⟨0, Fact.out⟩ (n ⟨0, Fact.out⟩ - s))

/-- Spatial translation of lattice test functions by a lattice vector. -/
def latticeTranslateTestFun (a : SpaceTimeLattice d) (f : TestFunctionLattice d) :
    TestFunctionLattice d :=
  fun n => f (n - a)

/-- The hypercubic group: signed permutations of coordinates. -/
structure HypercubicElement (d : ℕ) where
  perm : Equiv.Perm (Fin d)
  signs : Fin d → Int
  signs_sq : ∀ i, signs i = 1 ∨ signs i = -1

/-- The lattice symmetry group: ℤ^d translations ⋊ hypercubic group. -/
structure LatticeSymmetryGroup (d : ℕ) where
  translation : Fin d → ℤ
  hypercubic : HypercubicElement d

instance : One (LatticeSymmetryGroup d) :=
  ⟨{ translation := fun _ => 0
     hypercubic :=
       { perm := Equiv.refl _
         signs := fun _ => 1
         signs_sq := fun _ => Or.inl rfl } }⟩

@[instance] axiom instGroupLatticeSymmetryGroup (d : ℕ) :
  Group (LatticeSymmetryGroup d)

/-- Action of the lattice symmetry group on complex test functions. -/
def latticeSymmetryActionℂ (g : LatticeSymmetryGroup d)
    (f : TestFunctionLatticeℂ d) : TestFunctionLatticeℂ d :=
  fun n => f (fun i => g.hypercubic.signs i * n (g.hypercubic.perm i)
    + g.translation i)

end
