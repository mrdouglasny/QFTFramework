/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

/-!
# TheoryData — QFT Specification Hierarchy

A QFT can be specified in different ways: by a Lagrangian action (with explicit
field content and couplings), by CFT axioms (central charge, OPE data), by
bootstrap constraints, by a lattice model, etc.

This file defines the hierarchy:
- `TheoryData` — abstract: internal symmetry group + field content
- `QFTActionData` — Lagrangian: masses, couplings, gauge group
- `CFTData` — conformal bootstrap: central charge, OPE coefficients

## References

* aqft2/docs/multidim_plan.md
-/

/-! ## Abstract Theory Data -/

/-- Abstract specification of a quantum field theory's content.

This is the most general notion — a theory can be specified by an action
(`QFTActionData`), by CFT axioms (`CFTData`), by bootstrap constraints,
or by other means. The common structure is the internal (global) symmetry
group and the number of field species. -/
structure TheoryData where
  /-- Internal (global) symmetry group.
      Examples: `Unit` (trivial), `ZMod 2` (Ising ℤ₂), O(N) model -/
  InternalSymGroup : Type
  [instISG : Group InternalSymGroup]
  /-- Number of bosonic field species -/
  nBosonic : ℕ
  /-- Number of fermionic field species -/
  nFermionic : ℕ

namespace TheoryData
attribute [instance] instISG
end TheoryData

/-! ## Lagrangian Specification -/

/-- A QFT specified by a Euclidean action S_E[φ, ψ, A].

Lists the coupling constants that appear in the Lagrangian.
The same action data can be placed on different spacetimes. -/
structure QFTActionData extends TheoryData where
  /-- Gauge group (Unit for no gauge, SU n, U n, etc.) -/
  gaugeGroup : Type
  [instGaugeGrp : Group gaugeGroup]
  /-- Scalar mass squared m²ᵢ for each bosonic species -/
  scalarMassSq : Fin nBosonic → ℝ
  /-- Scalar self-interaction potential V(φ₁, ..., φₙ) -/
  scalarPotential : (Fin nBosonic → ℝ) → ℝ
  /-- Fermion masses -/
  fermionMass : Fin nFermionic → ℝ
  /-- Yukawa couplings y^a_{ij} -/
  yukawaCoeff : Fin nFermionic → Fin nFermionic → Fin nBosonic → ℝ
  /-- Gauge coupling constant g -/
  gaugeCoupling : ℝ

namespace QFTActionData
attribute [instance] instGaugeGrp
end QFTActionData

/-! ## Conformal Bootstrap Specification -/

/-- A QFT specified by conformal bootstrap data.

In the Euclidean signature, conformal symmetry constrains the
correlation functions to be determined by the OPE data. -/
structure CFTData extends TheoryData where
  /-- Central charge c -/
  centralCharge : ℝ
  /-- Indexing type for primary operators -/
  PrimaryIndex : Type
  /-- Scaling dimension Δᵢ of each primary -/
  conformalDim : PrimaryIndex → ℝ
  /-- Spin ℓᵢ of each primary -/
  spin : PrimaryIndex → ℕ
  /-- OPE coefficients C_{ijk} -/
  opeCoeff : PrimaryIndex → PrimaryIndex → PrimaryIndex → ℝ
  /-- The identity operator (Δ = 0, ℓ = 0) -/
  unitOp : PrimaryIndex
  unitOp_dim : conformalDim unitOp = 0
  unitOp_spin : spin unitOp = 0
  /-- Unitarity: all dimensions non-negative -/
  dim_nonneg : ∀ i, 0 ≤ conformalDim i

/-! ## Standard Theory Instances -/

/-- Free massive scalar: 1 boson, no fermions, trivial symmetry. -/
noncomputable def freeScalar (m : ℝ) : QFTActionData where
  InternalSymGroup := Unit
  nBosonic := 1
  nFermionic := 0
  gaugeGroup := Unit
  scalarMassSq := fun _ => m ^ 2
  scalarPotential := fun _ => 0
  fermionMass := Fin.elim0
  yukawaCoeff := fun i => Fin.elim0 i
  gaugeCoupling := 0

/-- φ⁴ theory: 1 scalar with quartic self-coupling, ℤ₂ symmetry φ → -φ. -/
noncomputable def phi4Theory (m : ℝ) (λ_ : ℝ) : QFTActionData where
  InternalSymGroup := ZMod 2
  nBosonic := 1
  nFermionic := 0
  gaugeGroup := Unit
  scalarMassSq := fun _ => m ^ 2
  scalarPotential := fun φ => λ_ * (φ 0) ^ 4
  fermionMass := Fin.elim0
  yukawaCoeff := fun i => Fin.elim0 i
  gaugeCoupling := 0

/-- O(N) model: N scalars with O(N) global symmetry and φ⁴ interaction. -/
noncomputable def oNModel (N : ℕ) (m : ℝ) (λ_ : ℝ) : QFTActionData where
  InternalSymGroup := Unit  -- TODO: OrthogonalGroup N ℝ when available
  nBosonic := N
  nFermionic := 0
  gaugeGroup := Unit
  scalarMassSq := fun _ => m ^ 2
  scalarPotential := fun φ => λ_ * (∑ i, (φ i) ^ 2) ^ 2
  fermionMass := Fin.elim0
  yukawaCoeff := fun i => Fin.elim0 i
  gaugeCoupling := 0
