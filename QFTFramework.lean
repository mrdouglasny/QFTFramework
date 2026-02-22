-- QFTFramework: Shared foundations for formalizing quantum field theory
--
-- Layer 1: Spacetime geometry (independent of theory)
import QFTFramework.SpacetimeData
import QFTFramework.Spacetime.Euclidean
import QFTFramework.Spacetime.Torus
import QFTFramework.Spacetime.Lattice

-- Layer 2: Theory specification (independent of spacetime)
import QFTFramework.TheoryData

-- Layer 3: QFT = Spacetime + Theory → Measure
import QFTFramework.QFTData

-- Layer 4: Axiomatic systems
import QFTFramework.Axioms.OsterwalderSchrader
