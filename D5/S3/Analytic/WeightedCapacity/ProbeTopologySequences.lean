/- GID: D5/S3/Analytic/WeightedCapacity/ProbeTopologySequences
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/ProbeTopologySequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sequences of finite capacity states converge in the rational probe topology exactly when eventually equal to their limit. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Finsupp.BigOperators

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences

open DyadicTailFilling Set Filter
open scoped Topology BigOperators

/-- The circle character associated with a total rational coefficient sequence. -/
noncomputable def chi {A : ℕ → ℕ} (r : ℕ → ℚ) (u : B A) : AddCircle (1 : ℝ) :=
  ((∑ n ∈ u.property.toFinset, r n * ((u.val n : ℕ) : ℚ) : ℚ) : ℝ)

/-- The coordinate phases with golden ratio frequency. -/
noncomputable def psi {A : ℕ → ℕ} (u : B A) : ℕ → AddCircle (1 : ℝ) :=
  fun n => (Real.goldenRatio * ((u.val n : ℕ) : ℝ) : ℝ)

/-- The initial topology of the golden phases and all rational characters. -/
noncomputable def tauPlus (A : ℕ → ℕ) : TopologicalSpace (B A) :=
  TopologicalSpace.induced psi inferInstance ⊓
    ⨅ r : ℕ → ℚ, TopologicalSpace.induced (chi r) inferInstance

end D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences
