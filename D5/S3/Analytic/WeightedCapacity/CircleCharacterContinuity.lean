/- GID: D5/S3/Analytic/WeightedCapacity/CircleCharacterContinuity
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/CircleCharacterContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity of an arbitrary circle character at a finite capacity state forces finite weighted absolute mass. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.CircleCharacterContinuity

open DyadicTailFilling Set Filter
open scoped Topology BigOperators

/-- The representative of a circle point in the half-open interval from minus one half to one half. -/
noncomputable def centered (t : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) t : ℝ)

/-- The circle character of a total circle row on finite capacity states. -/
noncomputable def charRow {A : ℕ → ℕ} (θ : ℕ → AddCircle (1 : ℝ)) (u : B A) :
    AddCircle (1 : ℝ) :=
  ∑ n ∈ u.property.toFinset, ((u.val n : ℕ) : ℤ) • θ n

/-- The extended sum of the capacities multiplied by the absolute centered representatives. -/
noncomputable def mass (A : ℕ → ℕ) (θ : ℕ → AddCircle (1 : ℝ)) : ENNReal :=
  ∑' n, ENNReal.ofReal ((A n : ℝ) * |centered (θ n)|)

end D5.S3.Analytic.WeightedCapacity.CircleCharacterContinuity
