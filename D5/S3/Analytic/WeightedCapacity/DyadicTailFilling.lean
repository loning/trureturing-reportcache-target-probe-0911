/- GID: D5/S3/Analytic/WeightedCapacity/DyadicTailFilling
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/DyadicTailFilling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Divergent dyadic capacities give exact sublevel closures of finite state levels. -/
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Constructions
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

open Set Filter
open scoped Topology BigOperators

/-- The product of the discrete natural coordinate intervals bounded by the capacities. -/
abbrev X (A : ℕ → ℕ) := ∀ n, Fin (A n + 1)

/-- The sum of the first k dyadically weighted natural coordinates. -/
noncomputable def prefixSum (k : ℕ) (x : ℕ → ℕ) : ℝ :=
  ∑ n ∈ Finset.range k, (x n : ℝ) / 2 ^ n

/-- The inclusive prefixSum sum through coordinate N. -/
noncomputable def P {A : ℕ → ℕ} (N : ℕ) (x : X A) : ℝ :=
  prefixSum (N + 1) (fun n => (x n : ℕ))

/-- The supremum of the nonnegative inclusive prefixSum sums in the extended nonnegative reals. -/
noncomputable def S {A : ℕ → ℕ} (x : X A) : ENNReal :=
  ⨆ N, ENNReal.ofReal (P N x)

/-- The extended total mass of the capacity corner. -/
noncomputable def M (A : ℕ → ℕ) : ENNReal :=
  S (fun n => ⟨A n, Nat.lt_succ_self _⟩)

/-- States with finite support, equipped with the topology inherited from the full product. -/
def B (A : ℕ → ℕ) := {x : X A // (Function.support (fun n => (x n : ℕ))).Finite}

/-- The real dyadic sum over the finite support of a state. -/
noncomputable def readout {A : ℕ → ℕ} (u : B A) : ℝ :=
  ∑ n ∈ u.property.toFinset, ((u.val n : ℕ) : ℝ) / 2 ^ n

/-- Nonnegative dyadic rational real numbers. -/
def Dpos : Set ℝ := {c | ∃ a q : ℕ, c = (a : ℝ) / 2 ^ q}

/-- A finite-state level set in its relative carrier. -/
def L (A : ℕ → ℕ) (c : ℝ) : Set (B A) := {u | readout u = c}

/-- The image of a finite-state level in the full product. -/
def ambientLevel (A : ℕ → ℕ) (c : ℝ) : Set (X A) := Subtype.val '' L A c

/-- Under divergent total capacity, a nonnegative dyadic finite-state level has precisely the
extended-sum sublevel as its closure in the full product. -/
theorem closure_level_eq_sublevel (A : ℕ → ℕ) (c : ℝ) (hM : M A = ⊤)
    (hc : c ∈ Dpos) :
    closure (ambientLevel A c) = {x | S x ≤ ENNReal.ofReal c} := by
  sorry

end D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
