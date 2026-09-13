/- GID: D5/S0/Rewriting/GuardedBoxPathAttainment
   generality: G
   mirror-B: D5/B/S0/Rewriting/GuardedBoxPathAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every pair of bounded natural configurations admits a shortest guarded unit word whose length is its coordinate distance. -/

import D5.S0.Rewriting.GuardedBoxPaths
import Mathlib.Data.Int.NatAbs

set_option autoImplicit false

namespace D5.S0.Rewriting.GuardedBoxPathAttainment

open GuardedBoxPaths

/-- Two configurations in a finite capacity box are joined by a successful unit word
whose length is their total absolute coordinate difference and is minimal among all
successful words with those endpoints. -/
theorem exists_shortest_word {P : Type*} [DecidableEq P] [Fintype P]
    (A a b : P → ℕ) (ha : ∀ p, a p ≤ A p) (hb : ∀ p, b p ≤ A p) :
    ∃ w : List (Instruction P), LegalPath A a b w ∧ w.length = distance a b ∧
      ∀ v : List (Instruction P), LegalPath A a b v → w.length ≤ v.length := by
  sorry

end D5.S0.Rewriting.GuardedBoxPathAttainment
