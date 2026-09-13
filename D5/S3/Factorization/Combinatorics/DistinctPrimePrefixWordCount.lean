/- GID: D5/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Words with prescribed multiplicities and distinct initial labels are counted by elementary symmetric coefficients. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.DistinctPrimePrefixWordCount

noncomputable section
open scoped BigOperators
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

/-- The number of words with occupation `a` whose first `j` labels are pairwise distinct. -/
def distinctPrefixCount {q : ℕ} (a : Multiset (Fin q)) (j : ℕ) : ℕ := by
  classical
  exact ((sectorWords a.card a).filter (fun w => ((List.ofFn w).take j).Nodup)).card

/-- The elementary symmetric coefficient of degree `j` in the label multiplicities. -/
def elementary {q : ℕ} (a : Multiset (Fin q)) (j : ℕ) : ℕ :=
  ∑ s ∈ (Finset.univ : Finset (Fin q)).powersetCard j, ∏ i ∈ s, a.count i

end D5.S3.Factorization.Combinatorics.DistinctPrimePrefixWordCount
