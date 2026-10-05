import DeletionCode.OddGraphWalk
import DeletionCode.Burst.BoundedWitnessWalk

/-! Nonbipartite components produce bounded burst-catalogue witnesses. -/
namespace DeletionCode.Burst.WordGraphWitness

open DeletionCode.Qary.Windows DeletionCode.Qary.SignedSupport DeletionCode.Qary.SignedRuleCount
open BoundedWitnessWalk

variable {α : Type*} [Fintype α] [DecidableEq α] [Inhabited α]

theorem component_witness {V : Type*} {t k b n : ℕ} (ht : 2 ≤ t)
    (G : SimpleGraph V) (words : V → Letters α)
    (K : Set (Gram α (windowLength k b) → ℤ))
    (hunique : ∀ v, KUnique (words v) n k)
    (hcat : ∀ {v w}, G.Adj v w → Catalogue.Rule t k b
      (wordSpectrum (words w) n (windowLength k b) -
        wordSpectrum (words v) n (windowLength k b)))
    (hK : ∀ {v w}, G.Adj v w →
      (wordSpectrum (words w) n (windowLength k b) -
        wordSpectrum (words v) n (windowLength k b)) ∈ K)
    (x : V) (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet α (k + b),
      Witness t k b (wordSpectrum (words x) n (windowLength k b)) K U := by
  obtain ⟨m, hodd, vertices, hstart, hend, hadj⟩ := OddGraphWalk.component_odd_walk x hnot
  let walkWords : Fin (m + 1) → Letters α := fun j => words (vertices j)
  have hclosed : Agree (walkWords 0) 0 (walkWords (Fin.last m)) 0 n := by
    intro j _
    simp only [walkWords, hstart, hend]
  obtain ⟨U, hU⟩ := extract_word_walk ht walkWords K
    (fun j => hunique (vertices j)) hclosed hodd (fun i => hcat (hadj i))
    (fun i => hK (hadj i))
  exact ⟨U, by simpa only [walkWords, hstart] using hU⟩

end DeletionCode.Burst.WordGraphWitness
