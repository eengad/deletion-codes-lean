import DeletionCode.RelationBlockSavings
import DeletionCode.BlockAdjunction

/-!
Ordered generation on actual finite sets of integer rules. A strict rank
assignment records the inherited order. Restriction to whole rule blocks
preserves both that order and rational independence, and retains each supplier
because it shares the actual negative gram.
-/
namespace DeletionCode.FiniteGenerating

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

def GeneratingOn {k : ℕ} (v : Gram (windowLength k) → ℤ) (G : RuleSet k)
    (rank : (Gram (windowLength k) → ℤ) → ℕ) : Prop :=
  ∀ u ∈ G, ∀ g, u g = -1 → v g ≠ 0 ∨ ∃ z ∈ G, rank z < rank u ∧ z g ≠ 0

def Independent {k : ℕ} (G : RuleSet k) : Prop :=
  LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ))

/-- A finite independent generating set with an actual strict ordering. -/
structure GeneratingAt {k : ℕ} (v : Gram (windowLength k) → ℤ) (G : RuleSet k) : Prop where
  independent : Independent G
  ordered : ∃ rank : (Gram (windowLength k) → ℤ) → ℕ,
    Set.InjOn rank (↑G : Set _) ∧ GeneratingOn v G rank

def ClosedIn {k : ℕ} (G U : RuleSet k) : Prop :=
  ∀ a ∈ U, ∀ b ∈ G, ConnectedIn G a b → b ∈ U

theorem independent_restrict {k : ℕ} {G U : RuleSet k} (hUG : U ⊆ G)
    (hind : Independent G) : Independent U := by
  let f : U → G := fun u => ⟨u.val, hUG u.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun u : G => u.val) hab)
  exact hind.comp f hf

theorem generating_restrict {k : ℕ} (v : Gram (windowLength k) → ℤ)
    (G U : RuleSet k) (rank : (Gram (windowLength k) → ℤ) → ℕ)
    (hUG : U ⊆ G) (hclosed : ClosedIn G U) (hgen : GeneratingOn v G rank) :
    GeneratingOn v U rank := by
  intro u hu g hneg
  rcases hgen u (hUG hu) g hneg with hv | ⟨z, hz, hrank, hzg⟩
  · exact Or.inl hv
  · have hconnect : ConnectedIn G u z := Relation.EqvGen.rel _ _
      ⟨hUG hu, hz, gramPrefix g,
        GeneratingBlocks.nonzero_incident u g (by omega),
        GeneratingBlocks.nonzero_incident z g hzg⟩
    exact Or.inr ⟨z, hclosed u hu z hz hconnect, hrank, hzg⟩

theorem GeneratingAt.restrict {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G U : RuleSet k} (hgen : GeneratingAt v G) (hUG : U ⊆ G)
    (hclosed : ClosedIn G U) : GeneratingAt v U := by
  obtain ⟨rank, hinj, horder⟩ := hgen.ordered
  refine ⟨independent_restrict hUG hgen.independent, rank, ?_,
    generating_restrict v G U rank hUG hclosed horder⟩
  intro a ha b hb hab
  exact hinj (hUG ha) (hUG hb) hab

theorem blockHull_closed {k : ℕ} (G I : RuleSet k) :
    ClosedIn G (RelationBlockSavings.blockHull G I) := by
  intro a ha b _ hab
  exact RelationBlockSavings.blockHull_closed G I ha hab

theorem generating_blockHull {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (I : RuleSet k) :
    GeneratingAt v (RelationBlockSavings.blockHull G I) :=
  hgen.restrict (RelationBlockSavings.blockHull_subset G I) (blockHull_closed G I)

theorem blockOf_closed {k : ℕ} (G : RuleSet k) (a : Gram (windowLength k) → ℤ) :
    ClosedIn G (blockOf G a) := by
  intro b hb c hc hbc
  exact (mem_blockOf G a c).mpr
    ⟨hc, Relation.EqvGen.trans _ _ _ ((mem_blockOf G a b).mp hb).2 hbc⟩

theorem generating_blockOf {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (a : Gram (windowLength k) → ℤ) :
    GeneratingAt v (blockOf G a) := by
  apply hgen.restrict
  · intro u hu
    exact ((mem_blockOf G a u).mp hu).1
  · exact blockOf_closed G a

#print axioms independent_restrict
#print axioms generating_restrict
#print axioms GeneratingAt.restrict
#print axioms generating_blockHull
#print axioms generating_blockOf

end DeletionCode.FiniteGenerating
