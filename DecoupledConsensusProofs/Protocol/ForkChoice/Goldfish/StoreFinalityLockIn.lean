module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Agreement
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityConsequences
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityUpgrade

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# B11 lock-in for the composed fork choice

This file extends doc1's height argument through the rewrite's two-stage fork
choice. In the cascade branch, the fork-choice root is the upgraded justified
block. In the non-cascade branch, directed earlier safety makes every candidate
comparable with historical finality. The height clause then makes the unique
path child toward that finality checkpoint eligible in the final Goldfish walk.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A high maximum-height witness makes historical `F` viable while the
current finalized block is at or below it. This is the high-frontier branch of
`finalized_mem_viable_of_current_preceq`; it does not require the remote
finalizing carrier itself to be processed by this store.

Statement change (ledger row C): the store is the named store and
the external finalizer is a named body, so directed earlier safety is
`NamedFinalizationBridge.finalized_preceq_of_height_lt` and the derived-state
agreement is the coherence clause `NamedStore.DerivedView`. -/
theorem finalized_mem_viable_of_height_lt_max {S : Setup V} {ρ : Run V}
    {st : Protocol.NamedStore V} {BF : NamedBlock V} {F : Block V} {h_f : Height}
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hFT : F ∈ st.core.T)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies,
      (Protocol.derive_named S.E S.cfg D).h = st.core.h_max)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f)
    (hcur : Block.Preceq st.core.F F)
    (hhigh : h_f < st.core.h_max) :
    F ∈ Protocol.V_tree st.core.toHealing.toFG := by
  obtain ⟨W, hWb, hmaxW⟩ := hmax
  have hheight : (Protocol.derive_named S.E S.cfg BF).h_F <
      (Protocol.derive_named S.E S.cfg W).h := by
    rw [hfin.2, hmaxW]
    exact hhigh
  have hFW : Block.Preceq F W.erase := by
    have h := NamedFinalizationBridge.finalized_preceq_of_height_lt S ρ W BF hsb hcf
      (hRun W hWb) hBF hheight
    rwa [hfin.1] at h
  have hWT : W.erase ∈ st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWb
  simp only [Protocol.V_tree, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
  refine ⟨⟨hFT, hcur⟩, W.erase, hWT, hFW, ?_⟩
  rw [hcoh.2.2.2.2 W hWb, hmaxW]
  exact Nat.sub_le _ _

/-- Every fork-choice candidate is comparable with a historical finalized
checkpoint once the candidate frontier is strictly above its height.

Same statement change as `finalized_mem_viable_of_height_lt_max`. -/
theorem candidate_comparable_with_finalized {S : Setup V} {ρ : Run V}
    {st : Protocol.NamedStore V} {BF : NamedBlock V} {F : Block V} {h_f : Height}
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f)
    (hfrontier : h_f < st.core.h_max - 1) :
    ∀ X ∈ Protocol.get_filtered_block_tree st.core.toHealing.toFG,
      Block.Preceq X F ∨ Block.Preceq F X := by
  intro X hX
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq,
    Protocol.Store.toHealing] at hX
  obtain ⟨⟨⟨_, _⟩, W, hWT, hXW, hWheight⟩, _⟩ := hX
  have hWT' : W ∈ st.bodies.image NamedBlock.erase := by rw [← hcoh.1]; exact hWT
  obtain ⟨Wn, hWnb, hWnE⟩ := Finset.mem_image.mp hWT'
  have hheight : (Protocol.derive_named S.E S.cfg BF).h_F <
      (Protocol.derive_named S.E S.cfg Wn).h := by
    rw [hfin.2, ← hcoh.2.2.2.2 Wn hWnb, hWnE]
    exact lt_of_lt_of_le hfrontier hWheight
  have hFW : Block.Preceq F W := by
    have h := NamedFinalizationBridge.finalized_preceq_of_height_lt S ρ Wn BF hsb hcf
      (hRun Wn hWnb) hBF hheight
    rw [hfin.1] at h
    rwa [hWnE] at h
  exact Block.preceq_linear hXW hFW

/-- If the SG anchor is at or below historical `F`, the final Goldfish walk
passes through `F`. The low-height clause makes the unique path child eligible;
comparability with `F` makes it the only candidate child. -/
theorem goldfish_fork_choice_passes_finalized (E : Env V)
    (st : Protocol.Store V) (anchor F : Block V)
    (votes supportVotes : Finset (GoldfishVote V)) (k : Slot)
    (hFJ : Block.Preceq st.F st.J)
    (hpc : ParentClosed st)
    (hFT : F ∈ st.T)
    (hFtree : F ∈ Protocol.get_filtered_block_tree st.toHealing.toFG)
    (hrootAnchor : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) anchor)
    (hanchorF : Block.Preceq anchor F)
    (hbelow : ∀ C ∈ st.T, Block.Preceq C F →
      (st.σ C).h < st.h_max - 1)
    (hcompare : ∀ X ∈ Protocol.get_filtered_block_tree st.toHealing.toFG,
      Block.Preceq X F ∨ Block.Preceq F X) :
    Block.Preceq F
      (Protocol.goldfish_fork_choice E st.σ st.h_max st.T st.s anchor
        (Protocol.get_filtered_block_tree st.toHealing.toFG)
        votes supportVotes k) := by
  simp only [Protocol.goldfish_fork_choice]
  refine Proofs.Optimistic.ghost_passes hanchorF ?_ ?_
  · intro C hanchorC _ hCF
    have hCT : C ∈ st.T := Proofs.Records.mem_of_preceq
      ((parentClosed_iff st).mp hpc).2 C F hFT hCF
    exact Proofs.Records.mem_filtered_of_preceq hFJ hFtree hCT hCF
      (Block.preceq_trans hrootAnchor hanchorC)
  · intro H hanchorH hHF hne
    obtain ⟨C, hCparent, hCF⟩ := Protocol.exists_child_towards F hHF hne
    have hHC : Block.Preceq H C := Protocol.preceq_of_parent? hCparent
    have hrootC : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) C :=
      Block.preceq_trans hrootAnchor
        (Block.preceq_trans hanchorH hHC)
    have hCT : C ∈ st.T := Proofs.Records.mem_of_preceq
      ((parentClosed_iff st).mp hpc).2 C F hFT hCF
    have hCtree : C ∈
        Protocol.get_filtered_block_tree st.toHealing.toFG :=
      Proofs.Records.mem_filtered_of_preceq hFJ hFtree hCT hCF hrootC
    have hCeligible : Protocol.goldfish_eligible E st.σ st.h_max st.T st.s
        votes supportVotes k C = true := by
      have hHT : H ∈ st.T := Proofs.Records.mem_of_preceq
        ((parentClosed_iff st).mp hpc).2 H F hFT hHF
      have hHbelow := hbelow H hHT hHF
      rw [Proofs.Optimistic.goldfish_eligible_iff]
      rw [parent_eq_of_parent? hCparent]
      exact Or.inl hHbelow
    have hCchildren : C ∈ Protocol.ghost_children
        (Protocol.get_filtered_block_tree st.toHealing.toFG)
        (Protocol.goldfish_eligible E st.σ st.h_max st.T st.s
          votes supportVotes k) H := by
      simp only [Protocol.ghost_children, Finset.mem_filter]
      exact ⟨hCtree, hCparent, hCeligible⟩
    have hunique : ∀ D ∈ Protocol.ghost_children
        (Protocol.get_filtered_block_tree st.toHealing.toFG)
        (Protocol.goldfish_eligible E st.σ st.h_max st.T st.s
          votes supportVotes k) H, D = C := by
      intro D hD
      have hDdata := Finset.mem_filter.mp hD
      rcases hcompare D hDdata.1 with hDF | hFD
      · exact Protocol.child_towards_unique hCparent hDdata.2.1 hCF hDF
      · exact Protocol.child_towards_unique hCparent hDdata.2.1
          (Block.preceq_trans hCF hFD) (Block.preceq_self D)
    refine ⟨C, ?_, hCF⟩
    unfold Protocol.ghost_step
    exact Proofs.Optimistic.argmax?_eq_some_of_unique hCchildren hunique

omit [Fintype V] in
/-- The exact FG-root boundary for external lock-in.

If the cascade gate fires, or if local finality has already reached historical
`F`, then `F` precedes `get_fg_root`. The only remaining case is doc1's
non-cascade branch: `get_fg_root` is the older local finalized block, it
precedes `F`, and the height frontier is strictly above `h_f + 1`. B11's
final Goldfish argument is needed only in this second branch. -/
theorem lockIn_fgRoot_boundary {st : Protocol.Store V} {F : Block V}
    {h_f : Height}
    (hcurJ : Block.Preceq st.F st.J)
    (hupgrade : Block.Preceq F st.J)
    (hheightLe : h_f ≤ st.h_j)
    (hbelowMax : st.h_j < st.h_max) :
    Block.Preceq F (Protocol.get_fg_root st.toHealing.toFG) ∨
      (Protocol.get_fg_root st.toHealing.toFG = st.F ∧
        Block.Preceq st.F F ∧ h_f < st.h_max - 1) := by
  by_cases hgate : st.h_max = st.h_j + 1
  · exact Or.inl (justified_preceq_fgRoot hupgrade (Or.inr hgate))
  · have hroot : Protocol.get_fg_root st.toHealing.toFG = st.F := by
      simp [Protocol.get_fg_root, Protocol.Store.toHealing, hgate]
    rcases Block.preceq_linear hcurJ hupgrade with hcurF | hFlocal
    · refine Or.inr ⟨hroot, hcurF, ?_⟩
      have key : ∀ a b c : Nat, a ≤ b → b < c → c ≠ b + 1 → a < c - 1 := by
        omega
      exact key h_f st.h_j st.h_max hheightLe hbelowMax hgate
    · exact Or.inl (by rw [hroot]; exact hFlocal)



/-! B11 external lock-in over the named store. -/
theorem lockIn_external_fgRoot_boundary {S : Setup V} {ρ : Run V}
    {st : Protocol.NamedStore V} {BF B : NamedBlock V} {F : Block V} {h_f : Height}
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hnhj : Internal.NamedNoHighJustifications S.E S.cfg st)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hbelow : Internal.JustificationBelowMax st.core)
    (hviable : FinalizedViable st.core)
    (horder : Block.preceq st.core.F st.core.J = true)
    (hmax : ∃ D ∈ st.bodies,
      (Protocol.derive_named S.E S.cfg D).h = st.core.h_max)
    (hB : B ∈ st.bodies)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg B F h_f)
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f) :
    Block.Preceq F st.core.J ∧ Internal.HasViableDescendant st.core F ∧
      (Block.Preceq F (Protocol.get_fg_root st.core.toHealing.toFG) ∨
        (Protocol.get_fg_root st.core.toHealing.toFG = st.core.F ∧
          Block.Preceq st.core.F F ∧ h_f < st.core.h_max - 1)) := by
  have hupgrade := upgrade hnhj hprov hB hjust hsb hcf hBF hRun hfin
  have hheightLe : h_f ≤ st.core.h_j := by
    rw [← hjust.2]
    exact hnhj B hB
  exact ⟨hupgrade,
    viableFinalized_external hcoh hnhj hprov hbelow hviable horder hmax hB hjust
      hsb hcf hBF hRun hfin,
    lockIn_fgRoot_boundary horder hupgrade hheightLe hbelow⟩




end StoreFinality
end Proofs
end DecoupledConsensusModel

end
