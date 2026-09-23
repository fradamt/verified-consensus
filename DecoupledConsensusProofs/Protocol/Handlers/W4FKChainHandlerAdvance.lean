module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityUpgrade
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotone
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainCheckpointLift

@[expose] public section

/-! # W4 branches fk-chain: the named block handler absorbs a block's finality

`StoreFinalityAcceptance.lean:338-366` records `on_block_candidate_preceq` as
blocked class d: its handler-field route `on_block_candidate_preceq_of_filters`
(`:298`) is green, but nothing supplies that route's `hupgrade` and `hviable`
premises, because the intermediate `afterJustification (unpackedAfterBlock …)`
state is assembled as a bare `Protocol.Store` with no named counterpart.

This file discharges those two premises without building a named counterpart of
the intermediate state, by reading them off the ORIGINAL named store instead.
Three observations make that possible.

* The handler's own admission guard is `Block.preceq Σ.F B`. So the store's `F`
  and the block's candidate checkpoint are two ancestors of the same block and
  are therefore comparable with no safety premise at all. If the candidate is at
  or below `Σ.F` the goal is already true by finality monotonicity, so only the
  strictly-above case has to fire the write.
* The justification guard is then free on both sides of the merge. If the merge
  fires, the new `Σ.J` IS the block's own justification and the block's chain
  order gives `σ.F ⪯ σ.J`. If it does not, the block's finalized height is at or
  below the store's justification height, which is exactly the hypothesis of
  `StoreFinality.upgrade_of_height_le` AT THE ORIGINAL STORE.
* The viability guard needs a processed descendant of the candidate at the
  frontier. The intermediate frontier is `max Σ.h_max σ.h`, so either the block
  itself is that witness, or the store's own maximum carrier is, and directed
  earlier safety (`NamedFinalizationBridge.finalized_preceq_of_height_lt`) puts the
  candidate below it. This is the argument of
  `StoreFinality.finalized_mem_viable_of_current_preceq`, replayed over the
  intermediate fields.

Nothing here is a new protocol claim, and no new public premise is taken: the
five run-level inputs (`SlashableBound`, `RootCollisionFree`, the block and the
bodies being run blocks, and `NamedProvenance`) are the ones the named facades
already consume, and `NamedProvenance` has premise-free producers at every named
read.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (ChainState HeightConfig derive_named named_transition)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A block below `C` is `C` itself or below `C`'s parent. -/
private theorem w4haPreceqCases {A C : Block V} (h : Block.Preceq A C) :
    A = C ∨ Block.Preceq A C.parent := by
  cases C with
  | genesis =>
      left
      simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using h
  | node p s r gv sv ats i =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr hp


/-- The named block handler either absorbs the block's own finalized checkpoint
into the store's `F`, or is a no-op. Named twin of `on_block_candidate_preceq`
(`StoreFinalityAcceptance.lean:338`, blocked class d). -/
theorem onBlockUsing_candidateFinality_preceq
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    {st : Protocol.NamedStore V} {B : NamedBlock V}
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hBrun : RunBlock S rho B)
    (hRun : ∀ D ∈ st.bodies, RunBlock S rho D)
    (hparent : B.parent ∈ st.bodies) :
    Block.Preceq (derive_named S.E S.cfg B).F
        (Protocol.on_block_using S.E st.core B.erase
          (fun ps => named_transition S.E S.cfg ps B)).F ∨
      Protocol.on_block_using S.E st.core B.erase
        (fun ps => named_transition S.E S.cfg ps B) = st.core := by
  by_cases h1 : st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
      B.erase.parent ∉ st.core.T
  · exact Or.inr (by simp only [Protocol.on_block_using, if_pos h1])
  by_cases h2 : (!Block.preceq st.core.F B.erase) = true
  · exact Or.inr (by simp only [Protocol.on_block_using, if_neg h1, if_pos h2])
  by_cases h3 : B.erase.proposer? ≠ some (S.E.proposer B.erase.slot)
  · exact Or.inr
      (by simp only [Protocol.on_block_using, if_neg h1, if_neg h2, if_pos h3])
  by_cases h4 : ¬ (B.erase.parent.slot < B.erase.slot)
  · exact Or.inr (by
      simp only [Protocol.on_block_using, if_neg h1, if_neg h2, if_neg h3,
        if_pos h4])
  left
  -- the write path
  have hslotLt : B.erase.parent.slot < B.erase.slot := not_not.mp h4
  have hBne : B ≠ NamedBlock.genesis := by
    intro hg
    subst hg
    exact absurd hslotLt (by simp [NamedBlock.erase, Block.parent, Block.slot])
  set sigma : ChainState V := derive_named S.E S.cfg B with hsigmaDef
  set stored : Protocol.Store V :=
    { st.core with
      σ := fun C => if C = B.erase then
        named_transition S.E S.cfg (st.core.σ B.erase.parent) B else st.core.σ C
      T := insert B.erase st.core.T
      timestamp_block := fun C =>
        if C = B.erase then some (st.core.t : Stamp)
        else st.core.timestamp_block C } with hstoredDef
  set unpacked : Protocol.Store V :=
    B.erase.gf_votes.foldl (Protocol.on_goldfish_vote_checked S.E) stored
      with hunpackedDef
  have hhandler : Protocol.on_block_using S.E st.core B.erase
      (fun ps => named_transition S.E S.cfg ps B) =
      Protocol.update_finality unpacked (unpacked.σ B.erase) := by
    simp only [Protocol.on_block_using, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, hunpackedDef, hstoredDef]
  have hcore := coreEq_foldl_on_goldfish_vote_checked S.E
    B.erase.gf_votes stored
  -- the stored chain state at `B` is the named derivation
  have hparentSigma : st.core.σ B.erase.parent = derive_named S.E S.cfg B.parent := by
    rw [Proofs.NamedWire.erase_parent]
    exact hcoh.2.2.2.2 B.parent hparent
  have hsigmaAt : unpacked.σ B.erase = sigma := by
    rw [hcore.σ_eq]
    show (if B.erase = B.erase then
      named_transition S.E S.cfg (st.core.σ B.erase.parent) B
      else st.core.σ B.erase) = sigma
    rw [if_pos rfl, hparentSigma, hsigmaDef]
    exact (BlockProcessingDefaults.derive_named_of_not_genesis S.E S.cfg B hBne).symm
  rw [hhandler, hsigmaAt]
  -- the unpacked fields
  have huF : unpacked.F = st.core.F := by
    rw [hunpackedDef, foldl_on_goldfish_vote_checked_F]
  have huT : unpacked.T = insert B.erase st.core.T := by
    rw [hunpackedDef, Proofs.foldl_on_goldfish_vote_checked_T]
  have huMax : unpacked.h_max = st.core.h_max := by
    rw [hunpackedDef, foldl_on_goldfish_vote_checked_h_max]
  have huJ : unpacked.J = st.core.J := hcore.J_eq
  have huHj : unpacked.h_j = st.core.h_j := hcore.h_j_eq
  -- the two ancestors of `B`
  have hFB : Block.Preceq st.core.F B.erase := by
    simpa only [Bool.not_eq_true', Bool.not_eq_false] using
      (Bool.not_eq_true _ ▸ h2 : ¬ ((!Block.preceq st.core.F B.erase) = true))
  have hparentT : B.erase.parent ∈ st.core.T := by
    by_contra hn
    exact h1 (Or.inr (Or.inr hn))
  have hchain := NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B
  have hcandB : Block.Preceq sigma.F B.erase :=
    (NamedDerivationGeometry.derive_named_anchors_preceq S.E S.cfg B).1
  have hmono : Block.Preceq st.core.F
      (Protocol.update_finality unpacked sigma).F := by
    have h := update_finality_F unpacked sigma
    rw [huF] at h
    exact h
  rcases Block.preceq_linear hcandB hFB with hcandF | hFcand
  · exact Block.preceq_trans hcandF hmono
  by_cases hEq : st.core.F = sigma.F
  · exact Block.preceq_trans (by rw [hEq]; exact Block.preceq_self _) hmono
  -- the strictly-above case: the write fires
  have hprec : Block.prec st.core.F sigma.F = true := by
    simp only [Block.prec, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hEq, hFcand⟩
  set afterMax : Protocol.Store V :=
    { unpacked with h_max := max unpacked.h_max sigma.h } with hafterMaxDef
  set afterJust : Protocol.Store V :=
    if Block.preceq afterMax.F sigma.J &&
        decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
          Protocol.HeightId.mk sigma.h_j sigma.J.root) then
      { afterMax with J := sigma.J, h_j := sigma.h_j }
    else afterMax with hafterJustDef
  have hstep : Protocol.update_finality unpacked sigma =
      if Block.prec afterJust.F sigma.F && Block.preceq sigma.F afterJust.J &&
          decide (sigma.F ∈ Protocol.viable_tree afterJust.σ afterJust.F
            afterJust.h_max afterJust.T)
        then { afterJust with F := sigma.F } else afterJust := rfl
  have hamF : afterMax.F = st.core.F := by rw [hafterMaxDef]; exact huF
  have hamJ : afterMax.J = st.core.J := by rw [hafterMaxDef]; exact huJ
  have hamHj : afterMax.h_j = st.core.h_j := by rw [hafterMaxDef]; exact huHj
  have hajF : afterJust.F = st.core.F := by
    rw [hafterJustDef]; split_ifs <;> exact hamF
  have hajSigma : afterJust.σ = unpacked.σ := by
    rw [hafterJustDef]; split_ifs <;> rfl
  have hajT : afterJust.T = insert B.erase st.core.T := by
    rw [hafterJustDef]
    split_ifs <;> (show afterMax.T = _; rw [hafterMaxDef]; exact huT)
  have hajMax : afterJust.h_max = max st.core.h_max sigma.h := by
    rw [hafterJustDef]
    split_ifs <;> (show afterMax.h_max = _; rw [hafterMaxDef, huMax])
  -- guard 1
  have hc1 : Block.prec afterJust.F sigma.F = true := by rw [hajF]; exact hprec
  -- guard 2
  have hFJsigma : Block.Preceq afterMax.F sigma.J := by
    rw [hamF]
    exact Block.preceq_trans hFcand hchain.finalized_preceq_justified
  have hc2 : Block.preceq sigma.F afterJust.J = true := by
    by_cases hmerge : (Block.preceq afterMax.F sigma.J &&
        decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
          Protocol.HeightId.mk sigma.h_j sigma.J.root)) = true
    · have hJ : afterJust.J = sigma.J := by rw [hafterJustDef, if_pos hmerge]
      rw [hJ]
      exact hchain.finalized_preceq_justified
    · have hJ : afterJust.J = st.core.J := by
        rw [hafterJustDef, if_neg hmerge]
        exact hamJ
      rw [hJ]
      refine StoreFinality.upgrade_of_height_le hsb hcf hBrun hRun hprov
        ⟨rfl, rfl⟩ ?_
      have hlex : ¬ (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
          Protocol.HeightId.mk sigma.h_j sigma.J.root) := by
        intro hlt
        exact hmerge (by
          rw [Bool.and_eq_true]
          exact ⟨hFJsigma, decide_eq_true hlt⟩)
      have hle : sigma.h_j ≤ afterMax.h_j :=
        heightId_height_le_of_le (not_lt.mp hlex)
      rw [hamHj] at hle
      exact le_trans hchain.heights_ordered hle
  -- guard 3
  have hmemT : sigma.F ∈ afterJust.T := by
    rw [hajT]
    rcases w4haPreceqCases hcandB with heq | hpar
    · rw [heq]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (NamedDerivationGeometry.core_ancestor_mem S.E S.cfg st hcoh hparentT hpar)
  have hc3 : sigma.F ∈ Protocol.viable_tree afterJust.σ afterJust.F
      afterJust.h_max afterJust.T := by
    simp only [Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    refine ⟨⟨hmemT, by rw [hajF]; exact hFcand⟩, ?_⟩
    by_cases hhigh : sigma.h < st.core.h_max
    · obtain ⟨D, hDb, hDh⟩ := hmax
      have hDrun := hRun D hDb
      have hDne : D.erase ≠ B.erase := by
        intro hDB
        have hDeq : D = B :=
          NamedRootCollisionFree.root_injective hcf D B hDrun hBrun D B
            (Or.inl (Proofs.NamedAncestry.named_self D))
            (Or.inr (Proofs.NamedAncestry.named_self B))
            (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDB])
        rw [hDeq] at hDh
        exact absurd hDh (Nat.ne_of_lt hhigh)
      have hheightLt : (derive_named S.E S.cfg B).h_F <
          (derive_named S.E S.cfg D).h := by
        rw [hDh]
        exact lt_trans hchain.finalized_below_height hhigh
      have hFD : Block.Preceq sigma.F D.erase :=
        NamedFinalizationBridge.finalized_preceq_of_height_lt S rho D B hsb hcf
          hDrun hBrun hheightLt
      refine ⟨D.erase, ?_, hFD, ?_⟩
      · rw [hajT]
        refine Finset.mem_insert_of_mem ?_
        rw [hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hDb
      · have hsigmaD : afterJust.σ D.erase = derive_named S.E S.cfg D := by
          rw [hajSigma, hcore.σ_eq]
          show (if D.erase = B.erase then
            named_transition S.E S.cfg (st.core.σ B.erase.parent) B
            else st.core.σ D.erase) = derive_named S.E S.cfg D
          rw [if_neg hDne]
          exact hcoh.2.2.2.2 D hDb
        rw [hsigmaD, hDh, hajMax, max_eq_left (le_of_lt hhigh)]
        exact Nat.sub_le _ _
    · refine ⟨B.erase, ?_, hcandB, ?_⟩
      · rw [hajT]; exact Finset.mem_insert_self _ _
      · have hsigmaB : afterJust.σ B.erase = sigma := by
          rw [hajSigma]; exact hsigmaAt
        rw [hsigmaB, hajMax, max_eq_right (Nat.le_of_not_lt hhigh)]
        exact Nat.sub_le _ _
  have hguard : (Block.prec afterJust.F sigma.F && Block.preceq sigma.F afterJust.J &&
      decide (sigma.F ∈ Protocol.viable_tree afterJust.σ afterJust.F
        afterJust.h_max afterJust.T)) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hc1, hc2⟩, decide_eq_true hc3⟩
  rw [hstep, if_pos hguard]
  exact Block.preceq_self _

#print axioms onBlockUsing_candidateFinality_preceq

/-! ## The store-level step -/

/-- The named block receipt preserves "every held body's candidate checkpoint is
at or below the store's finalized block". -/
theorem processBlockCore_advance
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    {st : Protocol.NamedStore V} {B : NamedBlock V}
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hBrun : B ∈ (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies →
      RunBlock S rho B)
    (hRun : ∀ D ∈ st.bodies, RunBlock S rho D)
    (hinv : ∀ D ∈ st.bodies,
      Block.Preceq (derive_named S.E S.cfg D).F st.core.F) :
    ∀ D ∈ (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies,
      Block.Preceq (derive_named S.E S.cfg D).F
        (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.F := by
  have hmonoStore :=
    NamedFinalityMonotone.process_block_core_F S.E S.hc S.cfg st B
  by_cases hp : B.parent ∈ st.bodies
  · set after : Protocol.Store V := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun ps => named_transition S.E S.cfg ps B)) S.hc st.core B.erase
        with hafterDef
    have hproc : Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B =
        Protocol.NamedStore.commitBlock st after B := by
      simp only [Protocol.NamedStore.process_block_core,
        if_neg (not_not_intro hp), hafterDef]
    have hcoreEq : (Protocol.NamedStore.commitBlock st after B).core = after :=
      NamedStore.commit_core st after B
    have hmono : Block.Preceq st.core.F after.F := by
      rw [hproc, hcoreEq] at hmonoStore
      exact hmonoStore
    have hnewF : ∀ hgrow : B.erase ∉ st.core.T ∧ B.erase ∈ after.T,
        Block.Preceq (derive_named S.E S.cfg B).F after.F := by
      intro hgrow
      obtain ⟨hfresh, hpost⟩ := hgrow
      have hBmem : B ∈
          (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies := by
        rw [hproc]
        unfold Protocol.NamedStore.commitBlock
        rw [if_pos ⟨hfresh, hpost⟩]
        exact Finset.mem_insert_self _ _
      by_cases hadm : Protocol.carried_attestations_admissible S.hc B.erase = true
      · have hafter : after = Protocol.on_block_using S.E st.core B.erase
            (fun ps => named_transition S.E S.cfg ps B) := by
          rw [hafterDef, Protocol.on_block_checked_using, if_pos hadm]
        rcases onBlockUsing_candidateFinality_preceq S hsb hcf hcoh hmax hprov
          (hBrun hBmem) hRun hp with hgood | hnoop
        · rw [hafter]; exact hgood
        · exact absurd (by rw [hafter, hnoop] at hpost; exact hpost) hfresh
      · have hafter : after = st.core := by
          rw [hafterDef, Protocol.on_block_checked_using,
            if_neg (by simpa using hadm)]
        exact absurd (by rw [hafter] at hpost; exact hpost) hfresh
    rw [hproc, hcoreEq]
    intro D hD
    unfold Protocol.NamedStore.commitBlock at hD
    split_ifs at hD with hgrow
    · rcases Finset.mem_insert.mp hD with rfl | hDold
      · exact hnewF hgrow
      · exact Block.preceq_trans (hinv D hDold) hmono
    · exact Block.preceq_trans (hinv D hD) hmono
  · rw [Protocol.NamedStore.process_block_core, if_pos hp]
    exact hinv

#print axioms processBlockCore_advance

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
