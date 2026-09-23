module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Generic.PrefixFGSelectorWitness
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore

@[expose] public section

/-!
# Honest FG witnesses at the first global height crossing

The first crossing is selected from the execution, not from one reader's
first observation. Every earlier honest height-H action has local frontier H.
An actual progress quorum then supplies an exact checkpoint witness, including
when its honest row is a timeout. No freshness or common-height premise is
needed for this causal base. Freshness and cross-reader compatibility remain
separate bootstrap obligations.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The first global honest-store crossing from at most H to H+1. -/
structure FirstHeightProgressAt
    (S : Setup V) (rho : Run V) (H : Height) (first : Nat) : Prop where
  positive : 0 < first
  frontier : honestHMaxBeforeIndex S rho first = H + 1
  before : ∀ i : Nat, i < first → honestHMaxBeforeIndex S rho i ≤ H

/-- **A height window**: below the cursor `first`, every honest frontier is at
most `H`. A first crossing is one; a run that never crosses above `H` gives
one at any cursor. -/
structure HeightWindowAt
    (S : Setup V) (rho : Run V) (H : Height) (first : Nat) : Prop where
  positive : 0 < first
  before : ∀ i : Nat, i < first → honestHMaxBeforeIndex S rho i ≤ H

/-- A first crossing is a height window. -/
theorem FirstHeightProgressAt.toWindow {S : Setup V} {rho : Run V} {H : Height} {first : Nat}
    (h : FirstHeightProgressAt S rho H first) : HeightWindowAt S rho H first :=
  ⟨h.positive, h.before⟩

/-- An attained crossing has a first global event cursor. The initial-height
bound is a store fact, not a freshness assumption about signatures. -/
theorem exists_firstHeightProgressAt
    (S : Setup V) {rho : Run V} (del : DeliveryWellFormed S rho)
    {H : Height} (hH : 1 ≤ H) {stop : Nat}
    (hcross : H < honestHMaxBeforeIndex S rho stop) :
    ∃ first : Nat, first ≤ stop ∧ FirstHeightProgressAt S rho H first := by
  have hzero : honestHMaxBeforeIndex S rho 0 ≤ 1 := by
    apply Finset.sup_le
    intro v _
    exact Nat.le_refl 1
  obtain ⟨first, hpos, hstop, hbefore, hfrontier⟩ :=
    exists_least_honestHMaxBeforeIndex_crossing S del (Nat.zero_le stop)
      (hzero.trans hH) hcross
  exact ⟨first, hstop, hpos, hfrontier, fun i hi => hbefore i (Nat.zero_le i) hi⟩

/-- Every earlier honest row of the crossing height was sent at local
`h_max = H`. The row need not be recent and need not be a target row. -/
theorem FirstHeightProgressAt.action_hMax
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {H : Height} {first : Nat} (hfirst : FirstHeightProgressAt S rho H first)
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    (hi : i < first) (ha : a.val_index ∈ rho.honest)
    (hevent : rho.events[i]? = some (Event.tick a.val_index ta))
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (hrow : a.height_pair.erase.height? = some H) :
    (actionStoreAt S rho a.val_index a.round).st.core.h_max = H := by
  have hselector := honestEmittedHeightRow_exactFGSelectorWitness
    S adm ha hemit hrow
  let D : NamedBlock V := Classical.choose hselector
  have hselectorD := Classical.choose_spec hselector
  let J : Block V := Classical.choose hselectorD
  have hselectorDJ := Classical.choose_spec hselectorD
  have htime : ta = S.a a.round := hselectorDJ.1
  have hDmem : D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies :=
    hselectorDJ.2.2.2.1
  have hDheight :
      ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = H :=
    hselectorDJ.2.2.2.2.1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho a.val_index a.round).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a a.round)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a a.round) a.val_index).1
  have hDcore : D.erase ∈
      (actionStoreAt S rho a.val_index a.round).st.core.T := by
    rw [hinv.1.1.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hDmem
  have hlower : H ≤ (actionStoreAt S rho a.val_index a.round).h_max := by
    have hbound := treeHeightsLeHMax_actionStore S adm a.val_index a.round
      D.erase hDcore
    rwa [hDheight] at hbound
  have hsame : (actionStoreAt S rho a.val_index a.round).st.core.h_max =
      (rho.stateBefore S i a.val_index).st.h_max := by
    rw [Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent, htime]
    rfl
  have hupper : (actionStoreAt S rho a.val_index a.round).st.core.h_max ≤ H := by
    rw [hsame]
    exact (localHMax_le_honestHMaxBeforeIndex S rho i ha).trans (hfirst.before i hi)
  exact Nat.le_antisymm hupper hlower




theorem fgConfirmationWitness_compatible_sgVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {T : Block V}
    (hwitness : fgConfirmationWitness S (actionStoreAt S rho v r) = some T) :
    Block.compatible (actionSGBlockAt S rho v r) T = true := by
  let n := actionReadAt S rho v r
  let st := n.st.core.toHealing
  let gc := NamedProfile.gradeContract n.cache
  have hk : S.hc.round_of st.s = r := by
    have ht := NamedActionSources.action_timing S
      (NamedRun.stateBeforeTime S rho (S.a r) v) r
    simpa only [n, actionReadAt, st] using ht.2.2
  obtain ⟨Cfg, hsource, hT⟩ := Option.map_eq_some_iff.mp hwitness
  have hsource' : Protocol.fg_source_with gc S.E S.hc st r
      (Protocol.grade2_block_with gc S.E S.hc st r) = some Cfg := by
    simpa only [actionStoreAt, actionFGSource, n, st, gc, hk] using hsource
  obtain ⟨Q, hQ⟩ : ∃ Q, Protocol.grade2_block_with gc S.E S.hc st r = some Q := by
    cases hgrade : Protocol.grade2_block_with gc S.E S.hc st r with
    | none =>
        exact False.elim (by
          simpa [Protocol.fg_source_with, hgrade] using hsource')
    | some Q => exact ⟨Q, rfl⟩
  have hQA : Block.preceq Q
      (DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r).anchor = true := by
    have hQaction : DecoupledConsensusModel.Protocol.grade2Block n.st.core.toHealing
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) = some Q := by
      simpa only [gc, NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
        Protocol.grade2_block_with, DecoupledConsensusModel.Protocol.frameGradeRead] using hQ
    have hQcheck :
        DecoupledConsensusModel.Protocol.grade2Block
          (Internal.NamedJointOutage.checkpoint S rho v r).st.core.toHealing
          (DecoupledConsensusModel.Protocol.readFrame
            (Internal.NamedJointOutage.checkpoint S rho v r).cache
            (Internal.NamedJointOutage.checkpoint S rho v r).st.core.toHealing r) =
          some Q := by
      change DecoupledConsensusModel.Protocol.grade2Block n.st.core.toHealing
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) = some Q
      exact hQaction
    have hpre := NamedOutageClosure.grade2_preceq_anchor_at_checkpoint
      S rho adm.toNamedAdmissibleCore v hv 0 r
      ⟨hr, Proofs.HealingLemmas.a_nonneg S r, hhor⟩ Q hQcheck
    simpa only [Internal.NamedJointOutage.checkpoint, n, st,
      actionRead_readFrame_eq_checkpoint S rho v r] using hpre
  have hsg := frame_sg_vote_preceq_source S n r hQ hQA hsource'
  have hTCfg : Block.preceq T Cfg = true := by
    have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st := by
      apply Proofs.NamedConfirmationMembership.invariant_update
      exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st := hinv.1.1
    have hCfgMem : Cfg ∈ n.st.core.T := by
      apply NamedActionSources.frame_fg_source_mem S n.cache n.st r hinv
      simpa only [gc, st] using hsource'
    rw [hcoh.1] at hCfgMem
    obtain ⟨D, hD, hErase⟩ := Finset.mem_image.mp hCfgMem
    have hsourceD : actionFGSource S n = some D.erase := by
      have hsourceN : actionFGSource S n = some Cfg := by
        simpa only [n, actionStoreAt] using hsource
      rw [← hErase] at hsourceN
      exact hsourceN
    have hcheckpoint := fgConfirmationWitness_checkpoint S
      (hagree := hcoh.2.2.2.2) hD hsourceD (by
        simpa only [n, actionStoreAt] using hwitness)
    rw [← hcheckpoint, ← hErase]
    exact Proofs.NamedEntryHeight.entry_geometry_ancestor S.E S.cfg D
  simpa only [actionSGBlockAt, actionStoreAt, n, st, gc, hk] using
    Block.compatible_of_preceq_common hsg hTCfg

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
