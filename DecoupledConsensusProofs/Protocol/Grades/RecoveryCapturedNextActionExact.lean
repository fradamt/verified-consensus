module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingBoundaryCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Exact captured next-action carrier

The action store's fresh grade batch is aligned to `Can`, while the common
live confirmation may be a descendant `D` of that endpoint. The alignment
can therefore be transported to `D`; strict honest-weight majority then
clears `D`. If the store's fresh anchor is below `Can`, the exact Section 7
SG selector's clear walk returns that same live confirmation.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem prepared_deepest_clear_eq_tip
    {floor : Option (Block V)} {C : Block V} {test : Block V → Bool}
    (hfloor : floor.elim True (fun a => Block.preceq a C = true))
    (htest : test C = true) :
    Protocol.deepest_clear floor C test = some C := by
  have hmem : C ∈ Protocol.chain_of C := by
    cases C with
    | genesis => simp [Protocol.chain_of, Protocol.chain_up, Block.depth]
    | node p s root gv gsv ats i =>
        simp [Protocol.chain_of, Protocol.chain_up, Block.depth, Block.parent?]
  have hsome : (Protocol.deepest_clear floor C test).isSome = true :=
    deepest_clear_isSome_of_mem hfloor hmem htest
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
  have hCmem : C ∈ (Protocol.chain_of C).toFinset.filter (fun B =>
      floor.elim true (fun anchor => Block.preceq anchor B) = true ∧
        test B = true) := by
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, ?_, htest⟩
    cases floor with
    | none => rfl
    | some a => simpa using hfloor
  have hLC : Block.Preceq L C := Proofs.Engine.deepest_clear_preceq hL
  have hCL : Block.Preceq C L := by
    refine Proofs.HealingLemmas.deepest?_dominates hL hCmem ?_
    exact Block.compatible_of_preceq_common (Block.preceq_self C) hLC
  have hEq : L = C := Block.preceq_antisymm hLC hCL
  simpa [hEq] using hL

/-- An exact action SG carrier equals its live confirmation when the prepared
action frame is aligned, its anchor is below the endpoint, and the frame clears
the live confirmation. -/
theorem actionSGBlockAt_eq_liveConfirmed_of_batchAligned
    (S : Setup V) {rho : Run V} {v : V} {r : Round}
    {Can D A : Block V}
    (hconfirmed : (actionStoreAt S rho v r).st.core.live_confirmed = D)
    (hbatch : let n := actionReadAt S rho v r
      BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F
        rho.honest r (allPhasesCutoff S.E S.hc r) Can)
    (hCanD : Block.Preceq Can D)
    (hanchor : nodeAnchor S (actionReadAt S rho v r) r = A)
    (hACan : Block.Preceq A Can)
    (hclear : nodeClear S (actionReadAt S rho v r) r D = true) :
    actionSGBlockAt S rho v r = D := by
  let ast := actionStoreAt S rho v r
  have _hbatch := hbatch
  have hconfirmed' : ast.st.core.live_confirmed = D := by
    simpa only [ast] using hconfirmed
  have hanchor' : nodeAnchor S ast r = A := by
    simpa only [ast, actionStoreAt] using hanchor
  have hclear' : nodeClear S ast r D = true := by
    simpa only [ast, actionStoreAt] using hclear
  have hanchorLive : Block.Preceq (nodeAnchor S ast r)
      ast.st.core.live_confirmed := by
    rw [hanchor', hconfirmed']
    exact Block.preceq_trans hACan hCanD
  have hclearLive : nodeClear S ast r ast.st.core.live_confirmed = true := by
    rw [hconfirmed']
    exact hclear'
  have hwalk : Protocol.deepest_clear (some (nodeAnchor S ast r))
      ast.st.core.toHealing.live_confirmed
      (nodeClear S ast r) = some ast.st.core.live_confirmed :=
    prepared_deepest_clear_eq_tip (by simpa using hanchorLive) hclearLive
  have hround : S.hc.round_of ast.st.core.toHealing.s = r := by
    simpa only [ast, Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  change Protocol.get_sg_vote_with (NamedProfile.gradeContract ast.cache)
      S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.st.core.toHealing.s)
      (Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache)
        S.E S.hc ast.st.core.toHealing
        (S.hc.round_of ast.st.core.toHealing.s)) = D
  rw [hround]
  unfold Protocol.get_sg_vote_with NamedProfile.gradeContract
    DecoupledConsensusModel.Protocol.frameContract
  change Protocol.currentSGVote ast.st.core.toHealing
      { nodeRead S ast r with Q2 := nodeQ2 S ast r } = D
  letI := (nodeRead S ast r).rawG2_decidable
  unfold Protocol.currentSGVote
  change (match Protocol.deepest_clear (some (nodeAnchor S ast r))
      ast.st.core.toHealing.live_confirmed (nodeClear S ast r) with
    | some B => B
    | none =>
      match nodeQ2 S ast r with
      | some B => B
      | none =>
        if (nodeRead S ast r).rawG2 then
          Protocol.get_fg_root ast.st.core.toHealing.toFG
        else nodeAnchor S ast r) = D
  rw [hwalk, hconfirmed']

#print axioms actionSGBlockAt_eq_liveConfirmed_of_batchAligned




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
