module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBase

@[expose] public section

/-!
# The round frontier of the honest action carriers

With a selected grade-2 block at every honest action store, an honest round-`q`
SG action carrier is below that store's own recorded confirmation, or it is the
store's selected grade-2 block. The two bounds form the *carrier bound set* of
the round.

Every bound is a member of the filtered tree read by its own action, so it has
a processed descendant at the local viability boundary — a run block of height
at least `M - 1`. That witness is what settles the mixed pairs the grade
lemmas do not reach: at a gate-off exact-frontier read the selected FG root is
below every run block of height at least `M - 1`
(`frontierRoot_preceq_of_gateOff`), so a recorded confirmation that fell back
to the root is compatible with every other bound. The genuine pairs are
`sameSlot_genuine_compatible_after_gst`, the grade pairs
`selectedG2_preceq_freshAnchor_of_settled`, and the mixed grade/genuine pairs
`selectedG2_preceq_genuineOpeningConfirmation`.

The bound set is therefore one chain, its deepest element exists, and it
dominates every honest action carrier of the round. This is the
`previousCarriers` field of a first `RoundCeilingBoundaryConeAt`, with no
hypothesis about the FG root beyond gate off: a root that moves inside the
round is already one of the bounds, since a store that falls back to its root
records exactly that root.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Local frontier facts of one action read -/



/-- A prepared frame anchor is active when the corresponding FG root is active. -/
private theorem seedFrameAnchor_mem_filtered
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round)
    (hroot : Protocol.get_fg_root st.toFG ∈
      Protocol.get_filtered_block_tree st.toFG) :
    Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc st r ∈ Protocol.get_filtered_block_tree st.toFG := by
  change DecoupledConsensusModel.Protocol.anchor E hc st r
    (DecoupledConsensusModel.Protocol.readFrame cache st r).g1 ∈
    Protocol.get_filtered_block_tree st.toFG
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame cache st r).g1 with
  | none => exact hroot
  | some opt =>
    cases opt with
    | none => exact hroot
    | some root =>
      cases hactive : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root with
      | none =>
        simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
          Option.getD_none] using hroot
      | some A =>
        simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
          Option.getD_some] using
          (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1

/-- The recorded confirmation of an honest action store is active in that
store. Both selector arms stay inside the filtered tree: the genuine arm is a
walk over it from an active anchor, and the fallback is the FG root. -/
theorem liveConfirmed_mem_filtered_actionStore
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho) (v : V) (r : Round) :
    (actionStoreAt S rho v r).live_confirmed ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG := by
  let pre := rho.storeBeforeTime S v (S.a r)
  let ast := actionStoreAt S rho v r
  let cst := Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)
  let confCache :=
    (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache
  let gc := NamedProfile.gradeContract confCache
  have hrootPre : Protocol.get_fg_root pre.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree pre.core.toHealing.toFG := by
    simpa only [pre, Run.storeBeforeTime] using
      (named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a r) v)
  have hrootAction : Protocol.get_fg_root ast.toHealing.toFG ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG := by
    rw [actionStoreAt_filteredTree S rho v r,
      actionStoreAt_fgRoot_eq_storeBeforeTime S rho v r]
    exact hrootPre
  have hrootConf : Protocol.get_fg_root cst.toHealing.toFG ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG := by
    rw [← actionStoreAt_filteredTree_eq_openingConfStore S rho v r,
      ← actionStoreAt_fgRoot_eq_openingConfStore S rho v r]
    exact hrootAction
  have hanchorConf : Protocol.get_sg_root_with gc S.E S.hc cst.toHealing
        (S.hc.round_of cst.s) ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG :=
    seedFrameAnchor_mem_filtered confCache S.E S.hc cst.toHealing
      (S.hc.round_of cst.s) hrootConf
  have hliveUpdate :
      (Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r)).live_confirmed ∈
        Protocol.get_filtered_block_tree cst.toHealing.toFG := by
    rw [Protocol.update_confirmation_with_live_confirmed]
    split
    · simpa only [Protocol.confWalkWith, Protocol.confAnchorWith,
        Protocol.confTree] using
        (Proofs.Records.ghost_mem_of _ _ hanchorConf (Finset.Subset.refl _))
    · simpa only [Protocol.confRoot] using hrootConf
  have hactionEq : ast.st.core =
      Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r) := by
    change (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r)
    exact actionStoreAt_eq_update_confirmation_confStore S rho v r
  change ast.st.core.live_confirmed ∈
    Protocol.get_filtered_block_tree ast.toHealing.toFG
  rw [hactionEq]
  change (Protocol.update_confirmation_with gc S.E S.hc cst
    (S.hc.opening_slot r)).live_confirmed ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG
  exact hliveUpdate

/-! ## The carrier bound set -/









/-

/-- The carrier bounds of one round lie on a single chain.

The four cases are the two selector arms crossed. A recorded confirmation is
either genuine or the store's own FG root; the genuine pairs are settled by
same-slot confirmation compatibility, the grade pairs by the cross-store grade
transport, the mixed grade/genuine pairs by the transport composed with the
confirmation walk, and every pair with a root fallback by the viability
witness of the other bound. -/
theorem seedCarrierBounds_compatible
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round}
    (hready: GradeRoundReady S rho q)
    (hsettled: SelectedG2SettledAt S rho q)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hhor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some Q)
    (hfrontier: ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a q)).h_max = M)
    (hgate: ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a q)).h_j + 2 ≤ M):
    ∀ X ∈ seedCarrierBounds S rho q, ∀ Y ∈ seedCarrierBounds S rho q,
      Block.compatible X Y = true:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hanchors: ∀ v ∈ rho.honest, ∃ A: Block V,
      Protocol.fresh_anchor S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some A:= by
    intro v hv
    obtain ⟨Q, hQ⟩:= hselected v hv
    exact Option.isSome_iff_exists.mp (fresh_anchor_isSome_of_grade2 S.E hQ)
  -- A grade-2 bound is below every honest fresh anchor of the round.
  have hgradeAnchor: ∀ u ∈ rho.honest, ∀ Q: Block V,
      Protocol.grade2_block S.E S.hc
          (actionStoreAt S rho u q).toHealing q = some Q →
        ∀ v ∈ rho.honest, ∀ A: Block V,
          Protocol.fresh_anchor S.E S.hc
            (actionStoreAt S rho v q).toHealing q = some A →
            Block.Preceq Q A:= by
    intro u hu Q hQ v hv A hA
    exact selectedG2_preceq_freshAnchor_of_settled S adm hready hsettled
      hu hv hQ hA
  intro X hX Y hY
  rcases seedCarrierBounds_cases S rho hX with ⟨u, hu, hXeq⟩ | ⟨u, hu, hXQ⟩
  · rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho u q with
      ⟨D, hD, hDeq⟩ | ⟨R, hReq, hRlive⟩
    · -- `X` is a genuine confirmation of `u`.
      have hXD: X = D:= by rw [hXeq, ← hDeq]
      rcases seedCarrierBounds_cases S rho hY with ⟨v, hv, hYeq⟩ | ⟨v, hv, hYQ⟩
      · rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v q with
          ⟨E, hE, hEeq⟩ | ⟨R', hR'eq, hR'live⟩
        · have hYE: Y = E:= by rw [hYeq, ← hEeq]
          rw [hXD, hYE]
          exact sameSlot_genuine_compatible_after_gst S adm hu hv hpost hhor
            hD hE
        · have hYroot: Y = Protocol.get_fg_root
              (actionStoreAt S rho v q).toHealing.toFG:= by
            rw [hYeq, ← hR'live, hR'eq,
              ← actionStoreAt_fgRoot_eq_openingConfStore S rho v q]
          rw [hYroot]
          exact Protocol.compatible_comm
            (seedRoot_compatible_bound S adm hsb hfrontier hgate hv hX)
      · -- `Y` is a selected grade-2 block: it is below `X`.
        obtain ⟨A, hA⟩:= hanchors u hu
        have hYX: Block.Preceq Y D:=
          selectedG2_preceq_genuineOpeningConfirmation S adm hready hsettled
            hv hu hYQ hA hD
        rw [hXD]
        exact Protocol.compatible_comm
          (Block.compatible_of_preceq_common hYX (Block.preceq_self D))
    · -- `X` fell back to the FG root of `u`.
      have hXroot: X = Protocol.get_fg_root
          (actionStoreAt S rho u q).toHealing.toFG:= by
        rw [hXeq, ← hRlive, hReq,
          ← actionStoreAt_fgRoot_eq_openingConfStore S rho u q]
      rw [hXroot]
      exact seedRoot_compatible_bound S adm hsb hfrontier hgate hu hY
  · -- `X` is a selected grade-2 block.
    rcases seedCarrierBounds_cases S rho hY with ⟨v, hv, hYeq⟩ | ⟨v, hv, hYQ⟩
    · rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v q with
        ⟨E, hE, hEeq⟩ | ⟨R', hR'eq, hR'live⟩
      · have hYE: Y = E:= by rw [hYeq, ← hEeq]
        obtain ⟨A, hA⟩:= hanchors v hv
        have hXE: Block.Preceq X E:=
          selectedG2_preceq_genuineOpeningConfirmation S adm hready hsettled
            hu hv hXQ hA hE
        rw [hYE]
        exact Block.compatible_of_preceq_common hXE (Block.preceq_self E)
      · have hYroot: Y = Protocol.get_fg_root
            (actionStoreAt S rho v q).toHealing.toFG:= by
          rw [hYeq, ← hR'live, hR'eq,
            ← actionStoreAt_fgRoot_eq_openingConfStore S rho v q]
        rw [hYroot]
        exact Protocol.compatible_comm
          (seedRoot_compatible_bound S adm hsb hfrontier hgate hv hX)
    · obtain ⟨A, hA⟩:= hanchors v hv
      exact Block.compatible_of_preceq_common
        (hgradeAnchor u hu X hXQ v hv A hA)
        (hgradeAnchor v hv Y hYQ v hv A hA)

/-- Every honest round-`q` action carrier is below one of the round's carrier
bounds. -/
theorem seedCarrier_preceq_bound
    (S: Setup V) (rho: Run V) {q: Round} {v: V} (hv: v ∈ rho.honest)
    (hselected: ∃ Q: Block V, Protocol.grade2_block S.E S.hc
      (actionStoreAt S rho v q).toHealing q = some Q):
    ∃ X ∈ seedCarrierBounds S rho q,
      Block.Preceq (actionSGBlockAt S rho v q) X:= by
  obtain ⟨Q, hQ⟩:= hselected
  rcases actionSGBlockAt_clear_or_selectedG2 S rho hQ with
    ⟨T, hwalk, hcarrier⟩ | hcarrier
  · refine ⟨(actionStoreAt S rho v q).live_confirmed, ?_, ?_⟩
    · simp only [seedCarrierBounds, Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨v, hv, rfl⟩
    · rw [hcarrier]
      exact Proofs.Engine.deepest_clear_preceq hwalk
  · refine ⟨Q, ?_, ?_⟩
    · simp only [seedCarrierBounds, Finset.mem_union, Finset.mem_biUnion,
        Option.mem_toFinset, Option.mem_def]
      exact Or.inr ⟨v, hv, hQ⟩
    · rw [hcarrier]
      exact Block.preceq_self Q

/-- **The round frontier.** With a selected grade 2 at every honest action
store, one run block of the round dominates every honest action carrier, and it
has a processed run-block descendant at the viability boundary.

No hypothesis about the FG root is used beyond gate off at the action reads: a
store that falls back to its own root contributes that root as its bound, so a
root that moves inside the round is already inside the bound set. -/
theorem exists_seedActionFrontier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round}
    (hready: GradeRoundReady S rho q)
    (hsettled: SelectedG2SettledAt S rho q)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hhor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some Q)
    (hfrontier: ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a q)).h_max = M)
    (hgate: ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a q)).h_j + 2 ≤ M):
    ∃ Cstar ∈ seedCarrierBounds S rho q, RunBlock S rho Cstar ∧
      (∀ v ∈ rho.honest, Block.Preceq (actionSGBlockAt S rho v q) Cstar) ∧
      (∃ W: Block V, RunBlock S rho W ∧ Block.Preceq Cstar W ∧
        M - 1 ≤ (derived_state S.E S.cfg W).h):= by
  have hcompatible:= seedCarrierBounds_compatible S adm hfb hready hsettled
    hpost hhor hselected hfrontier hgate
  have hnonempty: (seedCarrierBounds S rho q).Nonempty:= by
    have hpositive: 0 < ((S.E.committee 0) ∩ rho.honest).card:= by
      have hc:= hcom 0
      omega
    obtain ⟨v, hvmem⟩:= Finset.card_pos.mp hpositive
    have hv: v ∈ rho.honest:= (Finset.mem_inter.mp hvmem).2
    refine ⟨(actionStoreAt S rho v q).live_confirmed, ?_⟩
    simp only [seedCarrierBounds, Finset.mem_union, Finset.mem_image]
    exact Or.inl ⟨v, hv, rfl⟩
  obtain ⟨Cstar, hCstar⟩:= Option.isSome_iff_exists.mp
    (deepest?_isSome_of_compatible hcompatible hnonempty)
  have hCmem: Cstar ∈ seedCarrierBounds S rho q:= Proofs.Engine.deepest?_mem hCstar
  refine ⟨Cstar, hCmem, seedCarrierBounds_runBlock S adm hCmem, ?_,
    seedCarrierBounds_thinWitness S adm hfrontier hCmem⟩
  intro v hv
  obtain ⟨X, hX, hcarrier⟩:= seedCarrier_preceq_bound S rho hv (hselected v hv)
  exact Block.preceq_trans hcarrier
    (deepest?_dominates hCstar hX (hcompatible X hX Cstar hCmem))

end HealingSurface
end Proofs
end DecoupledConsensusModel
-/

/-! ## Named seed frontier -/


namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms liveConfirmed_mem_filtered_actionStore
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
