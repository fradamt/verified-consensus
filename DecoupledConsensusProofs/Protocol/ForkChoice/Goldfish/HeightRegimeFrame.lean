module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryCrossingCore
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryPrefix
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Grades.LegacyVocabulary
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison

@[expose] public section

/-!
# The height regime frame

The checkpoint-protection chain of the recovery height uses the
nonjustifiable predecessor through two facts only (plan section 44): every
honest finalized block in the prefix is below every run block at or above
the predecessor height, and every honest FG root in the prefix is below
every store block at the source height. At the recovery height both follow
from the finality cap and the gap; one height up they follow from the
previous regime, whose justified block is its checkpoint. This file states
the two facts as `FinalityFloorAt` and `HeightRegimeFrame`, proves the
recovery-height instances, and gives the generic forms of the chain's
leaves.

`FinalityFloorAt` and `HeightRegimeFrame.rootBelow` range over the named
store. The finality-floor witness is a `NamedBlock` reached through
`RunBlock` (`NamedRun.blockInRun`), and its height and finality fields use
`Protocol.derive_named`.
`HeightRegimeFrame.rootBelow`'s raw-tree witness stays an erased `Block`
(`FGForkChoice` still computes over `Store.T`/`Store.σ`), but its height
premise is the store's own cached chain state (`st.σ Q`, an invariant
clause of `Proofs.NamedStore.Coherent`'s `DerivedView`) rather than a recomputation
through `derived_state`, which 1636 retired as agreeing with the real
(named) computation only on timeout-free chains. See the closing note for
the one declaration this leaves at a Open.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A raw exact-height block at an honest event-prefix read forces that local
maximum to the unique height allowed by the finite public frontier. The
height premise reads the store's own cached chain state at `Q`, which is
`Protocol.derive_named` on the named body behind it
(`Proofs.NamedStore.Coherent`'s `DerivedView` clause, exported as
`Proofs.NamedStoreBridge.derivedView_stateBefore`) — not the retired `derived_state`
recomputation. -/
theorem localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho)
    {stop : Nat} {blocked : Height}
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {n : Nat} {reader : V} {Q : Block V}
    (hreader : reader ∈ rho.honest) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (rho.stateBefore S n reader).st.T)
    (hQheight : ((rho.stateBefore S n reader).st.σ Q).h = blocked + 1) :
    (rho.stateBefore S n reader).st.h_max = blocked + 1 := by
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n reader hQmem
  have hagree : (rho.stateBefore S n reader).st.core.σ Q =
      Protocol.derive_named S.E S.cfg D := by
    rw [← hDerase]
    exact Proofs.NamedStoreBridge.derivedView_stateBefore S rho n reader D hDmem
  have hQle : blocked + 1 ≤ (rho.stateBefore S n reader).st.h_max := by
    have hbound := Proofs.NamedStoreBridge.heights_le_hMax_stateBefore S rho n reader D hDmem
    rw [← hagree, hQheight] at hbound
    exact hbound
  have hfrontierN : honestHMaxBeforeIndex S rho n < blocked + 2 :=
    (honestHMaxBeforeIndex_mono S rho hnstop).trans_lt hfrontier
  have hfrontierNle : honestHMaxBeforeIndex S rho n ≤ blocked + 1 := by
    apply Nat.lt_succ_iff.mp
    simpa only [Nat.add_assoc] using hfrontierN
  have hupper : (rho.stateBefore S n reader).st.h_max ≤ blocked + 1 :=
    (localHMax_le_honestHMaxBeforeIndex S rho n hreader).trans hfrontierNle
  exact Nat.le_antisymm hupper hQle


/-- **The finality floor** at predecessor height `blocked` over the event
prefix `stop`, relative to a previous checkpoint `Tprev`: every honest
finalized block is below every run block at height at least `blocked` that
extends `Tprev`. The witness is a `NamedBlock` (`RunBlock` cannot take
an erased witness), read through `derive_named`; the finalized/`Tprev`
comparisons stay over erased blocks (`ChainState`'s own fields), so the
witness is compared through its `.erase`. -/
def FinalityFloorAt (S : Setup V) (rho : Run V) (blocked : Height) (stop : Nat)
    (Tprev : Block V) : Prop :=
  ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ stop →
    ∀ X : NamedBlock V, RunBlock S rho X →
      blocked ≤ (Protocol.derive_named S.E S.cfg X).h →
    Block.Preceq Tprev X.erase → Block.Preceq (rho.stateBefore S n v).st.F X.erase

/-- **The height regime frame** relative to a previous checkpoint `Tprev` of
height at most `blocked` and a round bound `c0`: the finality floor; honest
FG roots below every store block at height `blocked + 1` that extends
`Tprev`; every honest FG source at height `blocked + 1` in the prefix
extends `Tprev`. Grade-1 compatibility follows from the exact FG source
and is not a frame premise. The round parameter is retained for the
regime interface. At the recovery height `Tprev` is genesis. -/
structure HeightRegimeFrame
    (S : Setup V) (rho : Run V) (blocked : Height) (stop : Nat) (Tprev : Block V)
    (c0 : Round) : Prop where
  floor : FinalityFloorAt S rho blocked stop Tprev
  prevHeight : (derived_state S.E S.cfg Tprev).h ≤ blocked
  rootBelow : ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ stop →
    ∀ Q ∈ (rho.stateBefore S n v).st.T, ((rho.stateBefore S n v).st.σ Q).h = blocked + 1 →
    Block.Preceq Tprev Q →
    Block.Preceq (Protocol.get_fg_root (rho.stateBefore S n v).st.toHealing.toFG) Q
  sourceAbove : ∀ p ∈ rho.honest, ∀ r : Round, strictEventIndex rho (S.a r) ≤ stop →
    S.a r ≤ rho.horizon → ∀ B : Block V,
    Protocol.fg_source S.E S.hc (actionStoreAt S rho p r).toHealing r
      (Protocol.grade2_block S.E S.hc (actionStoreAt S rho p r).toHealing r) = some B →
    (derived_state S.E S.cfg B).h = blocked + 1 → Block.Preceq Tprev B
  namedSourceAbove : ∀ p ∈ rho.honest, ∀ r : Round,
    strictEventIndex rho (S.a r) ≤ stop → S.a r ≤ rho.horizon →
    ∀ B : NamedBlock V,
      B ∈ (actionStoreAt S rho p r).st.bodies →
      actionFGSource S (actionStoreAt S rho p r) = some B.erase →
      (Protocol.derive_named S.E S.cfg B).h = blocked + 1 →
      Block.Preceq Tprev B.erase

/-! ## Additive named-predecessor frame

`HeightRegimeFrame` above is the established erased interface. Keep it
unchanged while the named consumers move to the record below. The named
predecessor is retained through the frame, so its run membership and
`derive_named` height are available without reconstructing either from an
erased block.

The two derivations are not interchangeable in general: a named timeout row
can fail the entry match while its erased timeout row still contributes to
`derived_state`. The conversion to the erased frame therefore takes the
erased predecessor-height fact explicitly. -/




/-- Named-predecessor twin of `HeightRegimeFrame`. The other frame clauses
retain their established erased geometry, with the named predecessor erased
only at those relation boundaries. -/
structure HeightRegimeFrameN
    (S : Setup V) (rho : Run V) (blocked : Height) (stop : Nat)
    (Tprev : NamedBlock V) (c0 : Round) : Prop where
  floor : FinalityFloorAt S rho blocked stop Tprev.erase
  prevRun : RunBlock S rho Tprev
  prevHeight : (Protocol.derive_named S.E S.cfg Tprev).h ≤ blocked
  rootBelow : ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ stop →
    ∀ Q ∈ (rho.stateBefore S n v).st.T, ((rho.stateBefore S n v).st.σ Q).h = blocked + 1 →
    Block.Preceq Tprev.erase Q →
    Block.Preceq (Protocol.get_fg_root (rho.stateBefore S n v).st.toHealing.toFG) Q
  sourceAbove : ∀ p ∈ rho.honest, ∀ r : Round, strictEventIndex rho (S.a r) ≤ stop →
    S.a r ≤ rho.horizon → ∀ B : Block V,
    Protocol.fg_source S.E S.hc (actionStoreAt S rho p r).toHealing r
      (Protocol.grade2_block S.E S.hc (actionStoreAt S rho p r).toHealing r) = some B →
    (derived_state S.E S.cfg B).h = blocked + 1 → Block.Preceq Tprev.erase B
  namedSourceAbove : ∀ p ∈ rho.honest, ∀ r : Round,
    strictEventIndex rho (S.a r) ≤ stop → S.a r ≤ rho.horizon →
    ∀ B : NamedBlock V,
      B ∈ (actionStoreAt S rho p r).st.bodies →
      actionFGSource S (actionStoreAt S rho p r) = some B.erase →
      (Protocol.derive_named S.E S.cfg B).h = blocked + 1 →
      Block.Preceq Tprev.erase B.erase

/-- Restrict a named frame to a shorter event prefix. -/
theorem HeightRegimeFrameN.mono {S : Setup V} {rho : Run V} {blocked : Height}
    {stop stop' : Nat} {Tprev : NamedBlock V} {c0 : Round}
  (h : HeightRegimeFrameN S rho blocked stop Tprev c0) (hle : stop' ≤ stop) :
  HeightRegimeFrameN S rho blocked stop' Tprev c0 :=
  ⟨(fun v hv n hn => h.floor v hv n (hn.trans hle)), h.prevRun, h.prevHeight,
    fun v hv n hn => h.rootBelow v hv n (hn.trans hle),
    fun p hp r hr => h.sourceAbove p hp r (hr.trans hle),
    fun p hp r hr => h.namedSourceAbove p hp r (hr.trans hle)⟩

/-- Erase a named frame. The explicit height fact is required because the
named and erased derivations differ on mismatched timeout entries. -/
theorem HeightRegimeFrameN.toErased
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat}
    {Tprev : NamedBlock V} {c0 : Round}
    (h : HeightRegimeFrameN S rho blocked stop Tprev c0)
    (hprevHeight : (derived_state S.E S.cfg Tprev.erase).h ≤ blocked) :
    HeightRegimeFrame S rho blocked stop Tprev.erase c0 :=
  ⟨h.floor, hprevHeight,
    h.rootBelow, h.sourceAbove, h.namedSourceAbove⟩

/-- Build the named frame under a named predecessor witness for an established
erased frame. The witness supplies the full run object and its named height;
the erasure equality aligns the remaining geometric clauses. -/
theorem HeightRegimeFrame.toNamed
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat}
    {Tprev : Block V} {c0 : Round}
    (h : HeightRegimeFrame S rho blocked stop Tprev c0)
    (TprevN : NamedBlock V) (hTprev : TprevN.erase = Tprev)
    (hprevRun : RunBlock S rho TprevN)
    (hprevHeight : (Protocol.derive_named S.E S.cfg TprevN).h ≤ blocked) :
    HeightRegimeFrameN S rho blocked stop TprevN c0 := by
  subst Tprev
  exact ⟨h.floor, hprevRun, hprevHeight, h.rootBelow, h.sourceAbove,
    h.namedSourceAbove⟩

#print axioms HeightRegimeFrame.toNamed

/-- The floor restricts to shorter prefixes. -/
theorem FinalityFloorAt.mono {S : Setup V} {rho : Run V} {blocked : Height}
    {stop stop' : Nat} {Tprev : Block V}
    (h : FinalityFloorAt S rho blocked stop Tprev) (hle : stop' ≤ stop) :
    FinalityFloorAt S rho blocked stop' Tprev :=
  fun v hv n hn => h v hv n (hn.trans hle)

/-- The frame restricts to shorter prefixes. -/
theorem HeightRegimeFrame.mono {S : Setup V} {rho : Run V} {blocked : Height}
    {stop stop' : Nat} {Tprev : Block V} {c0 : Round}
    (h : HeightRegimeFrame S rho blocked stop Tprev c0) (hle : stop' ≤ stop) :
    HeightRegimeFrame S rho blocked stop' Tprev c0 :=
  ⟨h.floor.mono hle, h.prevHeight,
    fun v hv n hn => h.rootBelow v hv n (hn.trans hle),
    fun p hp r hr => h.sourceAbove p hp r (hr.trans hle),
    fun p hp r hr => h.namedSourceAbove p hp r (hr.trans hle)⟩


/-- **The recovery-height floor.** The finality cap places every honest
finalized block strictly below `blocked`. The finalized carrier at the
event prefix is the named witness `NamedProvenanceBridge` (`Proofs.Bridges.
storeFinalizationOnChain_stateBefore`) supplies, carried to `stop` by
`NamedBodyRetention.stateBefore_bodies_mono`; the crossing comparison and the
E1/E2 separation are the named twin `NamedFinalizationBridge.
finalized_preceq_of_height_lt` ( 1636). -/
theorem finalityFloorAt_of_recovery
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked) :
    FinalityFloorAt S rho blocked stop Block.genesis := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  intro v hv n hn X hX hXh _
  obtain ⟨D, hDbodies, hDF, -⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho n v
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDbodies
  have hDstop : D ∈ (rho.stateBefore S stop v).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho v hn hDbodies
  have hcapD : (Protocol.derive_named S.E S.cfg D).h_F ≤ hF0 := hcap v hv D hDstop
  have hcrossed : (Protocol.derive_named S.E S.cfg D).h_F <
      (Protocol.derive_named S.E S.cfg X).h :=
    (hcapD.trans_lt ((Nat.lt_succ_self hF0).trans
      (NjGap.lt_of_recoveryHeight hrec))).trans_le hXh
  have hpre : Block.Preceq (Protocol.derive_named S.E S.cfg D).F X.erase :=
    NamedFinalizationBridge.finalized_preceq_of_height_lt S rho X D hsb
      adm.toNamedRootCollisionFree hX hDrun hcrossed
  simpa only [hDF] using hpre

/-! The recovery constructor uses the named NJ universe already produced by
`RecoveryPrefixRun`. -/
theorem heightRegimeFrame_of_recovery
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2) :
    HeightRegimeFrame S rho blocked stop Block.genesis 0 := by
  have hfloor := finalityFloorAt_of_recovery S adm hbelow hcap hrec
  refine ⟨hfloor, ?_, ?_,
    fun _ _ _ _ _ B _ _ => Protocol.preceq_genesis B,
    fun _ _ _ _ _ B _ _ _ => Protocol.preceq_genesis B.erase⟩
  · change 1 ≤ blocked
    exact Nat.succ_le_of_lt ((Nat.zero_le (hF0 + 1)).trans_lt
      (NjGap.lt_of_recoveryHeight hrec))
  intro v hv n hn Q hQ hQh _
  have hmax : (rho.stateBefore S n v).st.core.h_max = blocked + 1 :=
    localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
      S adm hfrontier hv hn hQ hQh
  have hcapN : HonestPrefixFinalityCap S rho n hF0 :=
    honestPrefixFinalityCap_of_le S adm.toNamedScheduleWellFormed hn hcap
  have huniverse : HonestPrefixNJUniverse S rho n blocked :=
    honestPrefixNJUniverse_of_finalityCap S adm.toNamedDeliveryWellFormed hcapN hrec
  have hne : (rho.stateBefore S n v).st.core.h_j ≠ blocked := by
    obtain ⟨D, hD, hJ, hJh⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBefore S rho n v
    have hneD := (huniverse v hv D hD).2
    intro heq
    apply hneD
    exact hJh.trans heq
  have hgate : ¬ (rho.stateBefore S n v).st.core.h_max =
      (rho.stateBefore S n v).st.core.h_j + 1 := by
    intro hgate
    apply hne
    exact (Nat.add_right_cancel (hmax.symm.trans hgate)).symm
  simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
  obtain ⟨D, hD, hErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hQ
  have hDview := Proofs.NamedStoreBridge.derivedView_stateBefore S rho n v D hD
  have hDheight : (Protocol.derive_named S.E S.cfg D).h = blocked + 1 := by
    rw [← hDview]
    rw [hErase]
    exact hQh
  have hfloorD := hfloor v hv n hn D
    (Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD)
    (hDheight ▸ Nat.le_succ blocked) (Protocol.preceq_genesis D.erase)
  simpa only [hErase] using hfloorD

/-! ## The chain's leaves from the floor and the frame -/

/-- Honest finalized blocks are below every run block at the source height. -/
theorem FinalityFloorAt.storeF_preceq_sourceHeightBlock
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat} {Tprev : Block V}
    (h : FinalityFloorAt S rho blocked stop Tprev)
    {n : Nat} {reader : V} (hreader : reader ∈ rho.honest)
    (hnstop : n ≤ stop) {P : NamedBlock V}
    (hPrun : RunBlock S rho P)
    (hPheight : (Protocol.derive_named S.E S.cfg P).h = blocked + 1)
    (hTP : Block.Preceq Tprev P.erase) :
    Block.Preceq (rho.stateBefore S n reader).st.F P.erase :=
  h reader hreader n hnstop P hPrun (hPheight ▸ Nat.le_succ blocked) hTP

/-- At a delivery inside the prefix, the reader's finalized block is below
every run block at or above the predecessor height. -/
theorem FinalityFloorAt.finalizedPreceq_at_delivery
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat} {Tprev : Block V}
    (h : FinalityFloorAt S rho blocked stop Tprev) (adm : Admissible S rho)
    {P : NamedBlock V} (hPrun : RunBlock S rho P)
    (hPheight : blocked ≤ (Protocol.derive_named S.E S.cfg P).h)
    (hTP : Block.Preceq Tprev P.erase)
    {Gamma : Time} (hGammaPrefix : strictEventIndex rho Gamma ≤ stop)
    {reader : V} (hreader : reader ∈ rho.honest)
    {i : Nat} {X : NamedBlock V} {t : Time}
    (hevent : rho.events[i]? = some (Event.deliver reader (Object.block X) t))
    (ht : t < Gamma) :
    Block.Preceq (rho.stateBefore S i reader).st.F P.erase := by
  have hiGamma : i < strictEventIndex rho Gamma := by
    by_contra hnot
    have hGammaLe : Gamma ≤ (Event.deliver reader (Object.block X) t).time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver reader (Object.block X) t)
        (Nat.le_of_not_gt hnot) hevent
    have hGammaLeT : Gamma ≤ t := by
      simpa only [Event.time] using hGammaLe
    exact (not_le_of_gt ht) hGammaLeT
  exact h reader hreader i (hiGamma.trans_le hGammaPrefix).le P hPrun hPheight hTP

/-- A block at the source height that extends `Tprev` is above `Tprev`'s
ancestors at lower heights: `Tprev` itself is below the source checkpoint. -/
theorem HeightRegimeFrame.prev_preceq_of_height
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat} {Tprev : Block V}
    {c0 : Round} (h : HeightRegimeFrame S rho blocked stop Tprev c0)
    {T Q : Block V} (hTQ : Block.Preceq T Q) (hprevQ : Block.Preceq Tprev Q)
    (hTh : (derived_state S.E S.cfg T).h = blocked + 1) :
    Block.Preceq Tprev T := by
  rcases Block.preceq_linear hprevQ hTQ with hpt | htp
  · exact hpt
  · exfalso
    have hmono := Protocol.derived_h_mono S.E S.cfg htp
    rw [hTh] at hmono
    exact Nat.not_succ_le_self blocked (hmono.trans h.prevHeight)

/-- A store block at the source height is retained in the honest reader's
finality-filtered tree, and the root is below it. The height premise reads
the store's own cached chain state, matching `HeightRegimeFrame.rootBelow`
and `localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier`. -/
theorem HeightRegimeFrame.fgRoot_preceq_and_filteredMem
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat} {Tprev : Block V}
    {c0 : Round} (h : HeightRegimeFrame S rho blocked stop Tprev c0) (adm : Admissible S rho)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {n : Nat} {reader : V} {Q : Block V}
    (hreader : reader ∈ rho.honest) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (rho.stateBefore S n reader).st.T)
    (hQheight : ((rho.stateBefore S n reader).st.σ Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q) :
    Block.Preceq (Protocol.get_fg_root
      (rho.stateBefore S n reader).st.toHealing.toFG) Q ∧
      Q ∈ Protocol.get_filtered_block_tree
        (rho.stateBefore S n reader).st.toHealing.toFG := by
  have hmax : (rho.stateBefore S n reader).st.h_max = blocked + 1 :=
    localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
      S adm hfrontier hreader hnstop hQmem hQheight
  have hrootQ := h.rootBelow reader hreader n hnstop Q hQmem hQheight hTQ
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n reader hQmem
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hDmem
  have hagree : (rho.stateBefore S n reader).st.core.σ Q =
      Protocol.derive_named S.E S.cfg D := by
    rw [← hDerase]
    exact Proofs.NamedStoreBridge.derivedView_stateBefore S rho n reader D hDmem
  have hDheight : (Protocol.derive_named S.E S.cfg D).h = blocked + 1 := by
    rw [← hagree]; exact hQheight
  have hTD : Block.Preceq Tprev D.erase := hDerase ▸ hTQ
  have hFQ : Block.Preceq (rho.stateBefore S n reader).st.F Q := by
    have := h.floor.storeF_preceq_sourceHeightBlock hreader hnstop hDrun hDheight hTD
    rwa [hDerase] at this
  have hV : Q ∈ Protocol.V_tree
      (rho.stateBefore S n reader).st.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hQmem, hFQ⟩, Q, hQmem, Block.preceq_self _, ?_⟩
    have hmax' : (rho.stateBefore S n reader).st.core.h_max = blocked + 1 := hmax
    rw [hmax', hQheight]
    exact Nat.sub_le _ _
  exact ⟨hrootQ, Proofs.Records.mem_filtered_of_mem_V_tree hV hrootQ⟩

/-- Named-predecessor twin of the frame's root/filter export. -/
theorem HeightRegimeFrameN.fgRoot_preceq_and_filteredMem
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat}
    {Tprev : NamedBlock V} {c0 : Round}
    (h : HeightRegimeFrameN S rho blocked stop Tprev c0) (adm : Admissible S rho)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {n : Nat} {reader : V} {Q : Block V}
    (hreader : reader ∈ rho.honest) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (rho.stateBefore S n reader).st.T)
    (hQheight : ((rho.stateBefore S n reader).st.σ Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev.erase Q) :
    Block.Preceq (Protocol.get_fg_root
      (rho.stateBefore S n reader).st.toHealing.toFG) Q ∧
      Q ∈ Protocol.get_filtered_block_tree
        (rho.stateBefore S n reader).st.toHealing.toFG := by
  have hmax : (rho.stateBefore S n reader).st.h_max = blocked + 1 :=
    localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
      S adm hfrontier hreader hnstop hQmem hQheight
  have hrootQ := h.rootBelow reader hreader n hnstop Q hQmem hQheight hTQ
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n reader hQmem
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hDmem
  have hagree : (rho.stateBefore S n reader).st.core.σ Q =
      Protocol.derive_named S.E S.cfg D := by
    rw [← hDerase]
    exact Proofs.NamedStoreBridge.derivedView_stateBefore S rho n reader D hDmem
  have hDheight : (Protocol.derive_named S.E S.cfg D).h = blocked + 1 := by
    rw [← hagree]
    exact hQheight
  have hTD : Block.Preceq Tprev.erase D.erase := hDerase ▸ hTQ
  have hFQ : Block.Preceq (rho.stateBefore S n reader).st.F Q := by
    have := h.floor.storeF_preceq_sourceHeightBlock hreader hnstop hDrun hDheight hTD
    rwa [hDerase] at this
  have hV : Q ∈ Protocol.V_tree
      (rho.stateBefore S n reader).st.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hQmem, hFQ⟩, Q, hQmem, Block.preceq_self _, ?_⟩
    have hmax' : (rho.stateBefore S n reader).st.core.h_max = blocked + 1 := hmax
    rw [hmax', hQheight]
    exact Nat.sub_le _ _
  exact ⟨hrootQ, Proofs.Records.mem_filtered_of_mem_V_tree hV hrootQ⟩



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
