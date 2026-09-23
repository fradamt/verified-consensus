module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.PublicCutBody
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.Handlers.AdoptionConstructor

@[expose] public section

/-!
# Frozen processed-tree closure under core admissibility

Receipt stamps and actual acceptance times agree at public cutoffs.
Admission carries all ancestors into the processed tree. The current-proposal
arm is ancestor closed by its definition. No participation or fault bound
is needed for these local execution facts.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution
open Proofs.Optimistic Protocol
open Protocol.HonestWeightMajority
  (on_block_new_timestamp on_tick_emit_proposal_timestamp_block)

variable {V : Type} [DecidableEq V] [Fintype V]



/-! ## Named processed-tree ancestor closure -/

theorem ancestorProcessed_of_voterProcessed
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {B : Block V}
    (hBmem : B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s) :
    ∀ C : Block V, Block.Preceq C B →
      C ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have sch : ScheduleWellFormed S rho := AdmissibleCore.toScheduleWellFormed adm
  have hprocessed : B ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := hBmem
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  intro C hCB
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hprocessed ⊢
  rw [hslot, Nat.add_sub_cancel] at hprocessed ⊢
  rcases hprocessed with ⟨hBT, hstamp | ⟨P, hP, hBP⟩⟩
  · have hBTtime : B ∈
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hBT
    have hstampTime : stampedBefore
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) B = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hstamp
    obtain ⟨Bn, hBn, hBnErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w hBTtime
    have hstampBn : stampedBefore
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) Bn.erase = true := by
      simpa only [hBnErase] using hstampTime
    have hBnFreeze :=
      NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore S rho
        sch (publicTime_view_freeze S s) hBn hstampBn
    have hcohFreeze := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.view_freeze S.E s) w).1.1.1
    have hBfreeze : B ∈
        (rho.stateBeforeTime S (Protocol.view_freeze S.E s) w).st.core.T := by
      rw [hcohFreeze.1]
      exact Finset.mem_image.mpr ⟨Bn, hBnFreeze, hBnErase⟩
    have hCfreeze : C ∈
        (rho.stateBeforeTime S (Protocol.view_freeze S.E s) w).st.core.T := by
      exact Proofs.Records.mem_of_preceq
        ((parentClosed_iff _).mp
          (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (Protocol.view_freeze S.E s) w)).2 C B hBfreeze hCB
    obtain ⟨Cn, hCn, hCnErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.view_freeze S.E s) w hCfreeze
    have hCnStamp := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
      S rho sch w (Protocol.view_freeze S.E s) Cn hCn
    have hcarry := NamedOutageClosure.q10_strict_body_carry S rho
      sch w (le_of_lt (view_freeze_lt_vote_time_succ S.E s)) hCn
    have hCtreeTime : C ∈
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
      have hcohDuty := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E (s + 1)) w).1.1.1
      rw [hcohDuty.1]
      exact Finset.mem_image.mpr ⟨Cn, hcarry.1, hCnErase⟩
    have hCtree : C ∈ duty.T := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hCtreeTime
    have hCstampTime : stampedBefore
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) C = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hCnStamp ⊢
      rw [← hCnErase, hcarry.2]
      exact hCnStamp
    have hCstamp : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.view_freeze S.E s) C = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hCstampTime
    exact ⟨by simpa only [Protocol.Store.toHealing] using hCtree,
      Or.inl hCstamp⟩
  · have hPT : P ∈ duty.T := by
      simpa only [Protocol.Store.toHealing] using hP.1
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w
    have hCP : Block.Preceq C P := Block.preceq_trans hCB hBP
    have hCT : C ∈ duty.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 C P hPT hCP
    exact ⟨by simpa only [Protocol.Store.toHealing] using hCT,
      Or.inr ⟨P, hP, hCP⟩⟩

/-! ## Named timing and admitted-before wrappers -/


/-- A named admitted block carries all its ancestors to a later read, with the
same timestamp cutoff. -/
theorem admittedBefore_ancestor_mem_and_stamp_at
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {A H : Block V} {Gamma Gamma' : Time}
    (hadmit : Protocol.AdmittedBefore S rho v H Gamma)
    (hAH : Block.Preceq A H) (hle : Gamma ≤ Gamma') :
    A ∈ (rho.storeBeforeTime S v Gamma').T ∧
      stampedBefore (rho.storeBeforeTime S v Gamma').timestamp_block Gamma A = true :=
  Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at S adm hadmit hAH hle

/-

/-- A pre-cutoff block receipt stamp bounds the actual acceptance time. -/
theorem acceptsAt_block_lt_of_stamp_before
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    {v: V} (hv: v ∈ rho.honest) {i n: Nat}
    {B: Block V} {t Gamma: Time}
    (hacc: rho.acceptsAt S i v (Object.block B) t)
    (hin: i + 1 ≤ n) (hpub: PublicTime S Gamma)
    (hstamp: stampedBefore
      (rho.stateBefore S n v).st.timestamp_block Gamma B = true):
    t < Gamma:= by
  have hcarry: BlockCarry (rho.stateBefore S (i + 1) v).st
      (rho.stateBefore S n v).st:=
    block_carry S adm.toScheduleWellFormed v n hin
  have hattestations:
      Protocol.carried_attestations_admissible S.hc B = true:=
    carried_attestations_admissible_of_acceptsAt_block S hacc
  obtain ⟨hhandle, hpreProcessed, hpostProcessed⟩:= hacc
  obtain ⟨hindex, e, he, hnode, htime⟩:= hhandle
  simp only [Run.handlesAtIndex] at hindex
  rcases hindex with htick | hdeliver
  · obtain ⟨t', htick, hem⟩:= htick
    have heq: Event.tick v t' = e:= Option.some.inj (htick.symm.trans he)
    have htt: t' = t:= (congrArg Event.time heq).trans htime
    subst t'
    have heTick: rho.events[i]? = some (Event.tick v t):= htick
    let pre:= (rho.stateBefore S i v).st
    obtain ⟨hguard, hBeq⟩:= Proofs.HealingSurface.block_mem_on_tick_emit S
      (S.node v) pre (rho.stateBefore S i v).Λ t hem
    let k:= S.E.slotOf t
    have hBeq': B =
        (Protocol.propose_block S.E S.hc S.cfg (S.node v)
          { pre with t:= t, s:= k }).2:= by
      simpa only [k] using hBeq
    have htProposal: t = Protocol.proposal_time S.E k:= hguard.2.1
    have hprop: S.E.proposer k = (S.node v).val_index:= hguard.2.2
    have hfieldsT:= on_tick_emit_proposal_fields S (S.node v) pre
      (rho.stateBefore S i v).Λ k hguard.1 hprop
    rw [← htProposal] at hfieldsT
    have hfieldsStamp:= on_tick_emit_proposal_timestamp_block S (S.node v) pre
      (rho.stateBefore S i v).Λ k hguard.1 hprop
    rw [← htProposal] at hfieldsStamp
    have hfieldsT':
        (on_tick_emit S (S.node v) pre (rho.stateBefore S i v).Λ t).1.T =
          (Protocol.propose_block S.E S.hc S.cfg (S.node v)
            { pre with t:= t, s:= k }).1.T:= by
      simpa only [Proofs.Optimistic.tickStore, k] using hfieldsT.1
    have hfieldsStamp':
        (on_tick_emit S (S.node v) pre (rho.stateBefore S i v).Λ t).1.timestamp_block =
          (Protocol.propose_block S.E S.hc S.cfg (S.node v)
            { pre with t:= t, s:= k }).1.timestamp_block:= by
      simpa only [Proofs.Optimistic.tickStore, k] using hfieldsStamp
    have hstate: (rho.stateBefore S (i + 1) v).st =
        (on_tick_emit S (S.node v) pre (rho.stateBefore S i v).Λ t).1:= by
      unfold pre Run.stateBefore
      rw [List.take_add_one, heTick, List.foldl_append]
      simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
        Function.update_self]
    have hBpre: B ∉ ({ pre with t:= t, s:= k }: Protocol.Store V).T:= by
      simpa only [Object.processed, decide_eq_false_iff_not, pre] using
        hpreProcessed
    have hBout: B ∈
        (on_tick_emit S (S.node v) pre (rho.stateBefore S i v).Λ t).1.T:= by
      rw [← hstate]
      simpa only [Object.processed, decide_eq_true_eq] using hpostProcessed
    have hBstage: B ∈
        (Protocol.propose_block S.E S.hc S.cfg (S.node v)
          { pre with t:= t, s:= k }).1.T:= by
      rw [← hfieldsT']
      exact hBout
    have hBonBlockChecked: B ∈
        (Protocol.on_block_checked S.E S.hc S.cfg
          ({ pre with t:= t, s:= k }: Protocol.Store V) B).T:= by
      rw [hBeq'] at hBstage ⊢
      simpa only [Protocol.propose_block] using hBstage
    have hBonBlock: B ∈
        (Protocol.on_block S.E S.cfg
          ({ pre with t:= t, s:= k }: Protocol.Store V) B).T:= by
      rw [← on_block_checked_eq_on_block_of_admissible
        S.E S.hc S.cfg ({ pre with t:= t, s:= k }: Protocol.Store V)
          B hattestations]
      exact hBonBlockChecked
    have hstageStamp:= on_block_new_timestamp S.E S.cfg
      ({ pre with t:= t, s:= k }: Protocol.Store V) B hBpre hBonBlock
    have hproposedStamp:
        (Protocol.propose_block S.E S.hc S.cfg (S.node v)
          { pre with t:= t, s:= k }).1.timestamp_block B = some (t: Stamp):= by
      calc
        (Protocol.propose_block S.E S.hc S.cfg (S.node v)
          { pre with t:= t, s:= k }).1.timestamp_block B =
            (Protocol.on_block_checked S.E S.hc S.cfg
              ({ pre with t:= t, s:= k }: Protocol.Store V) B).timestamp_block B:= by
          rw [hBeq']
          rfl
        _ = (Protocol.on_block S.E S.cfg
              ({ pre with t:= t, s:= k }: Protocol.Store V) B).timestamp_block B:= by
          rw [on_block_checked_eq_on_block_of_admissible
            S.E S.hc S.cfg ({ pre with t:= t, s:= k }: Protocol.Store V)
              B hattestations]
        _ = some (t: Stamp):= hstageStamp
    have hpostStamp:
        (rho.stateBefore S (i + 1) v).st.timestamp_block B = some (t: Stamp):= by
      rw [hstate, hfieldsStamp']
      exact hproposedStamp
    have hfinalStamp:
        (rho.stateBefore S n v).st.timestamp_block B = some (t: Stamp):=
      hcarry.stamp B _ hpostStamp
    simp only [stampedBefore, hfinalStamp, decide_eq_true_eq] at hstamp
    exact WithBot.coe_lt_coe.mp hstamp
  · obtain ⟨t', hdeliver⟩:= hdeliver
    have heq: Event.deliver v (.block B) t' = e:=
      Option.some.inj (hdeliver.symm.trans he)
    have htt: t' = t:= (congrArg Event.time heq).trans htime
    subst t'
    have hi: rho.events[i]? = some (Event.deliver v (.block B) t):= by
      simpa [heq] using he
    let pre:= (rho.stateBefore S i v).st
    have hstate: (rho.stateBefore S (i + 1) v).st =
        Protocol.on_block_checked S.E S.hc S.cfg pre B:= by
      unfold pre Run.stateBefore
      rw [List.take_add_one, hi, List.foldl_append]
      simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
        Function.update_self, NodeState.process]
    have hBpre: B ∉ pre.T:= by
      simpa only [Object.processed, decide_eq_false_iff_not] using hpreProcessed
    have hBpostChecked: B ∈
        (Protocol.on_block_checked S.E S.hc S.cfg pre B).T:= by
      rw [← hstate]
      simpa only [Object.processed, decide_eq_true_eq] using hpostProcessed
    have hBpost: B ∈ (Protocol.on_block S.E S.cfg pre B).T:= by
      rw [← on_block_checked_eq_on_block_of_admissible
        S.E S.hc S.cfg pre B hattestations]
      exact hBpostChecked
    have hstateRaw: (rho.stateBefore S (i + 1) v).st =
        Protocol.on_block S.E S.cfg pre B:= by
      calc
        (rho.stateBefore S (i + 1) v).st =
            Protocol.on_block_checked S.E S.hc S.cfg pre B:= hstate
        _ = Protocol.on_block S.E S.cfg pre B:=
          on_block_checked_eq_on_block_of_admissible
            S.E S.hc S.cfg pre B hattestations
    have hpostStamp:
        (rho.stateBefore S (i + 1) v).st.timestamp_block B =
          some (pre.t: Stamp):= by
      rw [hstateRaw]
      exact on_block_new_timestamp S.E S.cfg pre B hBpre hBpost
    have hfinalStamp:
        (rho.stateBefore S n v).st.timestamp_block B = some (pre.t: Stamp):=
      hcarry.stamp B _ hpostStamp
    have hclock: pre.t < Gamma:= by
      simp only [stampedBefore, hfinalStamp, decide_eq_true_eq] at hstamp
      exact WithBot.coe_lt_coe.mp hstamp
    exact processed_lt_of_store_time_lt S adm.toScheduleWellFormed hv hi hpub
      (by simpa only [pre] using hclock)

/-- Admission preserves membership and pre-cutoff stamps for all ancestors. -/
theorem admittedBefore_ancestor_mem_and_stamp_at
    (S: Setup V) {ρ: Run V} (adm: AdmissibleCore S ρ)
    {v: V} {A H: Block V} {Γ Γ': Time}
    (hadmit: AdmittedBefore S ρ v H Γ)
    (hAH: Block.Preceq A H) (hle: Γ ≤ Γ'):
    A ∈ (ρ.storeBeforeTime S v Γ').T ∧
      stampedBefore (ρ.storeBeforeTime S v Γ').timestamp_block Γ A = true:= by
  obtain ⟨i, t, hacc, hlt⟩:= hadmit
  obtain ⟨_, ⟨e, he, _, het⟩⟩:= hacc.1
  have hpostH: H ∈ (ρ.stateBefore S (i + 1) v).st.T:= by
    simpa only [Object.processed, decide_eq_true_eq] using hacc.2.2
  have hpc: ParentClosed (ρ.stateBefore S (i + 1) v).st:=
    Proofs.Bridges.parentClosed_of_admissible S adm.toDeliveryWellFormed v (i + 1)
  have hpostA: A ∈ (ρ.stateBefore S (i + 1) v).st.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 A H hpostH hAH
  let N:= (ρ.events.filter (fun x => decide (x.time < Γ'))).length
  have hiN: i < N:= by
    by_contra hnot
    have hNle: N ≤ i:= Nat.le_of_not_gt hnot
    have hΓ'e: Γ' ≤ e.time:=
      Proofs.Optimistic.le_time_of_index_ge S adm.toScheduleWellFormed
        (t:= Γ') (j:= i) (e:= e) (by simpa [N] using hNle) he
    rw [het] at hΓ'e
    exact (not_le_of_gt (lt_of_lt_of_le hlt hle)) hΓ'e
  have hcarry: BlockCarry (ρ.stateBefore S (i + 1) v).st
      (ρ.stateBefore S N v).st:=
    block_carry S adm.toScheduleWellFormed v N (Nat.succ_le_of_lt hiN)
  have hsource: BlockStamps (ρ.stateBefore S (i + 1) v).st:=
    blockStamps_stateBefore S adm.toScheduleWellFormed v (i + 1)
  obtain ⟨c, hc⟩: ∃ c: Stamp,
      (ρ.stateBefore S (i + 1) v).st.timestamp_block A = some c:=
    Option.isSome_iff_exists.mp (hsource.stamped A hpostA)
  have hcfinal: (ρ.stateBefore S N v).st.timestamp_block A = some c:=
    hcarry.stamp A c hc
  have hclock: (ρ.stateBefore S (i + 1) v).st.t ≤ t:= by
    have ht:= block_store_time_after_event_le
      S adm.toScheduleWellFormed he v
    simpa only [het] using ht
  have hcΓ: c < (Γ: Stamp):=
    lt_of_le_of_lt
      (le_trans (hsource.bounded A c hc) (WithBot.coe_le_coe.mpr hclock))
      (WithBot.coe_lt_coe.mpr hlt)
  have hstore: ρ.storeBeforeTime S v Γ' = (ρ.stateBefore S N v).st:= by
    rw [Run.storeBeforeTime,
      Proofs.Optimistic.stateBeforeTime_eq_take S adm.toScheduleWellFormed Γ']
  rw [hstore]
  refine ⟨hcarry.mem A hpostA, ?_⟩
  simp only [stampedBefore, hcfinal, decide_eq_true_eq]
  exact hcΓ

/-- The frozen processed domain is ancestor closed. -/
theorem ancestorProcessed_of_voterProcessed
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    {w: V} (hw: w ∈ rho.honest) {s: Slot} {B: Block V}
    (hBmem: B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s):
    ∀ C: Block V, Block.Preceq C B →
      C ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s:= by
  let duty:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hBprocessed: B ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s:= hBmem
  have hslot: duty.toHealing.s = s + 1:= by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have hpc: ParentClosed (rho.stateBefore S n w).st:=
    Proofs.Bridges.parentClosed_of_admissible S adm.toDeliveryWellFormed w n
  intro C hCB
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    at hBprocessed ⊢
  rw [hslot, Nat.add_sub_cancel] at hBprocessed ⊢
  rcases hBprocessed with ⟨hBT, hstamp | ⟨P, hP, hBP⟩⟩
  · have hBTn: B ∈ (rho.stateBefore S n w).st.T:= by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hBT
    have hstampn: stampedBefore
        (rho.stateBefore S n w).st.timestamp_block
        (Protocol.view_freeze S.E s) B = true:= by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hstamp
    have hprocessed: (Object.block B).processed
        (rho.stateBefore S n w).st = true:= by
      simpa only [Object.processed, decide_eq_true_eq] using hBTn
    obtain hgen | ⟨i, hin, t, hacc⟩:=
      acceptsAt_block_of_processed S rho w n B hprocessed
    · have hCgen: C = Block.genesis:=
        Block.preceq_antisymm (hgen ▸ hCB) (Protocol.preceq_genesis C)
      subst C
      have hgenesis:= genesis_mem_and_stamp_storeBeforeTime
        S adm.toScheduleWellFormed w
        (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using
            hgenesis.2)⟩
    · have htFreeze: t < Protocol.view_freeze S.E s:=
        acceptsAt_block_lt_of_stamp_before
          S adm hw hacc (Nat.succ_le_of_lt hin)
            (publicTime_view_freeze S s) hstampn
      have hvisibleC:= admittedBefore_ancestor_mem_and_stamp_at
        S adm (show AdmittedBefore S rho w B
          (Protocol.view_freeze S.E s) from ⟨i, t, hacc, htFreeze⟩)
        hCB (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleC.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using
            hvisibleC.2)⟩
  · have hPT: P ∈ duty.T:= by
      simpa only [Protocol.Store.toHealing] using hP.1
    have hPTn: P ∈ (rho.stateBefore S n w).st.T:= by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hPT
    have hCP: Block.Preceq C P:= Block.preceq_trans hCB hBP
    have hCTn: C ∈ (rho.stateBefore S n w).st.T:=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
        C P hPTn hCP
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hCTn,
      Or.inr ⟨P, hP, hCP⟩⟩

-/

#print axioms ancestorProcessed_of_voterProcessed
#print axioms admittedBefore_ancestor_mem_and_stamp_at

end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
