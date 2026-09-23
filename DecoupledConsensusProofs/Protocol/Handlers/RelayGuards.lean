module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ReceiptCalls
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.BodyRetention
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusInternal.Execution.NamedAdmissible

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedRelayGuards
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem rows_bodies (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st a) rows).bodies = _
    rw [ih, NamedAdmission.admit_row_bodies]

private theorem on_block_with_bodies (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).bodies =
      (Protocol.NamedStore.process_block_core E hc cfg st B).bodies := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_bodies hc _ B.attestations
  · rfl

omit [Fintype V] in
private theorem commitBlock_self_bodies (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock st st.core B).bodies = st.bodies := by
  unfold Protocol.NamedStore.commitBlock
  split
  · rename_i h
    exact False.elim (h.1 h.2)
  · rfl

/-- A fresh full body in the result of its checked named handler passed all
three immutable guards. The outer exact-parent guard is irrelevant here: if
it rejects, the post-membership contradicts freshness. -/
private theorem new_body_guards (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).bodies) :
    B.erase.slot ≤ st.core.s ∧
      B.erase.proposer? = some (E.proposer B.erase.slot) ∧
      B.erase.parent.slot < B.erase.slot ∧
      Protocol.carried_attestations_admissible hc B.erase = true := by
  rw [on_block_with_bodies] at hpost
  unfold Protocol.NamedStore.process_block_core at hpost
  by_cases hp : B.parent ∈ st.bodies
  · simp only [hp, not_true_eq_false, if_false] at hpost
    by_cases ha : Protocol.carried_attestations_admissible hc B.erase = true
    · simp only [Protocol.on_block_checked_using, ha, if_true] at hpost
      by_cases hfirst : st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
          B.erase.parent ∉ st.core.T
      · simp only [Protocol.on_block_using, hfirst, if_true,
          commitBlock_self_bodies] at hpost
        exact False.elim (hpre hpost)
      · by_cases hfinal : (!Block.preceq st.core.F B.erase) = true
        · simp only [Protocol.on_block_using, hfirst, if_false, hfinal, if_true,
            commitBlock_self_bodies] at hpost
          exact False.elim (hpre hpost)
        · have hfinalFalse : (!Block.preceq st.core.F B.erase) = false :=
            Bool.eq_false_of_not_eq_true hfinal
          by_cases hproposer :
            B.erase.proposer? ≠ some (E.proposer B.erase.slot)
          · simp [Protocol.on_block_using, hfirst, hfinalFalse,
              hproposer, commitBlock_self_bodies] at hpost
            exact False.elim (hpre hpost)
          · by_cases hparent : ¬ B.erase.parent.slot < B.erase.slot
            · simp [Protocol.on_block_using, hfirst, hfinalFalse,
                hproposer, hparent, commitBlock_self_bodies] at hpost
              exact False.elim (hpre hpost)
            · exact ⟨Nat.le_of_not_gt (fun h => hfirst (Or.inl h)),
                not_not.mp hproposer, not_not.mp hparent, ha⟩
    · have haf : Protocol.carried_attestations_admissible hc B.erase = false :=
        Bool.eq_false_of_not_eq_true ha
      simp only [Protocol.on_block_checked_using, haf, Bool.false_eq_true,
        if_false, commitBlock_self_bodies] at hpost
      exact False.elim (hpre hpost)
  · simp only [hp] at hpost
    exact False.elim (hpre hpost)

private theorem attest_bodies (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.bodies = st.bodies :=
  NamedAdmission.admit_row_bodies hc st _

/-- The final store of a tick has the proposal-stage body set. -/
private theorem tick_bodies_eq_proposal_stage (gc : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    let s := E.slotOf t
    let st0 := Protocol.NamedStore.setClock E st t
    let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
    let st1 := if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
      then proposed.1 else st0
    (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies = st1.bodies := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let due := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
  let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
  let st1 := if due then proposed.1 else st0
  let emitted1 : List (NamedObject V) := if due then
    match proposed.2 with | none => [] | some C => [.block C]
    else []
  let voteDue := 0 < s ∧ t = Protocol.vote_time E s
  let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
  let st2 := if voteDue then voted.1 else st1
  let emitted2 : List (NamedObject V) :=
    if voteDue then voted.2.toList.map NamedObject.gfVote else []
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have h32 : st3.bodies = st1.bodies := by
    dsimp only [st3, st2]
    split_ifs <;> rfl
  have hout := NamedTick.tick_computed_duties gc E hc cfg nd st record t
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      let a := Protocol.NamedDuties.attest_with gc E hc nd st3 record
      (a.1, a.2.1, emitted1 ++ emitted2 ++ [.attest a.2.2])
    else (st3, record, emitted1 ++ emitted2)) at hout
  change (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies = st1.bodies
  rw [hout]
  split_ifs
  · rw [attest_bodies, h32]
  · exact h32

private theorem emitted_block_due (gc : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) (B : NamedBlock V)
    (hB : NamedObject.block B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2) :
    0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
      E.proposer (E.slotOf t) = nd.val_index := by
  by_contra hnot
  rw [NamedTick.tick_computed_duties] at hB
  dsimp only at hB
  simp only [if_neg hnot] at hB
  split_ifs at hB <;>
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, or_false, and_false, exists_false] at hB

/-- Retain the actual accepting handler input privately, including its slot.
The public static query exports only the three frozen immutable facts. -/
private theorem accepted_block_call_guards (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {B : NamedBlock V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) ta) :
    ∃ before : Protocol.NamedStore V,
      Execution.NamedReceiptCalls.blockCallAt S rho i v B before ∧
      B.erase.slot ≤ before.core.s ∧
      B.erase.proposer? = some (S.E.proposer B.erase.slot) ∧
      B.erase.parent.slot < B.erase.slot ∧
      Protocol.carried_attestations_admissible S.hc B.erase = true := by
  have hpre : B ∉ (NamedRun.stateBefore S rho i v).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hacc.2.1
  have hpost : B ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  rcases hacc.1.1 with ⟨t, htick, hB⟩ | ⟨t, hdeliver⟩
  · rw [Proofs.NamedRuntime.stateBefore_tick S rho htick] at hpost
    let n := NamedRun.stateBefore S rho i v
    let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
    let st0 := Protocol.NamedStore.setClock S.E n.st t
    have hpre0 : B ∉ st0.bodies := by
      simpa only [st0, Protocol.NamedStore.setClock] using hpre
    have heq := Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hB
    have heqStore := congrArg Prod.fst heq
    have hdue := emitted_block_due (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) n.st n.record t B hB
    have hstage := tick_bodies_eq_proposal_stage (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) n.st n.record t
    change B ∈ (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) n.st n.record t).1.bodies at hpost
    have hpost0 : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried
        S.E S.hc S.cfg st0 B).bodies := by
      rw [hstage] at hpost
      simp only [if_pos hdue] at hpost
      rw [heqStore] at hpost
      exact hpost
    exact ⟨st0, Proofs.NamedReceiptCallsBase.blockCallAt_self S rho htick hB,
      new_body_guards S.E S.hc S.cfg st0 B hpre0 hpost0⟩
  · rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver] at hpost
    exact ⟨(NamedRun.stateBefore S rho i v).st,
      Proofs.NamedReceiptCallsBase.blockCallAt_delivery S rho hdeliver,
      new_body_guards S.E S.hc S.cfg _ B hpre hpost⟩

theorem accepted_block_static_guards (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {B : NamedBlock V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) ta) :
    B.erase.proposer? = some (S.E.proposer B.erase.slot) ∧
    B.erase.parent.slot < B.erase.slot ∧
    Protocol.carried_attestations_admissible S.hc B.erase = true := by
  obtain ⟨_, _, _, hstatic⟩ := accepted_block_call_guards S rho hacc
  exact hstatic

/-- The event identity in a full actual-handles witness determines its time. -/
private theorem handle_time_of_event (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time} {e : NamedEvent V}
    (hcall : NamedRun.actualHandlesAt S rho i v (.block B) t)
    (he : rho.events[i]? = some e) : e.time = t := by
  obtain ⟨original, horiginal, _, ht⟩ := hcall.2
  have heq : e = original := Option.some.inj (he.symm.trans horiginal)
  exact (congrArg NamedEvent.time heq).trans ht

/-- Slot and clock stay linked in the one actual named fold. Delivery
preserves both fields; no delivery-time clock assignment is introduced. -/
private theorem stateBefore_slot_clock (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) :
    (NamedRun.stateBefore S rho i v).st.core.s =
      S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t := by
  induction i with
  | zero =>
    simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, Protocol.Store.init, Env.slotOf, slotOfTime]
  | succ i ih =>
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[i]? with
    | none => simpa only [Option.toList_none, List.foldl_nil] using ih
    | some e =>
      change (NamedWorld.step S (NamedRun.stateBefore S rho i) e v).st.core.s =
        S.E.slotOf (NamedWorld.step S (NamedRun.stateBefore S rho i) e v).st.core.t
      by_cases hv : e.node = v
      · cases e with
        | tick u t =>
          change u = v at hv
          subst u
          rw [Proofs.NamedRuntime.step_tick]
          rw [(Proofs.NamedNode.tick_clock S v _ t).1, (Proofs.NamedNode.tick_clock S v _ t).2]
        | deliver u o t =>
          change u = v at hv
          subst u
          rw [Proofs.NamedRuntime.step_deliver]
          rw [(Proofs.NamedNode.process_clock S _ o).1, (Proofs.NamedNode.process_clock S _ o).2]
          exact ih
      · rw [Proofs.NamedRuntime.step_other S _ e v (Ne.symm hv)]
        exact ih

private theorem stateBefore_time_nonneg (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (i : Nat) (v : V) :
    0 ≤ (NamedRun.stateBefore S rho i v).st.core.t := by
  have h := Proofs.NamedRuntime.stateBefore_clock_mono S rho sch.sorted
    (fun e he => (sch.in_horizon e he).1) v (Nat.zero_le i)
  exact h

/-- A source acceptance passed its actual future-slot guard. Its time is
therefore at or after the accepted block's proposal instant. -/
private theorem proposal_time_le_acceptance (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    {i : Nat} {v : V} {B : NamedBlock V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) ta) :
    Protocol.proposal_time S.E B.erase.slot ≤ ta := by
  obtain ⟨before, hcall, hslot, _⟩ := accepted_block_call_guards S rho hacc
  rcases hcall with ⟨t, hdeliver, rfl⟩ | ⟨t, htick, _, rfl⟩
  · have ht : t = ta := handle_time_of_event S rho hacc.1 hdeliver
    have htime := Proofs.NamedRuntime.stateBefore_clock_le_event S rho sch.sorted hdeliver
      (sch.in_horizon _ (List.mem_of_getElem? hdeliver)).1 v
    have hs := stateBefore_slot_clock S rho i v
    rw [hs] at hslot
    exact (Protocol.proposal_time_mono S.E hslot).trans
      ((Protocol.proposal_time_slotOf_le S.E (stateBefore_time_nonneg S rho sch i v)).trans
        (htime.trans ht.le))
  · have ht : t = ta := handle_time_of_event S rho hacc.1 htick
    have hnonneg : 0 ≤ t := (sch.in_horizon _ (List.mem_of_getElem? htick)).1
    exact (Protocol.proposal_time_mono S.E hslot).trans
      ((Protocol.proposal_time_slotOf_le S.E hnonneg).trans ht.le)

omit [Fintype V] in
private theorem named_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

private theorem no_geometry_alias (S : Setup V) (rho : NamedRun V)
    (roots : NamedRootCollisionFree S rho) (i : Nat) (v : V)
    (hv : v ∈ rho.honest) (B : NamedBlock V) (hB : NamedRun.blockInRun S rho B)
    (hnot : B ∉ (NamedRun.stateBefore S rho i v).st.bodies) :
    B.erase ∉ (NamedRun.stateBefore S rho i v).st.core.T := by
  intro hgeom
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
  rw [hcoh.1] at hgeom
  obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hgeom
  have hCscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hC)
  have hroot : C.root = B.root :=
    (Proofs.NamedWire.erase_root C).symm.trans ((congrArg Block.root he).trans (Proofs.NamedWire.erase_root B))
  have hCB : C = B := roots.root_injective C B hCscope hB C B
    (Or.inl (named_self C)) (Or.inr (named_self B)) hroot
  exact hnot (by simpa only [hCB] using hC)

/-- The receiver's public proposal tick occurs before a delivery at or
after that time. Lexicographic phase order includes the same-time case. -/
private theorem receiver_slot_at_delivery (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    {j : Nat} {receiver : V} {B : NamedBlock V} {td : Time}
    (hdeliver : rho.events[j]? = some (.deliver receiver (.block B) td))
    (hlo : Protocol.proposal_time S.E B.erase.slot ≤ td) :
    B.erase.slot ≤ (NamedRun.stateBefore S rho j receiver).st.core.s := by
  have hmem := List.mem_of_getElem? hdeliver
  have hhon : receiver ∈ rho.honest := sch.honest_only _ hmem
  let p := Protocol.proposal_time S.E B.erase.slot
  have hpt : p ≤ td := hlo
  have htick : NamedEvent.tick receiver p ∈ rho.events :=
    sch.tick_total receiver hhon p (Proofs.Optimistic.publicTime_proposal_time S B.erase.slot)
      (Proofs.Optimistic.proposal_time_nonneg S.E B.erase.slot)
      (hlo.trans (sch.in_horizon _ hmem).2)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp htick
  have hkj : k < j := by
    by_contra hnot
    have hjk : j ≤ k := Nat.le_of_not_gt hnot
    obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hdeliver
    have hne : j ≠ k := by
      intro heq
      subst k
      rw [hdeliver] at hk
      cases hk
    have hkey := (List.pairwise_iff_getElem.mp sch.sorted) j k hjLen hkLen
      (lt_of_le_of_ne hjk hne)
    rw [hjGet, hkGet] at hkey
    have hbad : ¬ NamedEvent.key (NamedEvent.deliver receiver (.block B) td) ≤
        NamedEvent.key (NamedEvent.tick receiver p) := by
      dsimp only [p] at hpt ⊢
      simp only [NamedEvent.key, NamedEvent.time, NamedEvent.phase, Prod.Lex.le_iff]
      intro h
      rcases h with hlt | ⟨heq, hphase⟩
      · exact (not_lt_of_ge hpt) hlt
      · norm_num at hphase
    exact hbad hkey
  have hclock := Proofs.NamedRuntime.tick_time_le_clock S rho sch.sorted
    (fun e he => (sch.in_horizon e he).1) hk hkj
  rw [stateBefore_slot_clock S rho j receiver]
  exact Protocol.slot_le_slotOf_of_proposal_time_le S.E hclock

/-- With the actual named parent, no alias, and all checked-core guards,
the handler inserts exactly this full block. The carried tail keeps bodies. -/
private theorem handler_inserts (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hp : B.parent ∈ st.bodies) (hfresh : B.erase ∉ st.core.T)
    (hslot : B.erase.slot ≤ st.core.s) (hF : Block.Preceq st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparent : B.erase.parent.slot < B.erase.slot)
    (hcarried : Protocol.carried_attestations_admissible S.hc B.erase = true) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  have hparentTree : B.erase.parent ∈ st.core.T := by
    rw [Proofs.NamedWire.erase_parent, hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hp
  have hfirst : ¬ (st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
      B.erase.parent ∉ st.core.T) := by
    simp only [not_or]
    exact ⟨Nat.not_lt.mpr hslot, hfresh, not_not.mpr hparentTree⟩
  have hfinal : (!Block.preceq st.core.F B.erase) = false := by rw [hF]; rfl
  have hafter : B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase).T := by
    simp [Protocol.on_block_checked_using, hcarried,
      Protocol.on_block_using, hfirst, hfinal, hproposer, hparent,
      Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T S.E]
  rw [on_block_with_bodies]
  unfold Protocol.NamedStore.process_block_core
  rw [if_neg (not_not.mpr hp)]
  unfold Protocol.NamedStore.commitBlock
  rw [if_pos ⟨hfresh, hafter⟩]
  exact Finset.mem_insert_self _ _

private theorem proposal_of_result (gc : Protocol.GradeContract V) (S : Setup V)
    (v : V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hout : (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st).2 = some B) :
    Protocol.NamedActions.proposal_with gc .poolAndCarried S.E S.hc (S.node v) st = some B := by
  unfold Protocol.NamedDuties.propose_block_with at hout
  cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried S.E S.hc (S.node v) st with
  | none => simp only [hp, reduceCtorEq] at hout
  | some C =>
    rw [hp] at hout
    have hCB : C = B := Option.some.inj hout
    exact congrArg some hCB

theorem handled_block_held_of_finalized_prefix (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    (delivery : NamedDeliveryWellFormed S rho)
    (roots : NamedRootCollisionFree S rho)
    {i j : Nat} {source receiver : V} {B : NamedBlock V} {ta td : Time}
    (hacc : NamedRun.acceptsAt S rho i source (.block B) ta)
    (hcall : NamedRun.actualHandlesAt S rho j receiver (.block B) td)
    (htime : ta ≤ td)
    (hF : Block.Preceq (NamedRun.stateBefore S rho j receiver).st.core.F B.erase) :
    B ∈ (NamedRun.stateBefore S rho (j + 1) receiver).st.bodies := by
  by_cases hheld : B ∈ (NamedRun.stateBefore S rho j receiver).st.bodies
  · exact NamedBodyRetention.stateBefore_bodies_mono S rho receiver (Nat.le_succ j) hheld
  have hreceiver : receiver ∈ rho.honest := by
    obtain ⟨e, he, hnode, _⟩ := hcall.2
    have hh := sch.honest_only e (List.mem_of_getElem? he)
    simpa only [hnode] using hh
  have hsource : source ∈ rho.honest := by
    obtain ⟨e, he, hnode, _⟩ := hacc.1.2
    have hh := sch.honest_only e (List.mem_of_getElem? he)
    simpa only [hnode] using hh
  have haccepted : B ∈ (NamedRun.stateBefore S rho (i + 1) source).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  have hscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hsource (i + 1) haccepted)
  have hfresh := no_geometry_alias S rho roots j receiver hreceiver B hscope hheld
  obtain ⟨hproposer, hparent, hcarried⟩ := accepted_block_static_guards S rho hacc
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j receiver).1.1.1
  rcases hcall.1 with ⟨t, htick, hB⟩ | ⟨t, hdeliver⟩
  · let n := NamedRun.stateBefore S rho j receiver
    let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
    let st0 := Protocol.NamedStore.setClock S.E n.st t
    have heq := Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hB
    have heqStore := congrArg Prod.fst heq
    have hresult : (Protocol.NamedDuties.propose_block_with (DecoupledConsensusModel.Protocol.frameContract c)
        S.E S.hc S.cfg (S.node receiver) st0).2 = some B := congrArg Prod.snd heq
    have hproposal := proposal_of_result (DecoupledConsensusModel.Protocol.frameContract c)
      S receiver st0 B hresult
    have hpayload := Proofs.NamedActions.proposal_payload (DecoupledConsensusModel.Protocol.frameContract c)
      .poolAndCarried S.E S.hc (S.node receiver) st0 B hproposal
    have hslotB : B.slot = st0.core.s := hpayload.2.2.1
    have hslot : B.erase.slot ≤ st0.core.s := by rw [Proofs.NamedWire.erase_slot, hslotB]
    have hnew := handler_inserts S st0 B
      (NamedStore.coherent_clock S.E S.cfg n.st t hcoh) hpayload.1 hfresh hslot
      hF hproposer hparent hcarried
    have hdue := emitted_block_due (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node receiver) n.st n.record t B hB
    rw [Proofs.NamedRuntime.stateBefore_tick S rho htick]
    change B ∈ (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node receiver) n.st n.record t).1.bodies
    rw [tick_bodies_eq_proposal_stage]
    simp only [if_pos hdue]
    rw [heqStore]
    exact hnew
  · have ht : t = td := handle_time_of_event S rho hcall hdeliver
    subst t
    have hparentHeld : B.parent ∈ (NamedRun.stateBefore S rho j receiver).st.bodies :=
      (DecoupledConsensusModel.Proofs.NamedReceipt.depsPresent_block_iff _ B).mp
        (delivery.deps j receiver (.block B) td hdeliver)
    have hproposalTime : Protocol.proposal_time S.E B.erase.slot ≤ td :=
      (proposal_time_le_acceptance S rho sch hacc).trans htime
    have hslot := receiver_slot_at_delivery S rho sch hdeliver hproposalTime
    rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver]
    exact handler_inserts S _ B hcoh hparentHeld hfresh hslot hF hproposer hparent hcarried

end DecoupledConsensusModel.Proofs.NamedRelayGuards

end
