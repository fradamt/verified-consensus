module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface (ReleasedThrough HonestStoresCrossedAt
  PermanentlyCrossedFrom UnreleasedCertificateStaleFrom)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The bare-store `_using` forms, generalized over the state builder -/

/-- `on_block_using` never lowers `(Σ.h_j, Σ.J.root)`, for any state builder:
the argument is Q5's, unfolded at the shared `on_block_using` core rather than
its `on_block` default instance. -/
private theorem on_block_using_heightId (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    Protocol.HeightId.mk st.h_j st.J.root ≤
      Protocol.HeightId.mk (Protocol.on_block_using E st B buildState).h_j
        (Protocol.on_block_using E st B buildState).J.root := by
  simp only [Protocol.on_block_using]
  split_ifs
  · exact le_refl _
  · exact le_refl _
  · exact le_refl _
  · refine le_trans (le_of_eq ?_) (update_finality_heightId _ _)
    rw [(coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).J_eq,
      (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).h_j_eq]
  · exact le_refl _

omit [DecidableEq V] [Fintype V] in
/-- The checked wrapper either runs the offered handler or leaves the store
unchanged, for any handler already known to advance `(h_j, J.root)`. -/
private theorem on_block_checked_using_heightId (handle : Protocol.Store V → Protocol.Store V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : Protocol.HeightId.mk st.h_j st.J.root ≤
      Protocol.HeightId.mk (handle st).h_j (handle st).J.root) :
    Protocol.HeightId.mk st.h_j st.J.root ≤
      Protocol.HeightId.mk (Protocol.on_block_checked_using handle hc st B).h_j
        (Protocol.on_block_checked_using handle hc st B).J.root := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · exact le_refl _



/-- The named block-processing prefix never lowers `Σ.h_j`: a missing named
parent is a no-op, and a successful check runs the same shared guard as Q5,
generalized to the healing transition's state builder. -/
private theorem process_block_core_h_j_mono (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    st.h_j ≤ (Protocol.NamedStore.process_block_core E hc cfg st B).h_j := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · have hle :
        st.core.h_j ≤
          (Protocol.on_block_checked_using
            (fun current => Protocol.on_block_using E current B.erase
              (fun parentState => Protocol.named_transition E cfg parentState B))
            hc st.core B.erase).h_j :=
      heightId_height_le_of_le
        (on_block_checked_using_heightId _ hc st.core B.erase
          (on_block_using_heightId E st.core B.erase _))
    simp only [Protocol.NamedStore.commitBlock]
    split_ifs <;> exact hle
  · exact le_refl _

omit [Fintype V] in
/-- `admit_row` writes `core` from `on_sg_vote` alone in both branches, so
its `h_j` field is carried, not merely bounded. -/
private theorem admit_row_h_j_mono (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    st.h_j ≤ (Protocol.NamedAdmission.admit_row hc st row).h_j := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact le_of_eq (coreEq_on_sg_vote hc st.core row.erase).h_j_eq.symm

omit [Fintype V] in
private theorem foldl_admit_row_h_j_mono (hc : Protocol.HealConfig)
    (l : List (NamedAttestation V)) (st : Protocol.NamedStore V) :
    st.h_j ≤ (l.foldl (Protocol.NamedAdmission.admit_row hc) st).h_j := by
  induction l generalizing st with
  | nil => exact le_rfl
  | cons row l ih =>
      rw [List.foldl_cons]
      exact (admit_row_h_j_mono hc st row).trans (ih _)

omit [Fintype V] in
private theorem admit_rows_h_j_mono (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    st.h_j ≤ (Protocol.NamedAdmission.admit_rows hc st rows).h_j :=
  foldl_admit_row_h_j_mono hc rows st

omit [Fintype V] in
private theorem admit_carried_h_j_mono (admission : Protocol.CarriedAdmission)
    (hc : Protocol.HealConfig) (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    after.h_j ≤ (Protocol.NamedAdmission.admit_carried admission hc before after B).h_j := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_h_j_mono hc after B.attestations
      · exact le_rfl

/-- The actual F1 tail preserves the core handler's `h_j` advance. -/
private theorem on_block_with_h_j_mono (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    st.h_j ≤ (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).h_j := by
  simp only [Protocol.NamedAdmission.on_block_with]
  exact (process_block_core_h_j_mono E hc cfg st B).trans
    (admit_carried_h_j_mono admission hc st
      (Protocol.NamedStore.process_block_core E hc cfg st B) B)

/-- Either proposal outcome is monotone; a failed lookup changes nothing. -/
private theorem propose_block_with_h_j_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    st.h_j ≤ (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.h_j := by
  simp only [Protocol.NamedDuties.propose_block_with]
  cases Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st with
  | none => exact le_rfl
  | some B => exact on_block_with_h_j_mono .alsoCarried E hc cfg st B

/-- The GF duty writes `core` through `on_goldfish_vote_checked` alone, which
carries `h_j` (Q5's `CoreEq`). -/
private theorem goldfish_vote_with_h_j_eq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.h_j = st.h_j := by
  simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact (coreEq_on_goldfish_vote_checked E st.core _).h_j_eq
  · rfl

/-- The confirmation duty never touches `(σ, F, J, h_j)`. -/
private theorem update_confirmation_with_h_j_eq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc E hc st s).h_j = st.h_j := rfl

/-- The attest duty writes `core` through `admit_row` alone. -/
private theorem attest_with_h_j_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    st.h_j ≤ (Protocol.NamedDuties.attest_with gc E hc nd st record).1.h_j := by
  simp only [Protocol.NamedDuties.attest_with]
  exact admit_row_h_j_mono hc st _

/-- The shared tick scheduler never lowers a per-stage-monotone accessor,
regardless of which duty family it is instantiated with. -/
private theorem scheduler_h_j_mono {State Record BlockOut VoteOut AttOut Out : Type}
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (ops : Protocol.TickScheduler.TickOps State Record BlockOut VoteOut AttOut)
    (blockOut : BlockOut → Out) (voteOut : VoteOut → Out) (attOut : AttOut → Out)
    (hj : State → Height)
    (hclock : ∀ (st : State) (t : Time), hj st ≤ hj (ops.clock st t (E.slotOf t)))
    (hp : ∀ st : State, hj st ≤ hj (ops.proposal st).1)
    (hv : ∀ st : State, hj st ≤ hj (ops.vote st).1)
    (hcfn : ∀ (st : State) (s : Slot), hj st ≤ hj (ops.confirmation st s))
    (ha : ∀ (st : State) (record : Record), hj st ≤ hj (ops.attestation st record).1)
    (st : State) (record : Record) (t : Time) :
    hj st ≤ hj (Protocol.TickScheduler.runWith E hc nd ops blockOut voteOut attOut
      (fun st record emitted => (st, record, emitted)) st record t).1 := by
  let s := E.slotOf t
  let st0 := ops.clock st t s
  let st1 := if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
    (ops.proposal st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time E s then (ops.vote st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then ops.confirmation st2 (s - 1) else st2
  have h0 : hj st ≤ hj st0 := hclock st t
  have h1 : hj st0 ≤ hj st1 := by
    dsimp only [st1]
    split_ifs
    · exact hp st0
    · exact le_rfl
  have h2 : hj st1 ≤ hj st2 := by
    dsimp only [st2]
    split_ifs
    · exact hv st1
    · exact le_rfl
  have h3 : hj st2 ≤ hj st3 := by
    dsimp only [st3]
    split_ifs
    · exact hcfn st2 (s - 1)
    · exact le_rfl
  have hout : (Protocol.TickScheduler.runWith E hc nd ops blockOut voteOut attOut
      (fun st record emitted => (st, record, emitted)) st record t).1 =
      if t = hc.a E.Δ (hc.round_of (ops.slot st3)) ∧
          nd.awake (hc.round_of (ops.slot st3)) = true then
        (ops.attestation st3 record).1
      else st3 := by
    dsimp only [Protocol.TickScheduler.runWith, st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hout]
  split_ifs
  · exact h0.trans (h1.trans (h2.trans (h3.trans (ha st3 record))))
  · exact h0.trans (h1.trans (h2.trans h3))

/-- The actual named tick never lowers `Σ.h_j`, for any grade contract. -/
private theorem namedTick_h_j_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    st.h_j ≤ (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.h_j := by
  have hclock : ∀ (st : Protocol.NamedStore V) (t : Time),
      st.h_j ≤ ((Protocol.NamedTick.namedOps gc E hc cfg nd).clock st t (E.slotOf t)).h_j :=
    fun _ _ => le_rfl
  have hp : ∀ st : Protocol.NamedStore V,
      st.h_j ≤ ((Protocol.NamedTick.namedOps gc E hc cfg nd).proposal st).1.h_j := by
    intro st
    exact propose_block_with_h_j_mono gc E hc cfg nd st
  have hv : ∀ st : Protocol.NamedStore V,
      st.h_j ≤ ((Protocol.NamedTick.namedOps gc E hc cfg nd).vote st).1.h_j := by
    intro st
    exact le_of_eq (goldfish_vote_with_h_j_eq gc E hc nd st).symm
  have hcfn : ∀ (st : Protocol.NamedStore V) (s : Slot),
      st.h_j ≤ ((Protocol.NamedTick.namedOps gc E hc cfg nd).confirmation st s).h_j := by
    intro st s
    exact le_of_eq (update_confirmation_with_h_j_eq gc E hc st s).symm
  have ha : ∀ (st : Protocol.NamedStore V) (record : Protocol.NamedRecord),
      st.h_j ≤ ((Protocol.NamedTick.namedOps gc E hc cfg nd).attestation st record).1.h_j := by
    intro st record
    exact attest_with_h_j_mono gc E hc nd st record
  simp only [Protocol.NamedTick.tick]
  exact scheduler_h_j_mono E hc nd (Protocol.NamedTick.namedOps gc E hc cfg nd)
    NamedObject.block NamedObject.gfVote NamedObject.attest Protocol.NamedStore.h_j
    hclock hp hv hcfn ha st record t

/-- The closed receipt dispatcher never lowers `Σ.h_j`. -/
private theorem namedReceipt_process_h_j_mono (S : Setup V) (st : Protocol.NamedStore V)
    (o : NamedObject V) : st.h_j ≤ (NamedReceipt.process S st o).h_j := by
  cases o with
  | block B =>
      simp only [NamedReceipt.process]
      exact on_block_with_h_j_mono .alsoCarried S.E S.hc S.cfg st B
  | gfVote u =>
      simp only [NamedReceipt.process]
      exact le_of_eq (coreEq_on_goldfish_vote_checked S.E st.core u).h_j_eq.symm
  | attest a =>
      simp only [NamedReceipt.process]
      exact admit_row_h_j_mono S.hc st a

/-- Phase preparation and final cache clipping do not touch the returned
store's `h_j`. -/
private theorem namedNode_tick_h_j_mono (S : Setup V) (v : V) (n : NamedNodeState V)
    (t : Time) : n.st.h_j ≤ (NamedNode.tick S v n t).1.st.h_j := by
  simp only [NamedNode.tick]
  exact namedTick_h_j_mono
    (NamedProfile.gradeContract (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t

/-- Delivery's cache clip and retained record do not touch the returned
store's `h_j`. -/
private theorem namedNode_process_h_j_mono (S : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) : n.st.h_j ≤ (NamedNode.process S n o).st.h_j := by
  simp only [NamedNode.process]
  exact namedReceipt_process_h_j_mono S n.st o

/-! ## Run-level monotonicity of the justified height -/

/-- One Section 7 world event never lowers one node's justified height. -/
private theorem worldStep_h_j_mono (S : Setup V) (w : World V)
    (e : Event V) (v : V) :
    (w v).st.h_j ≤ ((World.step S w e) v).st.h_j := by
  cases e with
  | tick u t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact namedNode_tick_h_j_mono S v (w v) t
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact le_rfl
  | deliver u o t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact namedNode_process_h_j_mono S (w v) o
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact le_rfl

/-- Folding any later event suffix never lowers one node's justified height. -/
private theorem foldlWorld_h_j_mono (S : Setup V) (v : V)
    (events : List (Event V)) (w : World V) :
    (w v).st.h_j ≤ ((events.foldl (World.step S) w) v).st.h_j := by
  induction events generalizing w with
  | nil => exact le_rfl
  | cons e events ih =>
      exact (worldStep_h_j_mono S w e v).trans
        (ih (w := World.step S w e))


/-- A node's justified height is monotone across arbitrary event-prefix
indices. -/
theorem stateBefore_h_j_mono
    (S : Setup V) (rho : Run V) (v : V) {m n : Nat} (hmn : m ≤ n) :
    (rho.stateBefore S m v).st.h_j ≤
      (rho.stateBefore S n v).st.h_j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      have hIH := ih (Nat.le_add_right m k)
      have hstep :
          (rho.stateBefore S (m + k) v).st.h_j ≤
            (rho.stateBefore S (m + k + 1) v).st.h_j := by
        simp only [Run.stateBefore, NamedRun.stateBefore, List.take_add_one, List.foldl_append]
        cases he : rho.events[m + k]? with
        | none => exact le_rfl
        | some e =>
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            exact worldStep_h_j_mono S _ e v
      exact hIH.trans (by simpa [Nat.add_assoc] using hstep)

/-- A node's justified height is monotone between two `stateAt` reads. -/
theorem stateAt_h_j_mono (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) {t t' : Time} (htt' : t ≤ t') :
    (rho.storeAt S v t).h_j ≤ (rho.storeAt S v t').h_j := by
  obtain ⟨events, hevents⟩ := Protocol.stateAt_eq_foldl S sch htt'
  simp only [Run.storeAt, hevents]
  exact foldlWorld_h_j_mono S v events (NamedRun.readAt S rho t)

/-! ## The temporal release-or-staleness statement -/




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
