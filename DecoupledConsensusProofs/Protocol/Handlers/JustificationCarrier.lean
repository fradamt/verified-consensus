module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.NumericStore

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedJustificationCarrier
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

private def CoreJustifier (st : Protocol.Store V) : Prop :=
  ∃ D ∈ st.T, (st.σ D).J = st.J ∧ (st.σ D).h_j = st.h_j

omit [Fintype V] in
private theorem initial_core_justifier :
    CoreJustifier (Protocol.NamedStore.initial : Protocol.NamedStore V).core := by
  exact ⟨Block.genesis, Finset.mem_singleton_self _, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] in
private theorem unchanged {st next : Protocol.Store V}
    (hT : next.T = st.T) (hSigma : next.σ = st.σ)
    (hJ : next.J = st.J) (hhj : next.h_j = st.h_j)
    (h : CoreJustifier st) : CoreJustifier next := by
  obtain ⟨D, hD, hDJ, hDh⟩ := h
  refine ⟨D, ?_, ?_, ?_⟩
  · rwa [hT]
  · rwa [hSigma, hJ]
  · rwa [hSigma, hhj]

private theorem gf_fields (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    let out := Protocol.on_goldfish_vote_checked E st u
    out.T = st.T ∧ out.σ = st.σ ∧ out.J = st.J ∧ out.h_j = st.h_j := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem gf_fold_fields (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) :
    let out := votes.foldl (Protocol.on_goldfish_vote_checked E) st
    out.T = st.T ∧ out.σ = st.σ ∧ out.J = st.J ∧ out.h_j = st.h_j := by
  induction votes generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons u votes ih =>
    have rest := ih (Protocol.on_goldfish_vote_checked E st u)
    have one := gf_fields E st u
    exact ⟨rest.1.trans one.1, rest.2.1.trans one.2.1,
      rest.2.2.1.trans one.2.2.1, rest.2.2.2.trans one.2.2.2⟩

omit [Fintype V] in
private theorem update_justifier (st : Protocol.Store V) (B : Block V)
    (sigma : ChainState V) (hB : B ∈ st.T) (hSigma : st.σ B = sigma)
    (h : CoreJustifier st) : CoreJustifier (Protocol.update_finality st sigma) := by
  obtain ⟨D, hD, hDJ, hDh⟩ := h
  have hNewJ : (st.σ B).J = sigma.J := congrArg ChainState.J hSigma
  have hNewH : (st.σ B).h_j = sigma.h_j := congrArg ChainState.h_j hSigma
  dsimp only [Protocol.update_finality]
  split_ifs <;> first
    | exact ⟨B, hB, hNewJ, hNewH⟩
    | exact ⟨D, hD, hDJ, hDh⟩

private theorem raw_block_justifier (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V)
    (h : CoreJustifier st) : CoreJustifier (Protocol.on_block_using E st B build) := by
  dsimp only [Protocol.on_block_using]
  split_ifs with hguard hpre hproposer hslot <;> first
    | exact h
    | (let sigma := build (st.σ B.parent)
       let stored : Protocol.Store V := { st with
         σ := fun C => if C = B then sigma else st.σ C
         T := insert B st.T
         timestamp_block := fun C => if C = B then some (st.t : Stamp) else st.timestamp_block C }
       let unpacked := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
       have hFresh : B ∉ st.T := fun hB => hguard (Or.inr (Or.inl hB))
       have hStored : CoreJustifier stored := by
         obtain ⟨D, hD, hDF, hDh⟩ := h
         have hDB : D ≠ B := by intro heq; subst D; exact hFresh hD
         exact ⟨D, Finset.mem_insert_of_mem hD, by simpa [stored, if_neg hDB] using hDF,
           by simpa [stored, if_neg hDB] using hDh⟩
       have fields := gf_fold_fields E stored B.gf_votes
       change CoreJustifier (Protocol.update_finality unpacked (unpacked.σ B))
       have hsigma : unpacked.σ B = sigma := by
         rw [fields.2.1]
         simp [stored, sigma]
       rw [hsigma]
       apply update_justifier _ B sigma
       · rw [fields.1]
         exact Finset.mem_insert_self _ _
       · exact hsigma
       · exact unchanged fields.1 fields.2.1 fields.2.2.1
           fields.2.2.2 hStored)

private theorem process_core_justifier (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hco : Proofs.NamedStore.Coherent S.E S.cfg st)
    (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  cases B with
  | genesis =>
    have hmem : Block.genesis ∈ st.core.T := by
      rw [hco.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hco.2.2.1.1
    have hpgen : NamedBlock.genesis.parent ∈ st.bodies := by
      change NamedBlock.genesis ∈ st.bodies
      exact hco.2.2.1.1
    rw [Protocol.NamedStore.process_block_core,
      if_neg (not_not.mpr hpgen), NamedStore.commit_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · change CoreJustifier (Protocol.on_block_using S.E st.core Block.genesis _)
      simpa [Protocol.on_block_using, hmem] using h
    · exact h
  | node parent slot root votes support rows proposer =>
   let B : NamedBlock V := .node parent slot root votes support rows proposer
   change CoreJustifier
     (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core
   by_cases hp : B.parent ∈ st.bodies
   · rw [Protocol.NamedStore.process_block_core, if_neg (not_not.mpr hp), NamedStore.commit_core]
     dsimp only [Protocol.on_block_checked_using]
     split_ifs
     · exact raw_block_justifier S.E st.core B.erase _ h
     · exact h
   · simpa [Protocol.NamedStore.process_block_core, hp] using h

omit [Fintype V] in
private theorem row_justifier (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  dsimp only [Protocol.on_sg_vote]
  split_ifs <;> exact h

omit [Fintype V] in
private theorem rows_justifier (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_justifier hc st a h)

private theorem block_justifier (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreJustifier st.core) :
    CoreJustifier
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hc := process_core_justifier S st B hco h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact rows_justifier S.hc _ B.attestations hc
  · exact hc

private theorem gf_justifier (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V)
    (h : CoreJustifier st) : CoreJustifier (Protocol.on_goldfish_vote_checked E st u) := by
  have f := gf_fields E st u
  exact unchanged f.1 f.2.1 f.2.2.1 f.2.2.2 h

private theorem clock_justifier (E : Env V) (st : Protocol.NamedStore V) (t : Time)
    (h : CoreJustifier st.core) : CoreJustifier (Protocol.NamedStore.setClock E st t).core := h

private theorem confirmation_justifier (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core := h

private theorem propose_justifier (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_justifier S st _ hco h

private theorem vote_justifier (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_justifier S.E st.core _ h
  · exact h

private theorem attest_justifier (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  row_justifier S.hc st _ h

private theorem tick_justifier (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreJustifier st.core) :
    CoreJustifier (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 := clock_justifier S.E st t h
  have hc0 := NamedStore.coherent_clock S.E S.cfg st t hco
  have h1 : CoreJustifier st1.core := by dsimp [st1]; split_ifs
    <;> first | exact propose_justifier gc S nd st0 hc0 h0 | exact h0
  have h2 : CoreJustifier st2.core := by dsimp [st2]; split_ifs
    <;> first | exact vote_justifier gc S nd st1 h1 | exact h1
  have h3 : CoreJustifier st3.core := by
    by_cases hs : 0 < s ∧ t = Protocol.support_cutoff S.E s
    · simpa [st3, hs] using confirmation_justifier gc S st2 (s - 1) h2
    · simpa [st3, hs] using h2
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact attest_justifier gc S nd st3 record h3
  · exact h3

private theorem node_tick_justifier (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreJustifier n.st.core) :
    CoreJustifier (Execution.NamedNode.tick S v n t).1.st.core :=
  tick_justifier (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t hco h

private theorem node_process_justifier (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreJustifier n.st.core) :
    CoreJustifier (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact block_justifier S n.st B hco h
  | gfVote u => exact gf_justifier S.E n.st.core u h
  | attest a => exact row_justifier S.hc n.st a h

private theorem fold_justifier (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (hinv : ∀ v, Proofs.NamedConfirmationMembership.Invariant S.E S.cfg (w v).st ∧
      NamedTickRecord.Invariant (w v).record)
    (h : ∀ v, CoreJustifier (w v).st.core) :
    ∀ v, CoreJustifier (events.foldl (NamedWorld.step S) w v).st.core := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih =>
    apply ih
    · intro v
      cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          exact ⟨by simpa [NamedWorld.step] using
              NamedNode.confirmation_invariant_tick S v (w v) t (hinv v).1,
            by simpa [NamedWorld.step] using
              NamedNode.record_invariant_tick S v (w v) t (hinv v).2⟩
        · simpa [NamedWorld.step, Function.update_of_ne hv] using hinv v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using NamedNode.invariants_process S (w v) o (hinv v).1 (hinv v).2
        · simpa [NamedWorld.step, Function.update_of_ne hv] using hinv v
    · intro v
      cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using
            node_tick_justifier S v (w v) t (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u; simpa [NamedWorld.step] using
            node_process_justifier S (w v) o (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v

private theorem named_justifier (S : Setup V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreJustifier st.core) :
    ∃ D : NamedBlock V, D ∈ st.bodies ∧ (derive_named S.E S.cfg D).J = st.core.J ∧
      (derive_named S.E S.cfg D).h_j = st.core.h_j := by
  obtain ⟨raw, hraw, hF, hh⟩ := h
  rw [hco.1] at hraw
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hraw
  rw [hco.2.2.2.2 D hD] at hF hh
  exact ⟨D, hD, hF, hh⟩

/-- Both justification fields come from one actual full held named body.
This is unconditional strict-read provenance, not a compatibility statement. -/
theorem justification_carrier_stateBeforeTime
    (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBeforeTime S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).J = (NamedRun.stateBeforeTime S rho t v).st.core.J ∧
      (derive_named S.E S.cfg D).h_j = (NamedRun.stateBeforeTime S rho t v).st.core.h_j :=
  named_justifier S _ (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
    (fold_justifier S _ NamedWorld.init (fun _ => NamedNode.initial_invariants S)
      (fun _ => initial_core_justifier) v)

/-- Index form of `justification_carrier_stateBeforeTime`. -/
theorem justification_carrier_stateBefore
    (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      (derive_named S.E S.cfg D).J = (NamedRun.stateBefore S rho i v).st.core.J ∧
      (derive_named S.E S.cfg D).h_j = (NamedRun.stateBefore S rho i v).st.core.h_j :=
  named_justifier S _ (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
    (fold_justifier S (rho.events.take i) NamedWorld.init
      (fun _ => NamedNode.initial_invariants S) (fun _ => initial_core_justifier) v)

/-- Non-strict-read form, the one the B11 facades read. -/
theorem justification_carrier_readAt
    (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.readAt S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).J = (NamedRun.readAt S rho t v).st.core.J ∧
      (derive_named S.E S.cfg D).h_j = (NamedRun.readAt S rho t v).st.core.h_j :=
  named_justifier S _ (Proofs.NamedRuntime.readAt_invariants S rho t v).1.1.1
    (fold_justifier S _ NamedWorld.init (fun _ => NamedNode.initial_invariants S)
      (fun _ => initial_core_justifier) v)


end DecoupledConsensusModel.Proofs.NamedJustificationCarrier

end
