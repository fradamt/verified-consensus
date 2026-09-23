module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.NumericStore

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedMaximumCarrier
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

private def CoreMaximum (st : Protocol.Store V) : Prop :=
  ∃ D ∈ st.T, (st.σ D).h = st.h_max

omit [Fintype V] in
private theorem initial_core_maximum :
    CoreMaximum (Protocol.NamedStore.initial : Protocol.NamedStore V).core := by
  exact ⟨Block.genesis, Finset.mem_singleton_self _, rfl⟩

omit [DecidableEq V] [Fintype V] in
private theorem unchanged {st next : Protocol.Store V}
    (hT : next.T = st.T) (hSigma : next.σ = st.σ)
    (hmax : next.h_max = st.h_max) (h : CoreMaximum st) : CoreMaximum next := by
  obtain ⟨D, hD, hDh⟩ := h
  refine ⟨D, ?_, ?_⟩
  · rwa [hT]
  · rwa [hSigma, hmax]

omit [Fintype V] in
private theorem finality_fields (st : Protocol.Store V) (sigma : ChainState V) :
    let out := Protocol.update_finality st sigma
    out.T = st.T ∧ out.σ = st.σ ∧ out.h_max = max st.h_max sigma.h := by
  dsimp only [Protocol.update_finality]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

omit [Fintype V] in
private theorem update_maximum (st : Protocol.Store V) (B : Block V)
    (sigma : ChainState V) (hB : B ∈ st.T) (hSigma : st.σ B = sigma)
    (h : CoreMaximum st) : CoreMaximum (Protocol.update_finality st sigma) := by
  have fields := finality_fields st sigma
  by_cases hle : st.h_max ≤ sigma.h
  · refine ⟨B, ?_, ?_⟩
    · rw [fields.1]
      exact hB
    · rw [fields.2.1, fields.2.2, hSigma, Nat.max_eq_right hle]
  · obtain ⟨D, hD, hDh⟩ := h
    have hge : sigma.h ≤ st.h_max := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    refine ⟨D, ?_, ?_⟩
    · rw [fields.1]
      exact hD
    · rw [fields.2.1, fields.2.2, hDh, Nat.max_eq_left hge]

private theorem gf_fields (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    let out := Protocol.on_goldfish_vote_checked E st u
    out.T = st.T ∧ out.σ = st.σ ∧ out.h_max = st.h_max := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

private theorem gf_fold_fields (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) :
    let out := votes.foldl (Protocol.on_goldfish_vote_checked E) st
    out.T = st.T ∧ out.σ = st.σ ∧ out.h_max = st.h_max := by
  induction votes generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u votes ih =>
    have rest := ih (Protocol.on_goldfish_vote_checked E st u)
    have one := gf_fields E st u
    exact ⟨rest.1.trans one.1, rest.2.1.trans one.2.1,
      rest.2.2.trans one.2.2⟩

private theorem raw_block_maximum (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V)
    (h : CoreMaximum st) : CoreMaximum (Protocol.on_block_using E st B build) := by
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
       have hStored : CoreMaximum stored := by
         obtain ⟨D, hD, hDh⟩ := h
         have hDB : D ≠ B := by intro heq; subst D; exact hFresh hD
         exact ⟨D, Finset.mem_insert_of_mem hD,
           by simpa [stored, if_neg hDB] using hDh⟩
       have fields := gf_fold_fields E stored B.gf_votes
       change CoreMaximum (Protocol.update_finality unpacked (unpacked.σ B))
       have hsigma : unpacked.σ B = sigma := by
         rw [fields.2.1]
         simp [stored, sigma]
       rw [hsigma]
       apply update_maximum unpacked B sigma
       · rw [fields.1]
         exact Finset.mem_insert_self _ _
       · exact hsigma
       · exact unchanged fields.1 fields.2.1 fields.2.2 hStored)

private theorem process_core_maximum (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact h
    | (rw [NamedStore.commit_core]
       dsimp only [Protocol.on_block_checked_using]
       split_ifs
       · exact raw_block_maximum S.E st.core B.erase _ h
       · exact h)

omit [Fintype V] in
private theorem row_maximum (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  dsimp only [Protocol.on_sg_vote]
  split_ifs <;> exact h

omit [Fintype V] in
private theorem rows_maximum (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_maximum hc st a h)

private theorem block_maximum (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : CoreMaximum st.core) :
    CoreMaximum
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hc := process_core_maximum S st B h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact rows_maximum S.hc _ B.attestations hc
  · exact hc

private theorem gf_maximum (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V)
    (h : CoreMaximum st) : CoreMaximum (Protocol.on_goldfish_vote_checked E st u) := by
  have fields := gf_fields E st u
  exact unchanged fields.1 fields.2.1 fields.2.2 h

private theorem clock_maximum (E : Env V) (st : Protocol.NamedStore V) (t : Time)
    (h : CoreMaximum st.core) : CoreMaximum (Protocol.NamedStore.setClock E st t).core := h

private theorem confirmation_maximum (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core := h

private theorem propose_maximum (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_maximum S st _ h

private theorem vote_maximum (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_maximum S.E st.core _ h
  · exact h

private theorem attest_maximum (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  row_maximum S.hc st _ h

private theorem tick_maximum (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (h : CoreMaximum st.core) :
    CoreMaximum (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 := clock_maximum S.E st t h
  have h1 : CoreMaximum st1.core := by
    dsimp [st1]
    split_ifs <;> first
      | exact propose_maximum gc S nd st0 h0
      | exact h0
  have h2 : CoreMaximum st2.core := by
    dsimp [st2]
    split_ifs <;> first
      | exact vote_maximum gc S nd st1 h1
      | exact h1
  have h3 : CoreMaximum st3.core := by
    by_cases hs : 0 < s ∧ t = Protocol.support_cutoff S.E s
    · simpa [st3, hs] using confirmation_maximum gc S st2 (s - 1) h2
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
  · exact attest_maximum gc S nd st3 record h3
  · exact h3

private theorem node_tick_maximum (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : CoreMaximum n.st.core) :
    CoreMaximum (Execution.NamedNode.tick S v n t).1.st.core :=
  tick_maximum (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t h

private theorem node_process_maximum (S : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) (h : CoreMaximum n.st.core) :
    CoreMaximum (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact block_maximum S n.st B h
  | gfVote u => exact gf_maximum S.E n.st.core u h
  | attest a => exact row_maximum S.hc n.st a h

private theorem world_step_maximum (S : Setup V) (w : NamedWorld V)
    (e : NamedEvent V) (v : V) (h : CoreMaximum (w v).st.core) :
    CoreMaximum (NamedWorld.step S w e v).st.core := by
  cases e with
  | tick u t =>
    by_cases hv : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using node_tick_maximum S v (w v) t h
    · simpa only [NamedWorld.step, Function.update_of_ne hv] using h
  | deliver u o t =>
    by_cases hv : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using node_process_maximum S (w v) o h
    · simpa only [NamedWorld.step, Function.update_of_ne hv] using h

private theorem fold_maximum (S : Setup V) (events : List (NamedEvent V))
    (w : NamedWorld V) (h : ∀ v, CoreMaximum (w v).st.core) :
    ∀ v, CoreMaximum (events.foldl (NamedWorld.step S) w v).st.core := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih => exact ih _ (fun v => world_step_maximum S w e v (h v))

private theorem named_maximum (S : Setup V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreMaximum st.core) :
    ∃ D : NamedBlock V, D ∈ st.bodies ∧ (derive_named S.E S.cfg D).h = st.core.h_max := by
  obtain ⟨raw, hraw, hh⟩ := h
  rw [hco.1] at hraw
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hraw
  rw [hco.2.2.2.2 D hD] at hh
  exact ⟨D, hD, hh⟩

/-- The strict-read maximum is attained by one actual held full named body. -/
theorem maximum_carrier_stateBeforeTime
    (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    ∃ D : NamedBlock V,
      D ∈ (NamedRun.stateBeforeTime S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).h =
        (NamedRun.stateBeforeTime S rho t v).st.core.h_max :=
  named_maximum S _ (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
    (fold_maximum S _ NamedWorld.init (fun _ => initial_core_maximum) v)


/-- The same at an event index. The fold that carries `CoreMaximum` is private
to this file, so the index form is stated here rather than rebuilt downstream
(export E6). -/
theorem maximum_carrier_stateBefore
    (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    ∃ D : NamedBlock V,
      D ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      (derive_named S.E S.cfg D).h =
        (NamedRun.stateBefore S rho i v).st.core.h_max :=
  named_maximum S _ (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
    (fold_maximum S (rho.events.take i) NamedWorld.init (fun _ => initial_core_maximum) v)

/-- The same at a non-strict read. -/
theorem maximum_carrier_readAt
    (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    ∃ D : NamedBlock V,
      D ∈ (NamedRun.readAt S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).h = (NamedRun.readAt S rho t v).st.core.h_max :=
  named_maximum S _ (Proofs.NamedRuntime.readAt_invariants S rho t v).1.1.1
    (fold_maximum S _ NamedWorld.init (fun _ => initial_core_maximum) v)


end DecoupledConsensusModel.Proofs.NamedMaximumCarrier

end
