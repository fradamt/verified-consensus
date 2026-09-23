module
public import DecoupledConsensusStatements.Instantiation
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Claims
public import DecoupledConsensusInternal.Legacy.Instance
public import DecoupledConsensusProofs.ModelVocabulary.Execution.Instance
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedAdmissible

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

abbrev P (S : Setup V) := DecoupledConsensusModel.Execution.spec S
abbrev E (S : Setup V) := Statements.Instantiation.env S
abbrev I (S : Setup V) := Statements.Instantiation.interface S

private theorem named_key_eq (e : NamedEvent V) :
    NamedEvent.key e = Generic.Event.key e := by
  cases e <;> rfl

private theorem named_time_eq (e : NamedEvent V) :
    NamedEvent.time e = Generic.Event.time e := by
  cases e <;> rfl

private theorem named_node_eq (e : NamedEvent V) :
    NamedEvent.node e = Generic.Event.node e := by
  cases e <;> rfl

private theorem emits_iff (S : Setup V) (rho : Run V) (v : V)
    (o : NamedObject V) (t : Time) :
    Generic.Run.emits (P S) rho v o t ↔ NamedRun.emits S rho v o t := by
  unfold Generic.Run.emits NamedRun.emits
  rw [Execution.emittedAt_eq S rho]
  rfl

private theorem processes_iff (S : Setup V) (rho : Run V) (v : V)
    (o : NamedObject V) (t : Time) :
    Generic.Run.processes (P S) rho v o t ↔ NamedRun.processes S rho v o t := by
  unfold Generic.Run.processes NamedRun.processes
  rw [emits_iff S rho v o t]
  rfl

private theorem handles_iff (S : Setup V) (rho : Run V) (i : Nat) (v : V)
    (e : NamedEvent V) (o : NamedObject V)
    (he : rho.events[i]? = some e) (hnode : e.node = v) :
    DecoupledConsensusModel.Execution.handles S (NamedRun.stateBefore S rho i v) e o ↔
      NamedRun.actualHandlesAtIndex S rho i v o := by
  cases o <;>
    simp [DecoupledConsensusModel.Execution.handles, NamedRun.actualHandlesAtIndex,
      NamedRun.processesAtIndex, Execution.NamedReceiptCalls.carriedGoldfishAt,
      Execution.NamedReceiptCalls.carriedAttestationAt, Execution.NamedReceiptCalls.blockCallAt,
      NamedRun.emittedAt,
      he, hnode]

theorem handlesAt_iff (S : Setup V) (rho : Run V) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) :
    Generic.Run.handlesAt (P S) rho i v o t ↔
      NamedRun.actualHandlesAt S rho i v o t := by
  constructor
  · rintro ⟨e, he, hnode, htime, hh⟩
    have hstate : Generic.Run.stateBefore (P S) rho i =
        NamedRun.stateBefore S rho i := by
      simpa only [P] using
        congrFun (Execution.stateBefore_eq S rho) i
    change DecoupledConsensusModel.Execution.handles S
        (Generic.Run.stateBefore (P S) rho i v) e o at hh
    rw [hstate] at hh
    have hnode' : NamedEvent.node e = v := by
      simpa only [named_node_eq] using hnode
    have htime' : NamedEvent.time e = t := by
      simpa only [named_time_eq] using htime
    exact ⟨(handles_iff S rho i v e o he hnode').1 hh,
      ⟨e, he, hnode', htime'⟩⟩
  · rintro ⟨ho, ⟨e, he, hnode, htime⟩⟩
    have hstate : Generic.Run.stateBefore (P S) rho i =
        NamedRun.stateBefore S rho i := by
      simpa only [P] using
        congrFun (Execution.stateBefore_eq S rho) i
    have hh := (handles_iff S rho i v e o he hnode).2 ho
    rw [← hstate] at hh
    change (P S).handles (Generic.Run.stateBefore (P S) rho i v) e o at hh
    have hnode' : Generic.Event.node e = v := by
      simpa only [named_node_eq] using hnode
    have htime' : Generic.Event.time e = t := by
      simpa only [named_time_eq] using htime
    exact ⟨e, he, hnode', htime', hh⟩

theorem acceptsAt_iff (S : Setup V) (rho : Run V) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) :
    Generic.Run.acceptsAt (P S) rho i v o t ↔
      NamedRun.acceptsAt S rho i v o t := by
  unfold Generic.Run.acceptsAt NamedRun.acceptsAt
  rw [handlesAt_iff S rho i v o t]
  constructor
  · rintro ⟨ha, hf, ht⟩
    change NamedReceipt.processed
        (Generic.Run.stateBefore (P S) rho i v).st o = false at hf
    change NamedReceipt.processed
        (Generic.Run.stateBefore (P S) rho (i + 1) v).st o = true at ht
    rw [Execution.stateBefore_eq S rho] at hf
    rw [Execution.stateBefore_eq S rho] at ht
    exact ⟨ha, hf, ht⟩
  · rintro ⟨ha, hf, ht⟩
    have hstate : Generic.Run.stateBefore (P S) rho i =
        NamedRun.stateBefore S rho i := by
      simpa only [P] using
        congrFun (Execution.stateBefore_eq S rho) i
    have hstate' : Generic.Run.stateBefore (P S) rho (i + 1) =
        NamedRun.stateBefore S rho (i + 1) := by
      simpa only [P] using
        congrFun (Execution.stateBefore_eq S rho) (i + 1)
    refine ⟨ha, ?_, ?_⟩
    · change NamedReceipt.processed
          (Generic.Run.stateBefore (P S) rho i v).st o = false
      rw [hstate]
      exact hf
    · change NamedReceipt.processed
          (Generic.Run.stateBefore (P S) rho (i + 1) v).st o = true
      rw [hstate']
      exact ht

private theorem named_execution_valid_of_generic_schedule
    (S : Setup V) (rho : Run V)
    (h : Generic.ScheduleWellFormed (P := P S) (E S) rho) :
    NamedScheduleWellFormed S rho := by
  refine {
    horizon_nonneg := h.horizon_nonneg
    sorted := by
      simpa only [NamedRun.events_eq, named_key_eq] using h.sorted
    nodup := by simpa only [NamedRun.events_eq] using h.nodup
    in_horizon := by
      simpa only [NamedRun.events_eq, NamedRun.horizon_eq, named_time_eq] using h.in_horizon
    honest_only := by
      simpa only [NamedRun.events_eq, NamedRun.honest_eq, named_node_eq] using h.honest_only
    tick_public := ?_
    tick_total := ?_ }
  · intro v t ht
    simpa [Generic.PublicTime, E] using h.tick_public v t ht
  · intro v hv t ht h0 hhor
    exact h.tick_total v hv t (by simpa [Generic.PublicTime, E] using ht) h0 hhor

private theorem named_execution_valid_of_generic_delivery
    (S : Setup V) (rho : Run V)
    (h : Generic.DeliveryWellFormed (P S) rho) :
    NamedDeliveryWellFormed S rho := by
  refine {
    wire := ?_
    deps := ?_
    fresh := ?_ }
  · intro i v o t he
    exact h.wire i v o t he
  · intro i v o t he
    have hh := h.deps i v o t he
    change NamedReceipt.depsPresent
        (Generic.Run.stateBefore (P S) rho i v).st o = true at hh
    rw [Execution.stateBefore_eq S rho] at hh
    exact hh
  · intro i v o t he
    have hh := h.fresh i v o t he
    change NamedReceipt.processed
        (Generic.Run.stateBefore (P S) rho i v).st o = false at hh
    rw [Execution.stateBefore_eq S rho] at hh
    exact hh

private theorem named_execution_valid_of_generic_unforgeable
    (S : Setup V) (rho : Run V)
    (h : Generic.UnforgeableSignatures (P S) rho) : NamedUnforgeable S rho := by
  refine {
    unforgeable := ?_
    carried_gf := ?_
    carried_attest := ?_ }
  · intro v o t hproc u hu ha
    have hproc' := (processes_iff S rho v o t).2 hproc
    have hh := h.unforgeable v o t hproc' u hu ha
    rcases hh with ⟨t', htle, hemits⟩
    exact ⟨t', htle, (emits_iff S rho u o t').1 hemits⟩
  · intro v B t hproc u hu uh
    have hproc' := (processes_iff S rho v (.block B) t).2 hproc
    have hcarries : Generic.ProtocolSpec.carries (P S) (.block B) (.gfVote u) := by
      exact Or.inl ⟨u, hu, rfl⟩
    have hauthor : (NamedObject.gfVote u).author = some u.val_index := rfl
    have hh := h.carried v (.block B) t hproc' (.gfVote u) hcarries
      u.val_index uh hauthor
    rcases hh with ⟨t', htle, hemits⟩
    exact ⟨t', htle, (emits_iff S rho u.val_index (.gfVote u) t').1 hemits⟩
  · intro v B t hproc a ha ah
    have hproc' := (processes_iff S rho v (.block B) t).2 hproc
    have hcarries : Generic.ProtocolSpec.carries (P S) (.block B) (.attest a) := by
      exact Or.inr ⟨a, ha, rfl⟩
    have hauthor : (NamedObject.attest a).author = some a.val_index := rfl
    have hh := h.carried v (.block B) t hproc' (.attest a) hcarries
      a.val_index ah hauthor
    rcases hh with ⟨t', htle, hemits⟩
    exact ⟨t', htle, (emits_iff S rho a.val_index (.attest a) t').1 hemits⟩

theorem voteSafetySchedule_of_generic_unforgeableRun
    (S : Setup V) (rho : Run V)
    (h : Generic.UnforgeableRun (P S) (E S) (I S) rho) :
    VoteSafetySchedule S rho := by
  refine {
    sorted := by
      simpa only [NamedRun.events_eq, named_key_eq] using h.sorted
    honest_only := by
      simpa only [NamedRun.events_eq, named_node_eq] using h.honest_only }

theorem attestationAuthenticity_of_generic_unforgeableRun
    (S : Setup V) (rho : Run V)
    (h : Generic.UnforgeableRun (P S) (E S) (I S) rho) :
    AttestationAuthenticity S rho := by
  refine { carriedAttest := ?_ }
  intro v B t hproc a ha ah
  have hproc' := (processes_iff S rho v (.block B) t).2 hproc
  have hcarries : Generic.ProtocolSpec.carries (P S) (.block B) (.attest a) := by
    exact Or.inr ⟨a, ha, rfl⟩
  have hauthor : (NamedObject.attest a).author = some a.val_index := rfl
  have hh := h.toUnforgeableSignatures.carried v (.block B) t hproc' (.attest a) hcarries
    a.val_index ah hauthor
  rcases hh with ⟨t', htle, hemits⟩
  exact ⟨t', htle, (emits_iff S rho a.val_index (.attest a) t').1 hemits⟩

theorem executionValid_of_generic
    (S : Setup V) (rho : Run V)
    (h : Generic.ExecutionValid (P S) (E S) (I S) rho) :
    Execution.ExecutionValid S rho := by
  refine {
    toNamedScheduleWellFormed :=
      named_execution_valid_of_generic_schedule S rho h.toScheduleWellFormed
    toNamedDeliveryWellFormed :=
      named_execution_valid_of_generic_delivery S rho h.toDeliveryWellFormed
    toNamedRootCollisionFree := h.idealization
    toNamedUnforgeable :=
      named_execution_valid_of_generic_unforgeable S rho h.toUnforgeableSignatures }

theorem finalityExecution_of_generic_runWellFormed
    (S : Setup V) (rho : Run V)
    (h : Generic.RunWellFormed (E S) (I S) rho) :
    Internal.FinalityExecution S rho := by
  refine { sorted := ?_, rootCollisionFree := h.idealization }
  simpa only [NamedRun.events_eq, named_key_eq] using h.sorted

private theorem processed_eq (S : Setup V) (rho : Run V) (i : Nat) (v : V)
    (o : NamedObject V) :
    (P S).processed (Generic.Run.stateBefore (P S) rho i v) o =
      NamedReceipt.processed (NamedRun.stateBefore S rho i v).st o := by
  change NamedReceipt.processed
      (Generic.Run.stateBefore (P S) rho i v).st o = _
  rw [Execution.stateBefore_eq S rho]

private theorem excludes_eq (S : Setup V) (rho : Run V) (d : Time) (w : V)
    (o : NamedObject V) :
    (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho d w) o =
      NamedReceipt.excludes (NamedRun.stateBeforeTime S rho d w).st o := by
  change NamedReceipt.excludes
      (Generic.Run.stateBeforeTime (P S) rho d w).st o = _
  rw [Execution.stateBeforeTime_eq S rho]

theorem genericExecutionValid_of_named
    (S : Setup V) (rho : Run V)
    (h : Execution.ExecutionValid S rho) :
    Generic.ExecutionValid (P S) (E S) (I S) rho := by
  refine {
    toScheduleWellFormed := ?_
    toDeliveryWellFormed := ?_
    toUnforgeableSignatures := ?_
    idealization := h.toNamedRootCollisionFree }
  · refine {
      horizon_nonneg := h.toNamedScheduleWellFormed.horizon_nonneg
      sorted := ?_
      nodup := h.toNamedScheduleWellFormed.nodup
      in_horizon := ?_
      honest_only := ?_
      tick_public := ?_
      tick_total := ?_ }
    · simpa only [NamedRun.events_eq, named_key_eq] using
        h.toNamedScheduleWellFormed.sorted
    · simpa only [NamedRun.events_eq, NamedRun.horizon_eq, named_time_eq] using
        h.toNamedScheduleWellFormed.in_horizon
    · simpa only [NamedRun.events_eq, named_node_eq] using
        h.toNamedScheduleWellFormed.honest_only
    · intro v t ht
      simpa [Generic.PublicTime, Execution.PublicTime, E] using
        h.toNamedScheduleWellFormed.tick_public v t ht
    · intro v hv t ht hnonneg hhor
      apply h.toNamedScheduleWellFormed.tick_total v hv t
      · simpa [Generic.PublicTime, Execution.PublicTime, E] using ht
      · exact hnonneg
      · exact hhor
  · refine {
      wire := ?_
      deps := ?_
      fresh := ?_ }
    · intro i v o t he
      change NamedReceipt.wellFormed S o = true
      exact h.toNamedDeliveryWellFormed.wire i v o t he
    · intro i v o t he
      change NamedReceipt.depsPresent
          (Generic.Run.stateBefore (P S) rho i v).st o = true
      rw [Execution.stateBefore_eq S rho]
      exact h.toNamedDeliveryWellFormed.deps i v o t he
    · intro i v o t he
      change NamedReceipt.processed
          (Generic.Run.stateBefore (P S) rho i v).st o = false
      rw [Execution.stateBefore_eq S rho]
      exact h.toNamedDeliveryWellFormed.fresh i v o t he
  · refine {
      unforgeable := ?_
      carried := ?_ }
    · intro v o t hproc u hu ha
      have hproc' := (processes_iff S rho v o t).1 hproc
      have ha' : (NamedObject.author o) = some u := by simpa [P] using ha
      rcases h.toNamedUnforgeable.unforgeable v o t hproc' u hu ha' with
        ⟨t', htle, hemits⟩
      exact ⟨t', htle, (emits_iff S rho u o t').2 hemits⟩
    · intro v o t hproc o' hcarries u hu ha
      cases o with
      | block B =>
          cases o' with
          | block B' =>
              rcases hcarries with hgf | hattest
              · rcases hgf with ⟨u', hu', heq⟩
                cases heq
              · rcases hattest with ⟨a', ha', heq⟩
                cases heq
          | gfVote vote =>
              rcases hcarries with hgf | hbad
              · rcases hgf with ⟨u', hu', heq⟩
                have hEq : vote = u' := by injection heq
                subst vote
                have hproc' := (processes_iff S rho v (.block B) t).1 hproc
                have hopt : (some u'.val_index : Option V) = some u := by
                  simpa [P, DecoupledConsensusModel.Execution.spec, NamedObject.author] using ha
                have hvote : u'.val_index = u := Option.some.inj hopt
                have hvoteHonest : u'.val_index ∈ rho.honest := by
                  simpa [hvote] using hu
                rcases h.toNamedUnforgeable.carried_gf v B t hproc' u' hu'
                  hvoteHonest with ⟨t', htle, hemits⟩
                exact ⟨t', htle, by
                  simpa [hvote] using
                    (emits_iff S rho u'.val_index (.gfVote u') t').2 hemits⟩
              · rcases hbad with ⟨a0, ha0, heq⟩
                cases heq
          | attest a =>
              rcases hcarries with hbad | hattest
              · rcases hbad with ⟨u0, hu0, heq⟩
                cases heq
              · rcases hattest with ⟨a', ha', heq⟩
                have hEq : a = a' := by injection heq
                subst a
                have hproc' := (processes_iff S rho v (.block B) t).1 hproc
                have hopt : (some a'.val_index : Option V) = some u := by
                  simpa [P, DecoupledConsensusModel.Execution.spec, NamedObject.author] using ha
                have hattestVal : a'.val_index = u := Option.some.inj hopt
                have hattestHonest : a'.val_index ∈ rho.honest := by
                  simpa [hattestVal] using hu
                rcases h.toNamedUnforgeable.carried_attest v B t hproc' a' ha'
                  hattestHonest with ⟨t', htle, hemits⟩
                exact ⟨t', htle, by
                  simpa [hattestVal] using
                    (emits_iff S rho a'.val_index (.attest a') t').2 hemits⟩
      | gfVote u0 => cases hcarries
      | attest a0 => cases hcarries

theorem genericPartialSynchrony_of_named
    (S : Setup V) (rho : Run V)
    (h : Execution.PartialSynchrony S rho) :
    Generic.PartialSynchrony (P S) (E S) rho := by
  refine { broadcast := ?_, relay := ?_ }
  · intro v hv o t hemit w hw hbound hguard
    rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w o] at hguard
    rcases Execution.Synchrony.broadcast h v hv o t
        ((emits_iff S rho v o t).1 hemit) w hw hbound hguard with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w o t').2 hj⟩
  · intro v hv i o t hacc w hw hmiss hbound hguard
    cases o with
    | block B =>
        rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w (.block B)] at hguard
        have hacc' := (acceptsAt_iff S rho i v (.block B) t).1 hacc
        have hmiss' := hmiss
        rw [processed_eq S rho (i + 1) w (.block B)] at hmiss'
        rcases Execution.Synchrony.relay_block h v hv i B t hacc' w hw hmiss' hbound hguard with
          ⟨t', htle, htlt, j, hj⟩
        exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.block B) t').2 hj⟩
    | gfVote u =>
        rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w (.gfVote u)] at hguard
        have hacc' := (acceptsAt_iff S rho i v (.gfVote u) t).1 hacc
        have hmiss' := hmiss
        rw [processed_eq S rho (i + 1) w (.gfVote u)] at hmiss'
        rcases Execution.Synchrony.relay_gf_vote h v hv i u t hacc' w hw hmiss' hbound hguard with
          ⟨t', htle, htlt, j, hj⟩
        exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.gfVote u) t').2 hj⟩
    | attest a =>
        rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w (.attest a)] at hguard
        have hacc' := (acceptsAt_iff S rho i v (.attest a) t).1 hacc
        have hmiss' := hmiss
        rw [processed_eq S rho (i + 1) w (.attest a)] at hmiss'
        rcases Execution.Synchrony.relay_attest h v hv i a t hacc' w hw hmiss' hbound hguard with
          ⟨t', htle, htlt, j, hj⟩
        exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.attest a) t').2 hj⟩

theorem genericHealthyPrefixDelivery_of_named
    (S : Setup V) (rho : Run V) (cut : Time)
    (h : Execution.HealthyPrefixDelivery S rho cut) :
    Generic.HealthyPrefixDelivery (P S) (E S) rho cut := by
  refine { broadcast := ?_, relay := ?_ }
  · intro v hv o t hemit w hw hcut hguard
    rw [excludes_eq S rho (t + (E S).Δ) w o] at hguard
    rcases Execution.NamedHealthyPrefixDelivery.broadcast h v hv o t
        ((emits_iff S rho v o t).1 hemit) w hw hcut hguard with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w o t').2 hj⟩
  · intro v hv i o t hacc w hw hmiss hcut hguard
    cases o with
    | block B =>
        rw [excludes_eq S rho (t + (E S).Δ) w (.block B)] at hguard
        have hacc' := (acceptsAt_iff S rho i v (.block B) t).1 hacc
        have hmiss' := hmiss
        rw [processed_eq S rho (i + 1) w (.block B)] at hmiss'
        rcases Execution.NamedHealthyPrefixDelivery.relay_block h v hv i B t
            hacc' w hw hmiss' hcut hguard with
          ⟨t', htle, htlt, j, hj⟩
        exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.block B) t').2 hj⟩
    | gfVote u =>
        rw [excludes_eq S rho (t + (E S).Δ) w (.gfVote u)] at hguard
        have hacc' := (acceptsAt_iff S rho i v (.gfVote u) t).1 hacc
        have hmiss' := hmiss
        rw [processed_eq S rho (i + 1) w (.gfVote u)] at hmiss'
        rcases Execution.NamedHealthyPrefixDelivery.relay_gf_vote h v hv i u t
            hacc' w hw hmiss' hcut hguard with
          ⟨t', htle, htlt, j, hj⟩
        exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.gfVote u) t').2 hj⟩
    | attest a =>
        rw [excludes_eq S rho (t + (E S).Δ) w (.attest a)] at hguard
        have hacc' := (acceptsAt_iff S rho i v (.attest a) t).1 hacc
        have hmiss' := hmiss
        rw [processed_eq S rho (i + 1) w (.attest a)] at hmiss'
        rcases Execution.NamedHealthyPrefixDelivery.relay_attest h v hv i a t
            hacc' w hw hmiss' hcut hguard with
          ⟨t', htle, htlt, j, hj⟩
        exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.attest a) t').2 hj⟩

theorem partialSynchrony_of_generic
    (S : Setup V) (rho : Run V)
    (h : Generic.PartialSynchrony (P S) (E S) rho) :
    Execution.PartialSynchrony S rho := by
  refine {
    broadcast := ?_
    relay_block := ?_
    relay_gf_vote := ?_
    relay_attest := ?_ }
  · intro v hv o t hemit w hw hbound hguard
    have hemit' := (emits_iff S rho v o t).2 hemit
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho
          (max t (E S).t_GST + (E S).Δ) w) o = false := by
      rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w o]
      exact hguard
    rcases h.broadcast v hv o t hemit' w hw hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w o t').1 hj⟩
  · intro v hv i B t hacc w hw hmiss hbound hguard
    have hacc' := (acceptsAt_iff S rho i v (.block B) t).2 hacc
    have hmiss' : (P S).processed
        (Generic.Run.stateBefore (P S) rho (i + 1) w) (.block B) = false := by
      rw [processed_eq S rho (i + 1) w (.block B)]
      exact hmiss
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho
          (max t (E S).t_GST + (E S).Δ) w) (.block B) = false := by
      rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w (.block B)]
      exact hguard
    rcases h.relay v hv i (.block B) t hacc' w hw hmiss' hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.block B) t').1 hj⟩
  · intro v hv i u t hacc w hw hmiss hbound hguard
    have hacc' := (acceptsAt_iff S rho i v (.gfVote u) t).2 hacc
    have hmiss' : (P S).processed
        (Generic.Run.stateBefore (P S) rho (i + 1) w) (.gfVote u) = false := by
      rw [processed_eq S rho (i + 1) w (.gfVote u)]
      exact hmiss
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho
          (max t (E S).t_GST + (E S).Δ) w) (.gfVote u) = false := by
      rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w (.gfVote u)]
      exact hguard
    rcases h.relay v hv i (.gfVote u) t hacc' w hw hmiss' hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.gfVote u) t').1 hj⟩
  · intro v hv i a t hacc w hw hmiss hbound hguard
    have hacc' := (acceptsAt_iff S rho i v (.attest a) t).2 hacc
    have hmiss' : (P S).processed
        (Generic.Run.stateBefore (P S) rho (i + 1) w) (.attest a) = false := by
      rw [processed_eq S rho (i + 1) w (.attest a)]
      exact hmiss
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho
          (max t (E S).t_GST + (E S).Δ) w) (.attest a) = false := by
      rw [excludes_eq S rho (max t (E S).t_GST + (E S).Δ) w (.attest a)]
      exact hguard
    rcases h.relay v hv i (.attest a) t hacc' w hw hmiss' hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.attest a) t').1 hj⟩

theorem healthy_of_generic
    (S : Setup V) (rho : Run V) (cut : Time)
    (h : Generic.HealthyPrefixDelivery (P S) (E S) rho cut) :
    Execution.HealthyPrefixDelivery S rho cut := by
  refine {
    broadcast := ?_
    relay_block := ?_
    relay_gf_vote := ?_
    relay_attest := ?_ }
  · intro v hv o t hemit w hw hbound hguard
    have hemit' := (emits_iff S rho v o t).2 hemit
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho (t + (E S).Δ) w) o = false := by
      rw [excludes_eq S rho (t + (E S).Δ) w o]
      exact hguard
    rcases h.broadcast v hv o t hemit' w hw hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w o t').1 hj⟩
  · intro v hv i B t hacc w hw hmiss hbound hguard
    have hacc' := (acceptsAt_iff S rho i v (.block B) t).2 hacc
    have hmiss' : (P S).processed
        (Generic.Run.stateBefore (P S) rho (i + 1) w) (.block B) = false := by
      rw [processed_eq S rho (i + 1) w (.block B)]
      exact hmiss
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho (t + (E S).Δ) w) (.block B) = false := by
      rw [excludes_eq S rho (t + (E S).Δ) w (.block B)]
      exact hguard
    rcases h.relay v hv i (.block B) t hacc' w hw hmiss' hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.block B) t').1 hj⟩
  · intro v hv i u t hacc w hw hmiss hbound hguard
    have hacc' := (acceptsAt_iff S rho i v (.gfVote u) t).2 hacc
    have hmiss' : (P S).processed
        (Generic.Run.stateBefore (P S) rho (i + 1) w) (.gfVote u) = false := by
      rw [processed_eq S rho (i + 1) w (.gfVote u)]
      exact hmiss
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho (t + (E S).Δ) w) (.gfVote u) = false := by
      rw [excludes_eq S rho (t + (E S).Δ) w (.gfVote u)]
      exact hguard
    rcases h.relay v hv i (.gfVote u) t hacc' w hw hmiss' hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.gfVote u) t').1 hj⟩
  · intro v hv i a t hacc w hw hmiss hbound hguard
    have hacc' := (acceptsAt_iff S rho i v (.attest a) t).2 hacc
    have hmiss' : (P S).processed
        (Generic.Run.stateBefore (P S) rho (i + 1) w) (.attest a) = false := by
      rw [processed_eq S rho (i + 1) w (.attest a)]
      exact hmiss
    have hguard' : (P S).excludes
        (Generic.Run.stateBeforeTime (P S) rho (t + (E S).Δ) w) (.attest a) = false := by
      rw [excludes_eq S rho (t + (E S).Δ) w (.attest a)]
      exact hguard
    rcases h.relay v hv i (.attest a) t hacc' w hw hmiss' hbound hguard' with
      ⟨t', htle, htlt, j, hj⟩
    exact ⟨t', htle, htlt, j, (handlesAt_iff S rho j w (.attest a) t').1 hj⟩

theorem slashableBound_of_generic
    (S : Setup V) (rho : Run V)
    (h : Generic.SlashableBound (I S) rho) :
    Statements.SlashableBound (Statements.«instance» S) rho := by
  intro c c' hc hc'
  exact h c c' hc hc'

theorem honestCommittees_of_generic
    (S : Setup V) (H : Finset V)
    (h : Generic.HonestCommittees (I S) H) :
    Statements.HonestCommittees (Statements.«instance» S) H := by
  intro s
  exact h s

end Proofs
end DecoupledConsensusModel

end
