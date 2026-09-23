module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedReceiptCalls
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Schedule.NamedTick

@[expose] public section

/-! Common call bindings for the concrete named run. These results produce
recipient input stores from actual events and emissions. Per-row F1 and internal
checked-GF prefix proofs are separate consumers of this common interface. -/
namespace DecoupledConsensusModel.Proofs.NamedReceiptCallsBase
open Execution
open Execution.NamedReceiptCalls
variable {V : Type} [DecidableEq V] [Fintype V]

theorem blockCallAt_delivery (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v (.block B) t)) :
    blockCallAt S rho i v B (NamedRun.stateBefore S rho i v).st :=
  Or.inl ⟨t, hi, rfl⟩

theorem blockCallAt_self (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t))
    (hB : NamedObject.block B ∈ NamedRun.emittedAt S rho i v t) :
    blockCallAt S rho i v B
      (Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t) :=
  Or.inr ⟨t, hi, hB, rfl⟩


/-- The call's input is an actual prefix or its actual clock staging. -/
theorem block_call_before_invariant (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {B : NamedBlock V} {before : Protocol.NamedStore V}
    (h : blockCallAt S rho i v B before) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg before := by
  have hpre := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1
  rcases h with ⟨t, _, rfl⟩ | ⟨t, _, _, rfl⟩
  · exact hpre
  · exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ t hpre


theorem delivery_result (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {o : NamedObject V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) :
    (NamedRun.stateBefore S rho (i + 1) v).st =
      NamedReceipt.process S (NamedRun.stateBefore S rho i v).st o := by
  rw [Proofs.NamedRuntime.stateBefore_deliver S rho hi]
  rfl


private theorem emitted_block_proposal (gc : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (B : NamedBlock V)
    (hB : NamedObject.block B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2) :
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd
      (Protocol.NamedStore.setClock E st t)).2 = some B := by
  rw [NamedTick.tick_computed_duties] at hB
  dsimp only at hB
  generalize hp : Protocol.NamedDuties.propose_block_with gc E hc cfg nd
    (Protocol.NamedStore.setClock E st t) = proposed at hB ⊢
  rcases proposed with ⟨after, result⟩
  cases result with
  | none =>
    split_ifs at hB <;> simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, or_false, and_false, exists_false] at hB
  | some C =>
    have hBC : B = C := by
      split_ifs at hB <;>
        simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_false, and_false, exists_false] at hB <;>
        exact NamedObject.block.inj hB
    rw [hBC]

-- Retain the actual-event witness in this public call-site interface; the
-- output equation itself follows from the computed emission.
set_option linter.unusedVariables false in
/-- A self-emitted block identifies the exact proposal invocation and its
closed named block/F1 result. No lookup or open premise is added. -/
theorem self_proposal_call (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {t : Time} {B : NamedBlock V}
    (hi : rho.events[i]? = some (.tick v t))
    (hB : NamedObject.block B ∈ NamedRun.emittedAt S rho i v t) :
    let n := NamedRun.stateBefore S rho i v
    let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
    let before := Protocol.NamedStore.setClock S.E n.st t
    Protocol.NamedDuties.propose_block_with (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) before =
        (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before B,
          some B) := by
  dsimp only
  let n := NamedRun.stateBefore S rho i v
  let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
  have hp := emitted_block_proposal (DecoupledConsensusModel.Protocol.frameContract c)
    S.E S.hc S.cfg (S.node v) n.st n.record t B hB
  unfold Protocol.NamedDuties.propose_block_with at hp ⊢
  split at hp
  · cases hp
  · rename_i C hC
    have hCB : C = B := Option.some.inj hp
    subst C
    rw [hC]






#print axioms blockCallAt_delivery
#print axioms blockCallAt_self
#print axioms block_call_before_invariant
#print axioms delivery_result
#print axioms self_proposal_call
end DecoupledConsensusModel.Proofs.NamedReceiptCallsBase

end
