module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Execution.NamedAdmissible
public import DecoupledConsensusProofs.Execution.ReceiptCallsBase

@[expose] public section

/-! Exact named formula checks and derived authentication for actual calls.
These are correspondences to the displayed named formulas, not an erasure
simulation or equality with compatibility direct-only receipt. -/
namespace DecoupledConsensusModel.Proofs.NamedNetworkBindings
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]









private theorem direct_index_processes_at (S : Setup V) (rho : NamedRun V)
    {i : Nat} {receiver : V} {o : NamedObject V} {t : Time}
    (hcall : NamedRun.processesAtIndex S rho i receiver o)
    (htimed : ∃ e : NamedEvent V, rho.events[i]? = some e ∧ e.node = receiver ∧ e.time = t) :
    NamedRun.processes S rho receiver o t := by
  obtain ⟨e, he, _, ht⟩ := htimed
  rcases hcall with ⟨time, hi, hem⟩ | ⟨time, hi⟩
  · have heq : NamedEvent.tick receiver time = e := Option.some.inj (hi.symm.trans he)
    have htime : time = t := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans ht
    subst time
    exact Or.inl ⟨i, hi, hem⟩
  · have heq : NamedEvent.deliver receiver o time = e := Option.some.inj (hi.symm.trans he)
    have htime : time = t := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans ht
    subst time
    exact Or.inr ⟨i, hi⟩

/-- The original carrier was actually processed by this recipient at this
same indexed event time. No retained-body observation substitutes for it. -/
private theorem block_call_processes_at (S : Setup V) (rho : NamedRun V)
    {i : Nat} {receiver : V} {B : NamedBlock V} {before : Protocol.NamedStore V} {t : Time}
    (hcall : Execution.NamedReceiptCalls.blockCallAt S rho i receiver B before)
    (htimed : ∃ e : NamedEvent V, rho.events[i]? = some e ∧ e.node = receiver ∧ e.time = t) :
    NamedRun.processes S rho receiver (.block B) t := by
  apply direct_index_processes_at S rho ?_ htimed
  rcases hcall with ⟨time, hi, _⟩ | ⟨time, hi, hem, _⟩
  · exact Or.inr ⟨time, hi⟩
  · exact Or.inl ⟨time, hi, hem⟩

/-- Authentication for real calls is derived from the three existing
full-object clauses. The proof does not require successful admission. -/
private theorem authentic_actual_handles_of_clauses (S : Setup V) (rho : NamedRun V)
    (hDirect : ∀ receiver o t, NamedRun.processes S rho receiver o t →
      ∀ author ∈ rho.honest, o.author = some author →
        ∃ sent, sent ≤ t ∧ NamedRun.emits S rho author o sent)
    (hCarriedGF : ∀ receiver B t, NamedRun.processes S rho receiver (.block B) t →
      ∀ u ∈ B.gf_votes, u.val_index ∈ rho.honest →
        ∃ sent, sent ≤ t ∧ NamedRun.emits S rho u.val_index (.gfVote u) sent)
    (hCarriedRow : ∀ receiver B t, NamedRun.processes S rho receiver (.block B) t →
      ∀ a ∈ B.attestations, a.val_index ∈ rho.honest →
        ∃ sent, sent ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) sent)
    {i : Nat} {receiver author : V} {o : NamedObject V} {t : Time}
    (h : NamedRun.actualHandlesAt S rho i receiver o t)
    (hHon : author ∈ rho.honest) (hAuthor : o.author = some author) :
    ∃ sent, sent ≤ t ∧ NamedRun.emits S rho author o sent := by
  obtain ⟨hcall, htimed⟩ := h
  cases o with
  | block B =>
    exact hDirect receiver (.block B) t
      (direct_index_processes_at S rho hcall htimed) author hHon hAuthor
  | gfVote u =>
    rcases hcall with hdirect | ⟨B, j, before, hcarrier, _, _, hindex⟩
    · exact hDirect receiver (.gfVote u) t
        (direct_index_processes_at S rho hdirect htimed) author hHon hAuthor
    · have hval : u.val_index = author := Option.some.inj hAuthor
      have hbody := block_call_processes_at S rho hcarrier htimed
      have hmember : u ∈ B.gf_votes := List.mem_of_getElem? hindex
      have hsigner : u.val_index ∈ rho.honest := hval.symm ▸ hHon
      simpa only [hval] using hCarriedGF receiver B t hbody u hmember hsigner
  | attest a =>
    rcases hcall with hdirect | ⟨B, j, before, hcarrier, _, _, hindex⟩
    · exact hDirect receiver (.attest a) t
        (direct_index_processes_at S rho hdirect htimed) author hHon hAuthor
    · have hval : a.val_index = author := Option.some.inj hAuthor
      have hbody := block_call_processes_at S rho hcarrier htimed
      have hmember : a ∈ B.attestations := List.mem_of_getElem? hindex
      have hsigner : a.val_index ∈ rho.honest := hval.symm ▸ hHon
      simpa only [hval] using hCarriedRow receiver B t hbody a hmember hsigner

/-- The typed authentication bundle supplies all premises of the derivation;
it gains no separate handler-authentication assumption. -/
theorem actual_handles_authenticated (S : Setup V) (rho : NamedRun V)
    (auth : NamedUnforgeable S rho)
    {i : Nat} {receiver author : V} {o : NamedObject V} {t : Time}
    (h : NamedRun.actualHandlesAt S rho i receiver o t)
    (hHon : author ∈ rho.honest) (hAuthor : o.author = some author) :
    ∃ sent, sent ≤ t ∧ NamedRun.emits S rho author o sent :=
  authentic_actual_handles_of_clauses S rho auth.unforgeable auth.carried_gf
    auth.carried_attest h hHon hAuthor


#print axioms actual_handles_authenticated
end DecoupledConsensusModel.Proofs.NamedNetworkBindings

end
