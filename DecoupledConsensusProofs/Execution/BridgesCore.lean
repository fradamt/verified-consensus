module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Execution.ReceiptCalls

@[expose] public section

/-! The named block-processing provenance bridge. -/
namespace DecoupledConsensusModel
namespace Proofs
namespace Bridges

open Execution
open Execution.NamedReceiptCalls
open NamedReceiptCallsBase

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A named block held by a prefix was processed there, unless it is genesis. -/
theorem processes_block_of_mem_T (S : Setup V) (rho : Run V) (v : V) :
    ∀ (i : Nat) (B : NamedBlock V), B ∈ (rho.stateBefore S i v).st.bodies →
      B = NamedBlock.genesis ∨
        ∃ (j : Nat) (e : Event V), j < i ∧ rho.events[j]? = some e ∧
          NamedRun.processes S rho v (Object.block B) e.time := by
  intro i
  induction i with
  | zero => intro B hB; exact Or.inl (Finset.mem_singleton.mp hB)
  | succ i ih =>
    intro B hB
    by_cases hpre : B ∈ (rho.stateBefore S i v).st.bodies
    · rcases ih B hpre with h | ⟨j, e, hj, hje, hproc⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, e, Nat.lt_succ_of_lt hj, hje, hproc⟩
    · refine Or.inr ?_
      obtain ⟨t, hacc⟩ := Proofs.NamedReceiptCalls.new_block_accepts S rho i v B hpre hB
      obtain ⟨⟨hidx, e, he, -, -⟩, -, -⟩ := hacc
      refine ⟨i, e, Nat.lt_succ_self i, he, ?_⟩
      rcases hidx with ⟨t', ht', hmem⟩ | ⟨t', ht'⟩
      · have heeq : e = NamedEvent.tick v t' := Option.some.inj (he.symm.trans ht')
        subst heeq
        exact Or.inl ⟨i, ht', hmem⟩
      · have heeq : e = NamedEvent.deliver v (.block B) t' :=
          Option.some.inj (he.symm.trans ht')
        subst heeq
        exact Or.inr ⟨i, ht'⟩

#print axioms processes_block_of_mem_T

end Bridges
end Proofs
end DecoupledConsensusModel

end
