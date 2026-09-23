module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore

@[expose] public section

namespace DecoupledConsensusModel
namespace Protocol
open Internal Execution
variable {V : Type} [DecidableEq V] [Fintype V]
namespace HonestWeightMajority

/-- Every honest committee has an honest member. -/
theorem exists_honest_committee_member
    {S : Setup V} {H : Finset V} (hcom : HonestCommittees S H)
    (s : Slot) : ∃ v, v ∈ H ∧ v ∈ S.E.committee s := by
  have hpositive : 0 < ((S.E.committee s) ∩ H).card := by
    have hmajority := hcom s
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpositive
  exact ⟨v, (Finset.mem_inter.mp hv).2, (Finset.mem_inter.mp hv).1⟩

end HonestWeightMajority
end Protocol
end DecoupledConsensusModel

end
