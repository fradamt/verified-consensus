module
public import DecoupledConsensusModel

@[expose] public section

/-! Canonical wire facade for the selected full named protocol. The active
receipt path uses full named blocks, votes, and attestations. -/
namespace DecoupledConsensusModel.Execution

abbrev Object := NamedObject

namespace Object
abbrev block := @NamedObject.block
abbrev gfVote := @NamedObject.gfVote
abbrev attest := @NamedObject.attest
noncomputable abbrev rec := @NamedObject.rec
noncomputable abbrev recOn := @NamedObject.recOn
noncomputable abbrev casesOn := @NamedObject.casesOn
noncomputable abbrev noConfusion := @NamedObject.noConfusion
noncomputable abbrev noConfusionType := @NamedObject.noConfusionType
abbrev author := @NamedObject.author
abbrev wellFormed := @NamedReceipt.wellFormed
abbrev depsPresent := @NamedReceipt.depsPresent
abbrev processed := @NamedReceipt.processed
abbrev process := @NamedReceipt.process
end Object

end DecoupledConsensusModel.Execution

end
