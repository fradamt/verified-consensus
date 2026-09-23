module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.GSTZero
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-! # Recovery-free raw honest-height progress helpers -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every admissible run with honest committees has a positive public honest
height frontier at each inclusive read. -/
theorem one_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (t : Time) :
    1 ≤ honestHMaxAt S rho t := by
  obtain ⟨v, hv⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hgenesis : (Block.genesis : Block V) ∈
      (rho.storeAt S v t).T :=
    ((parentClosed_iff (rho.storeAt S v t).core).mp
      (Proofs.NamedStoreBridge.parentClosed_stateAt S rho t v)).1
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateAt S rho t v hgenesis
  have hbound := Proofs.NamedStoreBridge.heights_le_hMax_stateAt S rho t v D hD
  have hDgen : D = NamedBlock.genesis := by
    cases D with
    | genesis => rfl
    | node p s r votes support rows proposer =>
        simp [NamedBlock.erase] at hDerase
  have hheight : (Protocol.derive_named S.E S.cfg D).h = 1 := by
    rw [hDgen]; rfl
  have hlocal : 1 ≤ (rho.storeAt S v t).h_max :=
    calc
      1 = (Protocol.derive_named S.E S.cfg D).h := hheight.symm
      _ ≤ (rho.storeAt S v t).h_max := hbound
  exact hlocal.trans (localHMax_le_honestHMaxAt S rho t hv)




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
