module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore

@[expose] public section

/-!
# Raw height progress adapters

This module exposes the two concrete ways in which a low run step raises the
public honest `h_max` frontier, together with the bounded honest-proposal timing
witness used after one action batch.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



/-- Height-filter interference at an honest strict read raises the public honest
frontier by that read, rather than exposing only the reader's local store.

design note: bound at the named carrier `D` (`D ∈ (…).bodies`), the height read via
`derive_named`. -/
theorem heightFilterInterference_lt_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time} {H : Height} {D : NamedBlock V}
    (hDmem : D ∈ (rho.storeBeforeTime S w read).bodies)
    (hheight : H ≤ (Protocol.derive_named S.E S.cfg D).h)
    (hint : HeightFilterInterferenceAt
      (rho.storeBeforeTime S w read) D.erase) :
    H < honestHMaxAt S rho read := by
  have hstrict := heightFilterInterference_hMax
    S adm hw hDmem hheight hint
  have hlocal := storeBeforeTime_hMax_le_storeAt
    S adm.toNamedScheduleWellFormed w read
  have hpublic := localHMax_le_honestHMaxAt S rho read hw
  have hstep : H < H + 2 := by
    have hone : H < H + 1 := by
      simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_self H
    have htwo : H + 1 ≤ H + 2 :=
      Nat.add_le_add_left (by decide : 1 ≤ 2) H
    exact hone.trans_le htwo
  exact hstep.trans_le (hstrict.trans (hlocal.trans hpublic))


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
