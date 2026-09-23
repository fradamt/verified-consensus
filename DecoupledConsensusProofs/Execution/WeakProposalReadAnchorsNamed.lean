module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.WeakFGRoot
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakSGWindow
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryRelativeMajorityProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Execution.WeakGenesisGSTZeroActionSources

@[expose] public section

/-!
# Prepared weak-genesis proposal-read anchors

Named-store restatements of the GST-zero SG-root bounds. The explicit core
store equality keeps reduction away from the prepared named wrapper.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

namespace WeakGenesis


/-- A prepared core FG root read before the next vote is below the current
protected duty head. -/
theorem fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
    (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hcom : HonestCommittees S rho.honest)
    (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r)
    {last d : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {t : Time}
    (ht : t ≤ Protocol.vote_time S.E (d + 1))
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w t).core.toHealing.toFG)
      (voteDutyHead S rho x d) := by
  have hmajority := honestWeightMajority_of_finiteWindows S hawake hhor
  rcases WeakFG.fgRoot_confirmationWitness_at_read S adm hmajority hw t with
    hgen | ⟨C, hC, hJ, a, ta, ha, hemit, hat, _, hT⟩
  · rw [hgen]
    exact Protocol.preceq_genesis _
  · have haTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
      have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
      rw [← htime]
      exact hat.trans_le ht
    exact ((actionSources_preceq_voteDutyHead_of_gstZero
      S adm hcom hgst hawake hhor hd hupper hx a.round haTime).2
        a.val_index ha).2 _ hT

#print axioms fgRootAtRead_preceq_voteDutyHead_of_gstZero_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
