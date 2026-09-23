module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4Direct
public import DecoupledConsensusProofs.Objects.HandoverPreparedV4Transfer
public import DecoupledConsensusProofs.Execution.PreparedV4Finality
public import DecoupledConsensusProofs.Execution.PreparedV4VoteSourcesClosed
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

/-! # Weak vote continuation from the prepared V4 handover -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The direct prepared V4 selector supplies the exact public safety cut.
The finite record transfers to each weak continuation, where accountable
finality and the continuation awake windows close every later vote source. -/
theorem weakVoteContinuation_preparedV4
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} {delayExtra : Nat}
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hrec : MultiProposerRecurrence S rho gap) :
    WeakVoteContinuation S rho rGST gap (progressLag' gap delayExtra) := by
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let L := progressLag' gap delayExtra
  let base : Round := D + 2 * L + 1
  let cut := safetyCutBound S rho rGST L
  have hcut : cut = base + S.hc.η_SG := by
    rfl
  refine ⟨cut, ?_, le_rfl, ?_⟩
  · have hrD : rGST ≤ D := by
      dsimp only [D, fgSafetyProgressDeadline]
      exact (Nat.le_succ rGST).trans (Nat.le_add_right (rGST + 1) _)
    rw [hcut]
    exact hrD.trans ((Nat.le_add_right D (2 * L + 1)).trans
      (Nat.le_add_right base S.hc.η_SG))
  · intro hhor
    obtain ⟨m, hmlo, hmhi, _, P, hP, hboot, hheight⟩ :=
      Handover.settledBootstrap_of_strong_preparedV4
        S adm hcom hbelow hdelay hrec hpost (n := cut)
          (by rw [hcut]) hhor
    refine ⟨m, hmlo, hmhi, P, hP, ?_⟩
    intro rho' execution' synchrony' hcom' hsb' hagree hawake d hd hdhor
    let adm' := Proofs.AdmissibleCore.ofParts execution' synchrony'
    have hfresh : D + 1 ≤ base + S.hc.η_SG := by
      dsimp only [base]
      exact (Nat.add_le_add_left (Nat.le_add_left 1 (2 * L)) D).trans
        (Nat.le_add_right (D + 2 * L + 1) S.hc.η_SG)
    have hboot' := Handover.SettledBootstrapPreparedV4.transfer
      S adm.toNamedAdmissibleCore adm' hcom' hboot hfresh hagree
    have hfinality :=
      Handover.SettledBootstrapPreparedV4.finalizedRootsBelowAtRead_of_accountable
        S adm' hsb' hboot' hheight
    have hawake' : ∀ r, base + S.hc.η_SG ≤ r →
        S.a (r - 1) ≤ rho'.horizon →
        AwakeWindowMajority S.E (fun v => (S.node v).awake)
          rho'.honest S.hc.η_SG r := by
      intro r hr hround
      exact hawake r (hcut.symm ▸ hr) hround
    rw [hcut]
    exact Handover.SettledBootstrapPreparedV4.voteSourcesSafeAt_core
      S adm' hcom' hboot' hawake' hfinality hd hdhor

#print axioms weakVoteContinuation_preparedV4

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
