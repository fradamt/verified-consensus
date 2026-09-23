module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakSGWindow
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakFrontierCandidate
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore

@[expose] public section

/-!
# Compatible SG history under core admissibility

Only actual honest emissions are constrained. Pool provenance proves the
emission and its awake gate. Grade batches and relative-majority windows
then preserve compatibility after old SG votes expire.

The joint induction must supply the protected history, the compatible live
confirmation, and the FG root/witness facts. These are not proved here.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakSG

open Internal Execution Internal.HealingSurface
open Proofs.Optimistic Protocol Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A pooled honest SG vote comes from its exact emitted action. -/
theorem honestSGVote_actionEmission_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w v : V} {time : Time} {k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ rho.honest)
    (hu : u ∈ (rho.storeBeforeTime S w time).toHealing.sg_votes k)
    (huv : u.val_index = v) :
    u = actionSGVoteAt S rho v k ∧
      rho.emits S v (Object.attest (actionAttestationAt S rho v k)) (S.a k) := by
  change u ∈
      ((rho.stateBeforeTime S time w).st.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed time
  have haN : a ∈ (rho.stateBefore S n w).st.sg_pool k := by
    rw [← hn]
    exact ha
  have haround : a.round = k :=
    Proofs.NamedStoreBridge.sgRounds_stateBefore S rho n w k a
      (List.mem_toFinset.mp haN)
  have hav : a.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hau
    have havu : a.val_index = u.val_index := by
      simpa only [Protocol.sgVote] using h
    exact havu.trans huv
  obtain ⟨j, e, o, hj, hje, hproc, hcarry⟩ :=
    Proofs.Optimistic.processes_attest_of_mem_sg_pool S rho w n k a haN
  obtain ⟨row, hrowEq, ta, hte, hemit⟩ :
      ∃ row : NamedAttestation V, a = row.erase ∧
        ∃ ta : Time, ta ≤ e.time ∧
          rho.emits S row.val_index (Object.attest row) ta := by
    cases o with
    | block Bl =>
        obtain ⟨row, hrowMem, hrowEq⟩ := hcarry
        have hrowV : row.val_index = v := by
          rw [hrowEq] at hav
          exact hav
        have hrowHon : row.val_index ∈ rho.honest := by
          rw [hrowV]
          exact hv
        obtain ⟨ta, hte, hemit⟩ := adm.toNamedUnforgeable.carried_attest
          w Bl e.time hproc row hrowMem hrowHon
        exact ⟨row, hrowEq, ta, hte, hemit⟩
    | gfVote voteObj => simp only [Proofs.Optimistic.CarriesRow] at hcarry
    | attest row =>
        have hrowEq : a = row.erase := hcarry
        have hrowV : row.val_index = v := by
          rw [hrowEq] at hav
          exact hav
        have hrowHon : row.val_index ∈ rho.honest := by
          rw [hrowV]
          exact hv
        obtain ⟨ta, hte, hemit⟩ := adm.toNamedUnforgeable.unforgeable
          w (Object.attest row) e.time hproc row.val_index hrowHon rfl
        exact ⟨row, hrowEq, ta, hte, hemit⟩
  have hrowHon : row.val_index ∈ rho.honest := by
    have hrowV : row.val_index = v := by
      rw [hrowEq] at hav
      exact hav
    rw [hrowV]
    exact hv
  have hrowRound : row.round = k := by
    rw [hrowEq] at haround
    exact haround
  have hemitV : rho.emits S v (Object.attest row) ta := by
    have hrowV : row.val_index = v := by
      rw [hrowEq] at hav
      exact hav
    exact hrowV ▸ hemit
  have hshape := Proofs.Optimistic.emits_attest_shape S hemitV
  have htime : ta = S.a k := by
    rw [hshape.2, hrowRound]
  have hiMem : Event.tick v ta ∈ rho.events := by
    obtain ⟨i, hi, -⟩ := hemitV
    exact List.mem_of_getElem? hi
  have hactionHor : S.a k ≤ rho.horizon := by
    have h := (adm.in_horizon (Event.tick v ta) hiMem).2
    simpa only [Event.time, htime] using h
  have hexact := honest_emits_exact_actionAttestationAt_of_awake S
    adm.toNamedScheduleWellFormed hv k
    (by simpa only [hrowRound] using Proofs.Optimistic.emits_attest_awake S hemitV)
    hactionHor
  have hrowAction : row = actionAttestationAt S rho v k :=
    Proofs.Optimistic.emits_attest_unique S adm.toNamedScheduleWellFormed
      hemitV hexact
      (hrowRound.trans (actionAttestationAt_shape S rho v k).2.1.symm)
  refine ⟨?_, hexact⟩
  calc
    u = Protocol.sgVote a := hau.symm
    _ = Protocol.sgVote row.erase := by rw [hrowEq]
    _ = Protocol.sgVote (actionAttestationAt S rho v k).erase := by
      rw [hrowAction]
    _ = actionSGVoteAt S rho v k := by
      have hshapeA := actionAttestationAt_shape S rho v k
      simp only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase,
        hshapeA.1, hshapeA.2.1, hshapeA.2.2]


/-- The selected SG block was already in the strict pre-action tree. -/
theorem actionSGBlockAt_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (r : Round) :
    actionSGBlockAt S rho v r ∈
      (rho.storeBeforeTime S v (S.a r)).T := by
  exact DecoupledConsensusModel.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime
    S rho v r



/-- Compatible emitted history controls each resolved honest SG pool entry. -/
theorem rootCompatible_of_emittedSGHistory_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {time : Time} {r : Round} {B : Block V}
    (hhistory : HonestSGEmissionsCompatibleAtRound S rho r B)
    {u : Protocol.SGVote V}
    (hu : u ∈ (rho.storeBeforeTime S w time).toHealing.sg_votes r)
    (huh : u.val_index ∈ rho.honest) :
    rootCompatible (rho.storeBeforeTime S w time).T B u.confirmed = true := by
  obtain ⟨huEq, hemit⟩ :=
    honestSGVote_actionEmission_of_mem_storeBeforeTime S adm huh hu rfl
  have hcompat := hhistory u.val_index huh hemit
  let C := actionSGBlockAt S rho u.val_index r
  have hconfirmed : u.confirmed = some C.root := by
    rw [huEq]
    rfl
  rw [hconfirmed]
  cases hfind : Block.find? (rho.storeBeforeTime S w time).T C.root with
  | none => simp only [rootCompatible, hfind]
  | some X =>
      have hXmem := find?_mem hfind
      obtain ⟨Xn, hXerase, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed hw time hXmem
      have hCmem : C ∈ (rho.storeBeforeTime S u.val_index (S.a r)).T :=
        actionSGBlockAt_mem_storeBeforeTime S adm u.val_index r
      obtain ⟨Cn, hCerase, hCrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed huh (S.a r) hCmem
      have hroot : Xn.root = Cn.root := by
        rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
          hXerase, hCerase]
        exact find?_root hfind
      have hnamed := adm.toNamedRootCollisionFree.root_injective
        Xn Cn hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self Cn)) hroot
      have hXC : X = C := hXerase.symm.trans
        ((congrArg NamedBlock.erase hnamed).trans hCerase)
      simpa only [rootCompatible, hfind, hXC] using hcompat


#print axioms honestSGVote_actionEmission_of_mem_storeBeforeTime
#print axioms actionSGBlockAt_mem_storeBeforeTime
#print axioms rootCompatible_of_emittedSGHistory_at_read






end WeakSG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
