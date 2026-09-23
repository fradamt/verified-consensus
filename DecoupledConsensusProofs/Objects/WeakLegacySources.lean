module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.WeakHeightBounds
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Objects.WeakFGRoot
public import DecoupledConsensusProofs.Protocol.Grades.SafetyCompatibilityJoin
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationAdoption
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapSlot
public import DecoupledConsensusProofs.Protocol.Grades.SafetySlotInduction
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakSGWindow
public import DecoupledConsensusProofs.Protocol.Grades.WeakFiniteWindow
public import DecoupledConsensusProofs.Execution.HandoverLegacyFinality
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory

@[expose] public section

/-!
# Finite old-source evidence for the weak safety fold

Old rows have a finite height cap. Bootstrap rows retain their protected
confirmation witnesses, including timeout rows. These facts supply the
old-root and old-frontier conditions of the joint fold.

The low-finality certificate fact is separate from the continuation. Its
post-GST export can use the accountable bound; its cap-zero case does not.
A zero old-row cutoff has no old rows and requires no frontier gap.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakJoint

open Internal Execution Protocol Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

-- moved from DecoupledConsensusProofs/HealingSurface/WeakSafetyWindowRun.lean (C1)

/-- All height rows before the finite cutoff are bounded by the cap. -/
abbrev OldHeightRowsBounded (S : Setup V) (rho : Run V)
    (fresh : Round) (cap : Height) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time) (h : Height),
    a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
    a.round < fresh → a.height_pair.erase.height? = some h → h ≤ cap

/-- Protected witnesses of the finite bootstrap include timeout rows. -/
abbrev FGWitnessesBelow (S : Setup V) (rho : Run V)
    (fresh base : Round) (P : Block V) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time) (h : Height) (T : Block V),
    a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
    a.height_pair.erase.height? = some h →
    fresh ≤ a.round → a.round < base + S.hc.η_SG →
    fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some T →
    Block.Preceq T P



/- The finite honest frontier supplies the previous-row cap. -/
theorem oldHeightRowsBounded_of_honestFrontier
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) (fresh : Round) :
    OldHeightRowsBounded S rho fresh (honestHMaxAt S rho (S.a (fresh - 1))) := by
  intro a ta h ha hemit hold hrow
  apply WeakFG.honestEmittedHeight_le_honestHMaxAt S adm ha hemit hrow
  rw [(Proofs.Optimistic.emits_attest_shape S hemit).2]
  exact Assembly.a_mono S (Nat.le_sub_one_of_lt hold)

#print axioms oldHeightRowsBounded_of_honestFrontier

private theorem namedAncestorBodyMem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · exact ih (hpc.2 _ hB) hparent

private theorem lowFGRoot_preceq_of_named_frontier_gap
    (S : Setup V) {rho : Run V} {v : V} (hv : v ∈ rho.honest)
    {time : Time} {cap : Height} {P : Block V}
    (hlegacy : FinalizedRootsBelowAtRead S rho cap P)
    (hfrontier : cap + 1 < (rho.storeBeforeTime S v time).h_max)
    {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S v time).bodies)
    (hDR : D.erase = Protocol.get_fg_root
      (rho.storeBeforeTime S v time).toHealing.toFG)
    (hheight : (derive_named S.E S.cfg D).h ≤ cap) :
    Block.Preceq
      (Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG) P := by
  let st := rho.storeBeforeTime S v time
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st := by
    simpa only [st] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time v).1.1.1
  have hpc := hcoh.2.2.1
  by_cases hgate : st.core.h_max = st.core.h_j + 1
  · have hroot : Protocol.get_fg_root st.toHealing.toFG = st.core.J := by
      change (if st.core.h_max = st.core.h_j + 1 then st.core.J else st.core.F) =
        st.core.J
      exact if_pos hgate
    obtain ⟨J, hJ, hJJ, hJh⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho time v
    have hJJ' : (derive_named S.E S.cfg J).J = st.core.J := by
      simpa only [st] using hJJ
    have hJh' : (derive_named S.E S.cfg J).h_j = st.core.h_j := by
      simpa only [st] using hJh
    rcases NamedCheckpointHeights.justified_ancestor_height S.E S.cfg J with
      hz | ⟨K, hKJ, hKerase, hKheight⟩
    · have hgen : (derive_named S.E S.cfg J).J = Block.genesis :=
        NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg J hz
      have hstJ : st.core.J = Block.genesis := by
        exact hJJ'.symm.trans hgen
      rw [hroot, hstJ]
      exact Protocol.preceq_genesis P
    · have hK : K ∈ st.bodies := namedAncestorBodyMem hpc hJ hKJ
      have hKD : K.erase = D.erase := by
        calc
          K.erase = (derive_named S.E S.cfg J).J := hKerase
          _ = st.core.J := hJJ'
          _ = Protocol.get_fg_root st.toHealing.toFG := hroot.symm
          _ = D.erase := hDR.symm
      have hKD' : K = D := hcoh.2.1 K hK D hD hKD
      have hDheight : (derive_named S.E S.cfg D).h = st.core.h_j := by
        exact (congrArg (fun X => (derive_named S.E S.cfg X).h) hKD'.symm).trans
          (hKheight.trans hJh')
      have hcap : st.core.h_j ≤ cap := by
        rw [← hDheight]
        exact hheight
      have hmax : st.core.h_max ≤ cap + 1 := by
        rw [hgate]
        exact Nat.add_le_add_right hcap 1
      exact False.elim ((Nat.not_lt_of_ge hmax) hfrontier)
  · have hroot : Protocol.get_fg_root st.toHealing.toFG = st.core.F := by
      change (if st.core.h_max = st.core.h_j + 1 then st.core.J else st.core.F) =
        st.core.F
      exact if_neg hgate
    obtain ⟨F, hF, hFF, hFh⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho time v
    have hFF' : (derive_named S.E S.cfg F).F = st.core.F := by
      simpa only [st] using hFF
    rcases NamedCheckpointHeights.finalized_ancestor_height S.E S.cfg F with
      hz | ⟨K, hKF, hKerase, hKheight⟩
    · have hgen : (derive_named S.E S.cfg F).F = Block.genesis :=
        NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg F hz
      have hstF : st.core.F = Block.genesis := by
        exact hFF'.symm.trans hgen
      rw [hroot, hstF]
      exact Protocol.preceq_genesis P
    · have hK : K ∈ st.bodies := namedAncestorBodyMem hpc hF hKF
      have hKD : K.erase = D.erase := by
        calc
          K.erase = (derive_named S.E S.cfg F).F := hKerase
          _ = st.core.F := hFF'
          _ = Protocol.get_fg_root st.toHealing.toFG := hroot.symm
          _ = D.erase := hDR.symm
      have hKD' : K = D := hcoh.2.1 K hK D hD hKD
      have hDheight : (derive_named S.E S.cfg D).h =
          (derive_named S.E S.cfg F).h_F := by
        exact (congrArg (fun X => (derive_named S.E S.cfg X).h) hKD'.symm).trans
          hKheight
      have hcap : (derive_named S.E S.cfg F).h_F ≤ cap := by
        rw [← hDheight]
        exact hheight
      change Block.Preceq (Protocol.get_fg_root st.toHealing.toFG) P
      rw [hroot, ← hFF']
      exact hlegacy v hv time F hF hcap

theorem oldFGRoot_preceq_of_finiteBootstrap_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {fresh base : Round} {cap : Height} {P : Block V} {boundary time : Time}
    (holdRows : OldHeightRowsBounded S rho fresh cap)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P)
    (hfrontier : fresh = 0 ∨ ∀ w ∈ rho.honest,
      cap + 1 < (rho.storeBeforeTime S w boundary).h_max)
    (hfgAll : FGWitnessesBelow S rho fresh base P)
    {w : V} (hw : w ∈ rho.honest) (htime : boundary ≤ time)
    {C : NamedBlock V} {a : NamedAttestation V} {ta : Time}
    (hC : C ∈ (rho.storeBeforeTime S w time).bodies)
    (hJ : (derive_named S.E S.cfg C).J =
      Protocol.get_fg_root (rho.storeBeforeTime S w time).toHealing.toFG)
    (ha : a.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (hold : a.round < base + S.hc.η_SG)
    (hpair : a.height_pair.erase = HeightPair.target
      (derive_named S.E S.cfg C).h_j (derive_named S.E S.cfg C).J.root)
    (hT : fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
      some (Protocol.get_fg_root (rho.storeBeforeTime S w time).toHealing.toFG)) :
    Block.Preceq
      (Protocol.get_fg_root (rho.storeBeforeTime S w time).toHealing.toFG) P := by
  by_cases hpre : a.round < fresh
  · rcases NamedCheckpointHeights.justified_ancestor_height S.E S.cfg C with
      hz | ⟨D, hDC, hDR, hDheight⟩
    · have hgen : (derive_named S.E S.cfg C).J = Block.genesis :=
        NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg C hz
      have hrootgen : Protocol.get_fg_root
          (rho.storeBeforeTime S w time).toHealing.toFG = Block.genesis :=
        hJ.symm.trans hgen
      rw [hrootgen]
      exact Protocol.preceq_genesis P
    · have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
          (rho.storeBeforeTime S w time) :=
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time w).1.1.1
      have hD : D ∈ (rho.storeBeforeTime S w time).bodies :=
        namedAncestorBodyMem hcoh.2.2.1 hC hDC
      have hrow : a.height_pair.erase.height? =
          some (derive_named S.E S.cfg C).h_j := by
        simp only [hpair, HeightPair.height?]
      have hbound := holdRows a ta _ ha hemit hpre hrow
      have hDR' : D.erase = Protocol.get_fg_root
          (rho.storeBeforeTime S w time).toHealing.toFG := hDR.trans hJ
      have hDheight' : (derive_named S.E S.cfg D).h ≤ cap := by
        rw [hDheight]
        exact hbound
      rcases hfrontier with hzero | hgap
      · rw [hzero] at hpre
        exact False.elim (Nat.not_lt_zero _ hpre)
      · have hfrontier' := hgap w hw |>.trans_le
          (storeBeforeTime_hMax_mono S adm.toNamedScheduleWellFormed w htime)
        exact lowFGRoot_preceq_of_named_frontier_gap S hw hfinality hfrontier'
          hD hDR' hDheight'
  · exact hfgAll a ta (derive_named S.E S.cfg C).h_j
      (Protocol.get_fg_root (rho.storeBeforeTime S w time).toHealing.toFG)
      ha hemit (by simp only [hpair, HeightPair.height?])
      (Nat.le_of_not_gt hpre) hold hT

#print axioms oldFGRoot_preceq_of_finiteBootstrap_at_read

/-- The finite bootstrap supplies both compatibility FG-root callbacks used by the
history-cut fold. -/
theorem legacyRootCallbacks_of_finiteBootstrap_complete
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {fresh base : Round} {start last : Slot} {cap : Height} {P : Block V}
    (holdRows : OldHeightRowsBounded S rho fresh cap)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P)
    (hfrontier : fresh = 0 ∨ ∀ w ∈ rho.honest,
      cap + 1 < (rho.storeBeforeTime S w
        (min (S.a (base + S.hc.η_SG)) (Protocol.vote_time S.E start))).h_max)
    (hfgAll : FGWitnessesBelow S rho fresh base P) :
    (∀ r, base + S.hc.η_SG ≤ r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
      a.round < base + S.hc.η_SG →
      a.height_pair.erase = HeightPair.target
        (derive_named S.E S.cfg C).h_j (derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
      Block.Preceq R P) ∧
    (∀ d, start < d → d ≤ last + 1 → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root
        (voteDutyStore S rho w d).toHealing.toFG
      C ∈ (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).bodies →
      (derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E d →
      a.round < base + S.hc.η_SG →
      a.height_pair.erase = HeightPair.target
        (derive_named S.E S.cfg C).h_j (derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
      Block.Preceq R P) := by
  constructor
  · intro r hr ht w hw C a
    dsimp only
    intro hC hJ ha hemit hold hpair hT
    have hroot := actionStoreAt_fgRoot_eq_storeBeforeTime S rho w r
    have hC' : C ∈ (rho.storeBeforeTime S w (S.a r)).bodies := by
      simpa only [actionStoreAt, actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedDuties.update_confirmation_with,
        Protocol.update_confirmation_with, Protocol.NamedStore.setClock] using hC
    have hJ' : (derive_named S.E S.cfg C).J =
        Protocol.get_fg_root (rho.storeBeforeTime S w (S.a r)).toHealing.toFG := by
      rw [← hroot]
      exact hJ
    have hT' : fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some (Protocol.get_fg_root
          (rho.storeBeforeTime S w (S.a r)).toHealing.toFG) := by
      rw [← hroot]
      exact hT
    have hsafe := oldFGRoot_preceq_of_finiteBootstrap_at_read S adm holdRows hfinality
      hfrontier hfgAll hw
      ((min_le_left _ _).trans (Assembly.a_mono S hr)) hC' hJ' ha hemit hold hpair hT'
    simpa only [hroot] using hsafe
  · intro d hd hupper w hw C a ta
    dsimp only
    intro hC hJ ha hemit ht hold hpair hT
    have hroot : Protocol.get_fg_root
        (voteDutyStore S rho w d).toHealing.toFG =
        Protocol.get_fg_root
          (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing.toFG := by
      rfl
    have hJ' : (derive_named S.E S.cfg C).J =
        Protocol.get_fg_root
          (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing.toFG := by
      rw [← hroot]
      exact hJ
    have hT' : fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some (Protocol.get_fg_root
          (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing.toFG) := by
      rw [← hroot]
      exact hT
    exact oldFGRoot_preceq_of_finiteBootstrap_at_read S adm holdRows hfinality
      hfrontier hfgAll hw
      ((min_le_right _ _).trans (vote_time_mono_slots S.E (Nat.le_of_lt hd)))
      hC hJ' ha hemit hold hpair hT'

#print axioms legacyRootCallbacks_of_finiteBootstrap_complete



/-- Run-scoped named previous-frontier exclusion.
The named height and ancestry argument applies only to blocks from the run.
The previous erased fold also obtains both blocks from runtime stores, so this is
the exact additive contract for that consumer. -/
abbrev NoOldFrontierAtCutRunBlocks (S : Setup V) (rho : Run V) (cut : Round)
    (start last : Slot) (P : NamedBlock V) : Prop :=
  ∀ e : Slot, start < e → e ≤ last + 1 →
  ∀ C : NamedBlock V, RunBlock S rho C → NamedBlock.Preceq P C →
  ∀ w ∈ rho.honest,
  (derive_named S.E S.cfg C).h < (voteDutyStore S rho w e).h_max - 1 →
  ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
  RunBlock S rho K →
  a.val_index ∈ rho.honest → NamedRun.emits S rho a.val_index (Object.attest a) ta →
  ta < Protocol.vote_time S.E e →
  a.height_pair.erase.height? = some ((voteDutyStore S rho w e).h_max - 1) →
  a.round < cut →
  fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
    some (derive_named S.E S.cfg K).T_h →
  NamedBlock.compatible C K = true







end WeakJoint
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
