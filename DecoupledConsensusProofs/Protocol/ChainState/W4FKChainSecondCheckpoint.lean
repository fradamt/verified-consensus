module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainCheckpointAlgebra
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainCheckpointLift
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierFirstHalf
public import DecoupledConsensusProofs.Execution.W4FKLockAlignment
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The two pins -/

/-- Pin: every honest round-`r` action of the carrier reads the carrier's
slot-`+1` proposal as its action head. This is the conclusion of
`carrierActionHeadEq_of_namedActionHeadCone`
(`CanonicalRegimeSecondCheckpointRun.lean:1190`), whose own hypothesis is the
same statement with both proposals bound. -/
def W4SecondCarrierActionHeadPin (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  ∀ P1 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
    ∀ v ∈ rho.honest, Internal.actionHeadAt S rho v r = P1.erase

/-- Pin: earlier `commonFinalityAtConfirmation_of_proposedBlockCandidate`
(`RecurringFinalityRun.lean:1476`) in named form. An honest post-boundary
proposal that finalizes `T` at height `h` puts `T` below every honest store's
finalized checkpoint at its own confirmation duty. -/
def W4CommonFinalityAtConfirmationPin
    (S : Setup V) (rho : Run V) (q0 : Round) : Prop :=
  ∀ (s : Slot) (B : NamedBlock V) (T : Block V) (h : Height),
    0 < s →
    healingBoundaryTime S q0 < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    proposedBlockAt S rho s = some B →
    NamedFinalizedAt S.E S.cfg B T h →
    0 < h →
    T ≠ Block.genesis →
    ∀ v ∈ rho.honest,
      Block.Preceq T (rho.storeAt S v (Protocol.confirmation_time S.E s)).F ∧
        h ≤ (rho.storeAt S v
          (Protocol.confirmation_time S.E s)).core.finalized_height

/-! ## Local helpers -/

omit [Fintype V] in
private theorem w4scParentPreceq (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent,
        Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)

omit [Fintype V] in
private theorem w4scNamedTrans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hBC
      subst B
      exact hAB
  | node parent s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC
      rcases hBC with rfl | hparent
      · exact hAB
      · simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
        exact Or.inr (ih hparent)

/-- One named block advances the chain height by at most one. Named twin of
`derived_h_le_succ_of_parent` (`CanonicalRegimeSecondCheckpointRun.lean:196`). -/
theorem namedHeight_le_parent_succ (E : Env V) (cfg : Protocol.HeightConfig)
    (B : NamedBlock V) :
    (derive_named E cfg B).h ≤ (derive_named E cfg B.parent).h + 1 := by
  cases B with
  | genesis => exact Nat.le_succ _
  | node p s root gv gsv ats proposer =>
      rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p s root gv gsv
        ats proposer with hc | hc
      · exact hc.le.trans (Nat.le_succ _)
      · exact hc.le

/-- Copied from the private `W4CarrierFirstHalfRun.lean:250`
(`w4_openingSlot_pos`). -/
private theorem w4scOpeningSlotPos
    (S : Setup V) {q r : Round}
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r)) :
    0 < S.hc.opening_slot r := by
  by_contra hnot
  have heq : S.hc.opening_slot r = 0 := Nat.eq_zero_of_not_pos hnot
  have hproposalBoundary :
      Protocol.proposal_time S.E (S.hc.opening_slot r) <
        healingBoundaryTime S q := by
    rw [heq]
    unfold healingBoundaryTime
    exact lt_of_lt_of_le (Protocol.proposal_time_lt_vote_time S.E 0)
      (Protocol.vote_time_mono_slots S.E (Nat.zero_le _))
  exact (lt_asymm hafter) hproposalBoundary

/-! ## The second carrier's checkpoint -/

/-- Named proof of `carrierFinalitySecondCheckpointAt_of_regime`. Either the
second carrier's slot-`+1` proposal has already finalized at or above the first
carrier's opening height, in which case the phase's early arm fires, or its
live justification is unfinalized and the carrier's own prefix histories,
read at the justification height, clear the anti-slashing record there. -/
theorem carrierFinalitySecondCheckpointAt_of_regime_of_suffix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 source first second : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hroundSecond : CanonicalRegimeRoundAt S rho q0 second)
    (hheadPin : W4SecondCarrierActionHeadPin S rho second)
    (hconfPin : W4CommonFinalityAtConfirmationPin S rho q0)
    {Pfirst Q1 : NamedBlock V}
    (hPfirst : proposedBlockAt S rho (S.hc.opening_slot first) = some Pfirst)
    (hQ1 : proposedBlockAt S rho (S.hc.opening_slot second + 1) = some Q1)
    (hjust : (derive_named S.E S.cfg Pfirst).h ≤ (derive_named S.E S.cfg Q1).h_j)
    (habove : honestHMaxAt S rho (S.a q0) < (derive_named S.E S.cfg Pfirst).h)
    (hone : 1 < (derive_named S.E S.cfg Pfirst).h)
    (hsourceLower : S.a source ≤
      Protocol.proposal_time S.E (S.hc.opening_slot second + 1))
    (hendConf : Protocol.confirmation_time S.E
      (S.hc.opening_slot second + 1) ≤ S.a (second + 1))
    (hendHor : S.a (second + 1) ≤ rho.horizon) :
    CarrierFinalitySecondCheckpointAt S rho q0 source first second := by
  intro Pfirst' Q1' hPfirst' hQ1'
  have hPe : Pfirst = Pfirst' := Option.some.inj (hPfirst.symm.trans hPfirst')
  have hQe : Q1 = Q1' := Option.some.inj (hQ1.symm.trans hQ1')
  subst hPe
  subst hQe
  obtain ⟨P0, hP0⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot second)
  set hJ := (derive_named S.E S.cfg Q1).h_j with hJdef
  set J := (derive_named S.E S.cfg Q1).J with hJblockDef
  have hJone : 1 < hJ := hone.trans_le hjust
  have hJpos : 0 < hJ := Nat.zero_lt_of_lt hJone
  have habove' : honestHMaxAt S rho (S.a q0) < hJ := habove.trans_le hjust
  -- geometry of the two proposals
  have hslotPos : 0 < S.hc.opening_slot second :=
    w4scOpeningSlotPos S hroundSecond.afterBoundary
  have hhorOne : Protocol.proposal_time S.E (S.hc.opening_slot second + 1) ≤
      rho.horizon :=
    (Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans
      ((Protocol.proposal_time_le_confirmation_time S.E _).trans
        hroundSecond.inHorizon)
  have hafterSlot : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot second + 1) :=
    hroundSecond.afterBoundary.trans_le
      (Protocol.proposal_time_mono S.E (Nat.le_succ _))
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot second + 1) ≤ rho.horizon := hendConf.trans hendHor
  have hplusOneParent : proposedParent S rho (S.hc.opening_slot second + 1) =
      P0.erase :=
    (canonicalCarrierParentEqualities_of_canonicalSuffixFrom S adm hsuffix
      hroundSecond.afterBoundary hroundSecond.carrier hroundSecond.inHorizon
      P0 Q1 hP0 hQ1).1
  have hQ1parent : Q1.parent = P0 :=
    namedProposalParent_eq_of_honest S adm hslotPos hroundSecond.carrier.1
      hroundSecond.carrier.2.1 hhorOne hP0 hQ1 hplusOneParent
  have hP0Q1 : NamedBlock.Preceq P0 Q1 := hQ1parent ▸ w4scParentPreceq Q1
  have hheightStep : (derive_named S.E S.cfg Q1).h ≤
      (derive_named S.E S.cfg P0).h + 1 := by
    have := namedHeight_le_parent_succ S.E S.cfg Q1
    rwa [hQ1parent] at this
  have hJbelowOpening : hJ ≤ (derive_named S.E S.cfg P0).h :=
    Nat.le_of_lt_succ
      ((NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg
        Q1).justified_below_height.trans_le hheightStep)
  obtain ⟨Jn, hJnQ1, hJnErase, hJnSelf, hJnNj, hJnHeight⟩ :=
    namedJustificationWitness S.E S.cfg Q1
  rcases hJnHeight with hzero | hJnHeight
  · exact absurd hzero (Nat.ne_of_gt hJpos)
  -- the lock alignment at the justification height
  have hJnTarget : (derive_named S.E S.cfg Jn).T_h.root = J.root := by
    rw [hJnSelf, hJnErase]
  have halign : ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt (rho.stateBeforeTime S (S.a second) v).Λ
        (actionAttestationAt S rho v second).finality_pair hJ J.root := by
    rcases namedPreceq_or_preceq_of_common hJnQ1 hP0Q1 with hJnP0 | hP0Jn
    · have hraw := CanonicalRegimeRoundAt.successorTargetLockAlignment_of_canonicalHeight
        S adm hbot hroundSecond hP0 hJnP0 hJnHeight habove'
      simpa only [hJnTarget] using hraw
    · have hP0height : (derive_named S.E S.cfg P0).h = hJ :=
        Nat.le_antisymm ((Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
          hP0Jn).trans_eq hJnHeight) hJbelowOpening
      have hP0target : (derive_named S.E S.cfg P0).T_h.root = J.root := by
        rw [Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hP0Jn
          (hP0height.trans hJnHeight.symm), hJnSelf, hJnErase]
      have hraw := CanonicalRegimeRoundAt.successorTargetLockAlignment_of_canonicalHeight
        S adm hbot hroundSecond hP0 (Proofs.NamedAncestry.named_self P0) hP0height habove'
      simpa only [hP0target] using hraw
  by_cases hfinal : hJ ≤ (derive_named S.E S.cfg Q1).h_F
  · -- the chain has already finalized its live justification
    left
    have horder := NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg Q1
    have hFeq : (derive_named S.E S.cfg Q1).h_F = hJ :=
      Nat.le_antisymm horder.heights_ordered hfinal
    have hfinalized : NamedFinalizedAt S.E S.cfg Q1
        (derive_named S.E S.cfg Q1).F hJ := ⟨rfl, hFeq⟩
    have hFne : (derive_named S.E S.cfg Q1).F ≠ Block.genesis :=
      namedFinalizedCheckpoint_ne_genesis S.E S.cfg hfinalized hJone
    obtain ⟨cp, hcpLe, hcpErase, hcpHeight⟩ :=
      namedCheckpoint_of_namedFinalizedAt S.E S.cfg hfinalized hJpos
    have hQ1run : RunBlock S rho Q1 :=
      proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
        (S.hc.opening_slot second + 1) (Nat.zero_lt_succ _)
        hroundSecond.carrier.2.1 hhorOne hQ1
    have hcpRun : RunBlock S rho cp :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hQ1run hcpLe
    have hcpFinalized : NamedFinalizedAt S.E S.cfg Q1 cp.erase hJ := by
      rw [hcpErase]
      exact hfinalized
    have hcpNe : cp.erase ≠ Block.genesis := by
      rw [hcpErase]
      exact hFne
    have hcommon := hconfPin (S.hc.opening_slot second + 1) Q1 cp.erase hJ
      (Nat.zero_lt_succ _) hafterSlot hroundSecond.carrier.2.1 hconfHor hQ1
      hcpFinalized hJpos hcpNe
    exact ⟨S.hc.opening_slot second + 1, Q1, cp, hJ, Nat.zero_lt_succ _,
      hafterSlot, hroundSecond.carrier.2.1, hQ1, hcpRun, hcpFinalized, hjust,
      hcpHeight, hcpNe, hsourceLower,
      hsourceLower.trans (Protocol.proposal_time_le_confirmation_time S.E _),
      hendConf, hcommon⟩
  · -- the live justification is unfinalized: the record is clear at `hJ`
    right
    have hFlt : (derive_named S.E S.cfg Q1).h_F < hJ := Nat.lt_of_not_le hfinal
    refine ⟨hJ, J, hjust, ?_⟩
    intro v hv
    refine ⟨hheadPin Q1 hQ1 v hv, rfl, rfl, hFlt, ?_, ?_, ?_⟩
    · by_cases hnone : (rho.stateBeforeTime S (S.a second) v).Λ.target hJ = none
      · exact Or.inl hnone
      · obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hnone
        right
        obtain ⟨Q, -, hQP0, hQheight, hQtarget⟩ :=
          hroundSecond.targetHistory P0 hP0 v hv hJ X habove' hX
        have hQJ : (derive_named S.E S.cfg Q).T_h = J :=
          namedTarget_eq_justification_of_sameHeight S.E S.cfg
            (w4scNamedTrans hQP0 hP0Q1) hJpos hQheight
        rw [hX, ← hQtarget, hQJ]
    · by_cases hfalse :
        (rho.stateBeforeTime S (S.a second) v).Λ.timeout hJ = false
      · exact hfalse
      · exfalso
        have htrue : (rho.stateBeforeTime S (S.a second) v).Λ.timeout hJ = true :=
          Bool.eq_true_of_not_eq_false hfalse
        obtain ⟨Q, -, hQP0, hQheight, hQnj⟩ :=
          hroundSecond.timeoutHistory P0 hP0 v hv hJ habove' htrue
        have hQfalse : (derive_named S.E S.cfg Q).nj = false :=
          namedNj_false_at_justificationHeight S.E S.cfg
            (w4scNamedTrans hQP0 hP0Q1) hJpos hQheight
        rw [hQfalse] at hQnj
        exact Bool.noConfusion hQnj
    · by_cases hnone : (rho.stateBeforeTime S (S.a second) v).Λ.lock hJ = none
      · exact Or.inl hnone
      · obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hnone
        right
        have hXT : X = J.root := (halign v hv).1 X hX
        rw [hX, hXT]


#print axioms namedHeight_le_parent_succ
#print axioms carrierFinalitySecondCheckpointAt_of_regime_of_suffix

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
