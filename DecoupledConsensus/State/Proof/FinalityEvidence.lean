import DecoupledConsensus.State.Proof.TargetHeight

namespace DecoupledConsensus

/-! # Finality Evidence Invariant

Proof-only certificate tracking for the state variable `F`.

The executable `State` deliberately stores only the finalized block, not the
height or quorums that justified the assignment. This module recovers that
evidence from the chain history: whenever a chain-associated state has
`F = C`, either `C` is genesis or the included votes contain the finalize and
justify quorums needed for a `FinalizedCertificate`.
-/

variable {n : ℕ}

open scoped Block

namespace Block

private lemma genesis_ancestor (B : Block n) : Block.genesis ≼ B := by
  induction B with
  | genesis => exact .refl _
  | mk _ parent _ _ ih => exact .step ih

end Block

namespace FinalityEvidence

/-- Certificate-shaped evidence for the current finalized block of an
    intermediate state associated with a fixed chain. The last conjunct uses
    the intermediate state's height; when `σ = stateOf chain`, this converts
    directly to `FinalizedCertificate`. -/
def FinalityEvidenceInv {B : Block n} (chain : Chain n B)
    (votes : List (Vote n)) (σ : State n) : Prop :=
  ∃ C : Block n, ∃ h_f, C = σ.F ∧ ∃ hC : C ≼ B,
    (h_f = 0 ∧ C = Block.genesis) ∨
      (h_f > 0 ∧
        FinalizeQuorumWitness votes C h_f ∧
        JustifyQuorumWitness votes C h_f ∧
        (stateOf (chain.subchain hC)).h = h_f ∧
        σ.h > h_f)

lemma FinalizeQuorumWitness.append_right {votes extra : List (Vote n)}
    {C : Block n} {h_f : ℕ}
    (h : FinalizeQuorumWitness votes C h_f) :
    FinalizeQuorumWitness (votes ++ extra) C h_f := by
  rcases h with ⟨Q, hQ, hVotes⟩
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  obtain ⟨v, hv, hv_val, hv_fin⟩ := hVotes i hi
  exact ⟨v, by simp [hv], hv_val, hv_fin⟩

lemma JustifyQuorumWitness.append_right {votes extra : List (Vote n)}
    {C : Block n} {h_f : ℕ}
    (h : JustifyQuorumWitness votes C h_f) :
    JustifyQuorumWitness (votes ++ extra) C h_f := by
  rcases h with ⟨Q, hQ, hVotes⟩
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  obtain ⟨v, hv, hv_val, hv_target, hv_height⟩ := hVotes i hi
  exact ⟨v, by simp [hv], hv_val, hv_target, hv_height⟩

lemma FinalityEvidenceInv.append_votes {B : Block n} {chain : Chain n B}
    {votes extra : List (Vote n)} {σ : State n}
    (h : FinalityEvidenceInv chain votes σ) :
    FinalityEvidenceInv chain (votes ++ extra) σ := by
  rcases h with ⟨C, h_f, hCeq, hC, hCert⟩
  refine ⟨C, h_f, hCeq, hC, ?_⟩
  rcases hCert with hZero | hPos
  · exact Or.inl hZero
  · exact Or.inr
      ⟨hPos.1,
        FinalizeQuorumWitness.append_right hPos.2.1,
        JustifyQuorumWitness.append_right hPos.2.2.1,
        hPos.2.2.2.1,
        hPos.2.2.2.2⟩

lemma FinalityEvidenceInv.height_mono {B : Block n} {chain : Chain n B}
    {votes : List (Vote n)} {σ τ : State n}
    (hF : τ.F = σ.F) (hh : σ.h ≤ τ.h)
    (h : FinalityEvidenceInv chain votes σ) :
    FinalityEvidenceInv chain votes τ := by
  rcases h with ⟨C, h_f, hCeq, hC, hCert⟩
  refine ⟨C, h_f, ?_, hC, ?_⟩
  · exact hCeq.trans hF.symm
  rcases hCert with hZero | hPos
  · exact Or.inl hZero
  · exact Or.inr
      ⟨hPos.1, hPos.2.1, hPos.2.2.1, hPos.2.2.2.1,
        lt_of_lt_of_le hPos.2.2.2.2 hh⟩

lemma processVote_finalityEvidence_pres {B : Block n} (chain : Chain n B)
    (votes : List (Vote n)) (σ : State n) (v : Vote n)
    (h : FinalityEvidenceInv chain votes σ) :
    FinalityEvidenceInv chain (votes ++ [v]) (processVote σ v) := by
  have hApp : FinalityEvidenceInv chain (votes ++ [v]) σ :=
    h.append_votes
  exact FinalityEvidenceInv.height_mono
    (by simp [processVote_F]) (by simp [processVote_h]) hApp

lemma processBlock_finalityEvidence_pres {B : Block n} (chain : Chain n B)
    (votes : List (Vote n)) (σ : State n)
    (h : FinalityEvidenceInv chain votes ({ σ with L := B } : State n)) :
    FinalityEvidenceInv chain (votes ++ B.votes) (processBlock σ B) := by
  unfold processBlock
  suffices ∀ (pre : List (Vote n)) (τ : State n),
      FinalityEvidenceInv chain (votes ++ pre) τ →
      FinalityEvidenceInv chain (votes ++ pre ++ B.votes)
        (B.votes.foldl processVote τ) by
    simpa using this [] ({σ with L := B} : State n) (by simpa using h)
  intro pre τ hτ
  induction B.votes generalizing pre τ with
  | nil => simpa
  | cons v vs ih =>
      simp only [List.foldl_cons]
      have hStep : FinalityEvidenceInv chain (votes ++ pre ++ [v])
          (processVote τ v) :=
        processVote_finalityEvidence_pres chain (votes ++ pre) τ v hτ
      have hRest := ih (pre ++ [v]) (processVote τ v) (by simpa using hStep)
      simpa [List.append_assoc] using hRest

lemma processHeight_finalityEvidence_pres {B : Block n} (chain : Chain n B)
    (votes : List (Vote n)) (σ : State n)
    (hE : FinalityEvidenceInv chain votes σ)
    (hJ : JTargetHeightInv chain σ)
    (hJW : JWitnessInv votes σ)
    (hPW : PWitnessInv votes σ)
    (hZeroJ : HjZeroJGenesisInv σ)
    (hhj_lt_h : σ.hj < σ.h) :
    FinalityEvidenceInv chain votes (processHeight σ) := by
  by_cases hFinal : currentlyFinalBool σ = true
  · have hFpost : (processHeight σ).F = σ.J := by
      rw [processHeight_F]
      unfold applyFinality
      simp [hFinal]
    by_cases hhj0 : σ.hj = 0
    · refine ⟨Block.genesis, 0, ?_, Block.genesis_ancestor B,
        Or.inl ⟨rfl, rfl⟩⟩
      exact (hFpost.trans (hZeroJ hhj0)).symm
    · rcases hJ with hJZero | hJPos
      · exact False.elim (hhj0 hJZero.1)
      · rcases hJPos with ⟨C, hC, hAnc, hHeight⟩
        subst C
        have hCur : CurrentlyFinal σ :=
          (currentlyFinalBool_eq_true_iff σ).mp hFinal
        have hFinalize : FinalizeQuorumWitness votes σ.J σ.hj := by
          refine ⟨σ.P, hCur, ?_⟩
          intro i hi
          exact hPW i hi
        have hJustify : JustifyQuorumWitness votes σ.J σ.hj := by
          rcases hJW with hJWZero | hJWPos
          · exact False.elim (hhj0 hJWZero)
          · exact hJWPos
        have hPostHigh : (processHeight σ).h > σ.hj :=
          lt_of_lt_of_le hhj_lt_h (processHeight_h_le σ)
        refine ⟨σ.J, σ.hj, hFpost.symm, hAnc, Or.inr ?_⟩
        exact ⟨Nat.pos_of_ne_zero hhj0, hFinalize, hJustify, hHeight, hPostHigh⟩
  · have hFpost : (processHeight σ).F = σ.F := by
      rw [processHeight_F]
      unfold applyFinality
      simp [hFinal]
    exact FinalityEvidenceInv.height_mono hFpost (processHeight_h_le σ) hE

lemma processSlot_finalityEvidence_pres {B : Block n} (chain : Chain n B)
    (votes : List (Vote n)) (σ : State n)
    (hE : FinalityEvidenceInv chain votes σ)
    (hJ : JTargetHeightInv chain σ)
    (hJW : JWitnessInv votes σ)
    (hPW : PWitnessInv votes σ)
    (hZeroJ : HjZeroJGenesisInv σ)
    (hhj_lt_h : σ.hj < σ.h) :
    FinalityEvidenceInv chain votes (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · have hPH : FinalityEvidenceInv chain votes (processHeight σ) :=
      processHeight_finalityEvidence_pres chain votes σ hE hJ hJW hPW hZeroJ
        hhj_lt_h
    have hSet : FinalityEvidenceInv chain votes
        ({processHeight σ with s := σ.s + 1} : State n) := by
      exact FinalityEvidenceInv.height_mono (by simp) (by simp) hPH
    simpa [processSlot, hEmpty] using hSet
  · exact FinalityEvidenceInv.height_mono
      (by simp [processSlot, hEmpty]) (by simp [processSlot, hEmpty]) hE

lemma iterateProcessSlot_finalityEvidence_pres {B : Block n}
    (chain : Chain n B) (votes : List (Vote n)) (σ : State n) (k : ℕ)
    (hE : FinalityEvidenceInv chain votes σ)
    (hJ : JTargetHeightInv chain σ)
    (hTargets : TargetsHeightInv chain σ)
    (hTargetsAnc : TargetsAncInv σ)
    (hJW : JWitnessInv votes σ)
    (hPW : PWitnessInv votes σ)
    (hVW : VoteWitnessInv votes σ)
    (hZeroJ : HjZeroJGenesisInv σ)
    (hhj_lt_h : σ.hj < σ.h)
    (hL : σ.L = B) :
    FinalityEvidenceInv chain votes (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
      change FinalityEvidenceInv chain votes (iterateProcessSlot (processSlot σ) k)
      apply ih
      · exact processSlot_finalityEvidence_pres chain votes σ hE hJ hJW hPW
          hZeroJ hhj_lt_h
      · exact processSlot_JTargetHeight_pres chain σ hJ hTargets hTargetsAnc hL
      · exact processSlot_targetsHeight_pres chain σ hTargets
      · exact processSlot_targets_anc_pres σ hTargetsAnc
      · exact processSlot_JWitness_pres votes σ hJW hVW
      · exact processSlot_PWitness_pres votes σ hPW
      · exact processSlot_voteWitness_pres votes σ hVW
      · exact processSlot_HjZeroJGenesis_pres σ hZeroJ (by omega)
      · exact processSlot_hj_lt_h σ hhj_lt_h
      · rw [processSlot_L]
        exact hL

lemma FinalityEvidenceInv.extend_chain {parent : Block n}
    (c : Chain n parent) (bid : BlockId) (newSlot : ℕ)
    (votesNew : List (Vote n)) (hSlot : newSlot > parent.slot)
    (votes : List (Vote n)) (σ : State n)
    (h : FinalityEvidenceInv c votes σ) :
    FinalityEvidenceInv (Chain.extend c bid newSlot votesNew hSlot)
      votes ({σ with L := Block.mk bid parent newSlot votesNew} : State n) := by
  rcases h with ⟨C, h_f, hCeq, hC, hCert⟩
  refine ⟨C, h_f, hCeq, Block.Ancestor.step hC, ?_⟩
  rcases hCert with hZero | hPos
  · exact Or.inl hZero
  · right
    have hSame :
        (stateOf ((Chain.extend c bid newSlot votesNew hSlot).subchain
          (Block.Ancestor.step hC))).h =
          (stateOf (c.subchain hC)).h :=
      congrArg State.h (chain_unique _ _)
    exact ⟨hPos.1, hPos.2.1, hPos.2.2.1, by simpa [hSame] using hPos.2.2.2.1,
      hPos.2.2.2.2⟩

/-- Chain-level finality evidence for the finalized block in `stateOf chain`. -/
theorem chain_finalityEvidence {B : Block n} (chain : Chain n B) :
    FinalityEvidenceInv chain (votesIncluded chain) (stateOf chain) := by
  induction chain with
  | genesis =>
      refine ⟨Block.genesis, 0, rfl, Block.Ancestor.refl Block.genesis, Or.inl ?_⟩
      exact ⟨rfl, rfl⟩
  | @extend parent c bid newSlot votes hSlot ih =>
      let B' : Block n := Block.mk bid parent newSlot votes
      let chain' : Chain n B' := Chain.extend c bid newSlot votes hSlot
      let σ0 : State n := stateOf c
      let k : ℕ := B'.slot - σ0.s
      let σSlots : State n := iterateProcessSlot σ0 k
      let σBlock : State n := processBlock σSlots B'
      have hL0 : σ0.L = parent := by
        dsimp [σ0]
        exact chain_state_L_eq_tip c
      obtain ⟨_hPrefix0, hTargets0, hJ0⟩ := chain_height_target_invs c
      have hTargetsAnc0 : TargetsAncInv σ0 := by
        dsimp [σ0]
        exact chain_targets_anc c
      have hEInit : FinalityEvidenceInv chain'
          (votesIncluded c) ({σ0 with L := B'} : State n) := by
        dsimp [chain']
        exact ih.extend_chain c bid newSlot votes hSlot (votesIncluded c) σ0
      have hIterTarget := iterateProcessSlot_height_pres c σ0 k
        (chain_height_target_invs c).1 hTargets0 hJ0 hTargetsAnc0 hL0
      have hESlotsParent : FinalityEvidenceInv c (votesIncluded c) σSlots := by
        dsimp [σSlots, k, σ0]
        exact iterateProcessSlot_finalityEvidence_pres c (votesIncluded c)
          (stateOf c) (B'.slot - (stateOf c).s) ih hJ0 hTargets0 hTargetsAnc0
          (chain_JWitness c) (chain_PWitness c) (chain_voteWitness c)
          (chain_HjZeroJGenesis c) (chain_hj_lt_h c) hL0
      have hESlots : FinalityEvidenceInv chain'
          (votesIncluded c) ({σSlots with L := B'} : State n) := by
        dsimp [chain']
        exact hESlotsParent.extend_chain c bid newSlot votes hSlot
          (votesIncluded c) σSlots
      have hHeightPres := chain_height_target_invs chain'
      have hTargetsBlock : TargetsHeightInv chain' σBlock := by
        dsimp [σBlock, σSlots, k, σ0, B', chain']
        exact (processBlock_height_pres chain'
          (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
          (extend_strictHeight_init c bid newSlot votes hSlot
            (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
            hIterTarget.1)
          (extend_targetsHeight_init c bid newSlot votes hSlot
            (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
            hIterTarget.2.1
            (iterateProcessSlot_targets_anc_pres (stateOf c)
              (B'.slot - (stateOf c).s) (chain_targets_anc c))
            (by rw [iterateProcessSlot_L, chain_state_L_eq_tip]))
          (extend_JTargetHeight_init c bid newSlot votes hSlot
            (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
            hIterTarget.2.2)).2.1
      have hJBlock : JTargetHeightInv chain' σBlock := by
        dsimp [σBlock, σSlots, k, σ0, B', chain']
        exact (processBlock_height_pres chain'
          (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
          (extend_strictHeight_init c bid newSlot votes hSlot
            (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
            hIterTarget.1)
          (extend_targetsHeight_init c bid newSlot votes hSlot
            (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
            hIterTarget.2.1
            (iterateProcessSlot_targets_anc_pres (stateOf c)
              (B'.slot - (stateOf c).s) (chain_targets_anc c))
            (by rw [iterateProcessSlot_L, chain_state_L_eq_tip]))
          (extend_JTargetHeight_init c bid newSlot votes hSlot
            (iterateProcessSlot (stateOf c) (B'.slot - (stateOf c).s))
            hIterTarget.2.2)).2.2
      have hEBlock : FinalityEvidenceInv chain'
          (votesIncluded c ++ B'.votes) σBlock := by
        dsimp [σBlock, B']
        exact processBlock_finalityEvidence_pres chain' (votesIncluded c)
          σSlots hESlots
      have hTargetsAncBlock : TargetsAncInv σBlock := by
        dsimp [σBlock]
        apply processBlock_targets_anc_pres
        · dsimp [σSlots, k, σ0]
          exact iterateProcessSlot_targets_anc_pres (stateOf c)
            (B'.slot - (stateOf c).s) (chain_targets_anc c)
        · rw [iterateProcessSlot_L, chain_state_L_eq_tip]
          exact Block.Ancestor.step (Block.Ancestor.refl parent)
      have hVWBlock : VoteWitnessInv (votesIncluded c ++ B'.votes) σBlock := by
        dsimp [σBlock, B']
        apply processBlock_voteWitness_pres
        · dsimp [σSlots, k, σ0]
          exact iterateProcessSlot_voteWitness_pres (votesIncluded c) (stateOf c)
            (B'.slot - (stateOf c).s) (chain_voteWitness c)
        · rw [iterateProcessSlot_L, chain_state_L_eq_tip]
          exact Block.Ancestor.step (Block.Ancestor.refl parent)
      have hJWBlock : JWitnessInv (votesIncluded c ++ B'.votes) σBlock := by
        dsimp [σBlock, B']
        apply processBlock_JWitness_pres
        · dsimp [σSlots, k, σ0]
          exact iterateProcessSlot_JWitness_pres (votesIncluded c) (stateOf c)
            (B'.slot - (stateOf c).s) (chain_JWitness c) (chain_voteWitness c)
        · dsimp [σSlots, k, σ0]
          exact iterateProcessSlot_voteWitness_pres (votesIncluded c) (stateOf c)
            (B'.slot - (stateOf c).s) (chain_voteWitness c)
        · rw [iterateProcessSlot_L, chain_state_L_eq_tip]
          exact Block.Ancestor.step (Block.Ancestor.refl parent)
      have hPWBlock : PWitnessInv (votesIncluded c ++ B'.votes) σBlock := by
        dsimp [σBlock, B']
        apply processBlock_PWitness_pres
        dsimp [σSlots, k, σ0]
        exact iterateProcessSlot_PWitness_pres (votesIncluded c) (stateOf c)
          (B'.slot - (stateOf c).s) (chain_PWitness c)
      have hZeroBlock : HjZeroJGenesisInv σBlock := by
        dsimp [σBlock, B']
        apply processBlock_HjZeroJGenesis_pres
        dsimp [σSlots, k, σ0]
        exact iterateProcessSlot_HjZeroJGenesis_pres (stateOf c)
          (B'.slot - (stateOf c).s) (chain_HjZeroJGenesis c) (chain_h_pos c)
      have hhjBlock : σBlock.hj < σBlock.h := by
        dsimp [σBlock, B']
        simpa using
          iterateProcessSlot_hj_lt_h (stateOf c)
            (B'.slot - (stateOf c).s) (chain_hj_lt_h c)
      have hState : stateOf chain' = processHeight σBlock := by
        dsimp [chain', σBlock, σSlots, k, σ0, B', stateOf, stateTransition]
      change FinalityEvidenceInv chain' (votesIncluded c ++ B'.votes)
        (stateOf chain')
      rw [hState]
      exact processHeight_finalityEvidence_pres chain'
        (votesIncluded c ++ B'.votes) σBlock hEBlock hJBlock hJWBlock hPWBlock
        hZeroBlock hhjBlock

theorem chain_finalizedCertificate {B : Block n} (chain : Chain n B) :
    ∃ h_f, ∃ hF : (stateOf chain).F ≼ B,
      FinalizedCertificate chain (stateOf chain).F h_f hF := by
  rcases chain_finalityEvidence chain with ⟨C, h_f, hCeq, hC, hCert⟩
  subst hCeq
  refine ⟨h_f, hC, ?_⟩
  rcases hCert with hZero | hPos
  · exact Or.inl hZero
  · exact Or.inr hPos

end FinalityEvidence

end DecoupledConsensus
