module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.HeightRegimeNamedBase
public import DecoupledConsensusProofs.Protocol.Grades.HeightRegimeNamedRunScoped
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressCompose
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightProgressFixedRoot
public import DecoupledConsensusProofs.Execution.SeedSourceCapClosure
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedRootSourceCap
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointAlgebra
public import DecoupledConsensusProofs.Execution.FinalityAgreement

@[expose] public section

/-!
# Run-scoped named height-regime base by the progress deadline

This is the additive  twin of earlier's bounded two-arm join. The recovery
arm weakens the existing named base. The finalized arm constructs the
run-scoped base directly, so the prior-root witness is known to be a run block.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic
open Proofs.HealingLemmas Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

omit [Fintype V] in
private theorem named_preceq_self_deadline (B : NamedBlock V) :
    NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem named_preceq_extend_deadline {A P : NamedBlock V}
    (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A P) :
    NamedBlock.Preceq A (.node P s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

omit [Fintype V] in
private theorem named_genesis_preceq_deadline (B : NamedBlock V) :
    NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => exact named_preceq_self_deadline _
  | node parent slot root votes support rows proposer ih =>
      exact named_preceq_extend_deadline slot root votes support rows proposer ih

omit [Fintype V] in
private theorem named_preceq_or_preceq_common_deadline
    {A B C : NamedBlock V} (hA : NamedBlock.Preceq A C)
    (hB : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
  induction C with
  | genesis =>
      have hAg : A = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq,
          decide_eq_true_eq] using hA
      have hBg : B = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq,
          decide_eq_true_eq] using hB
      subst A
      subst B
      exact Or.inl (named_preceq_self_deadline _)
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hA hB
      rcases hA with rfl | hA
      · rcases hB with rfl | hB
        · exact Or.inl (named_preceq_self_deadline _)
        · exact Or.inr
            (named_preceq_extend_deadline slot root votes support rows proposer hB)
      · rcases hB with rfl | hB
        · exact Or.inl
            (named_preceq_extend_deadline slot root votes support rows proposer hA)
        · exact ih hA hB

omit [Fintype V] in
private theorem fold_F_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).F = st.F :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.2.1

omit [Fintype V] in
private theorem fold_h_F_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_F = st.h_F :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.2.2

omit [Fintype V] in
private theorem fold_J_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).J = st.J :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem fold_h_j_deadline (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_j = st.h_j :=
  (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.1

/-- A positive named finalization has a full named checkpoint witness which is
the height entry at its own height. -/
private theorem namedFinalization_selfTarget_deadline
    (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V)
    (hpos : 0 < (derive_named E cfg B).h_F) :
    ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
      F.erase = (derive_named E cfg B).F ∧
      (derive_named E cfg F).h = (derive_named E cfg B).h_F ∧
      (derive_named E cfg F).T_h = F.erase := by
  induction B with
  | genesis => simp [derive_named, ChainState.initial] at hpos
  | node parent slot root votes support rows proposer ih =>
      let B := NamedBlock.node parent slot root votes support rows proposer
      let folded := fold_rows (TimeoutBinding.targeted V)
        (derive_named E cfg parent) B.erase rows
      have hstate : derive_named E cfg B = process_height_events E cfg folded := rfl
      have hafterF : (Protocol.afterFin E folded).F =
          (derive_named E cfg B).F := by
        rw [hstate, Protocol.process_height_events_eq]
        split_ifs <;> rfl
      have hafterH : (Protocol.afterFin E folded).h_F =
          (derive_named E cfg B).h_F := by
        rw [hstate, Protocol.process_height_events_eq]
        split_ifs <;> rfl
      by_cases hfinal : finalityReady E folded = true
      · simp only [Protocol.afterFin_F, Protocol.afterFin_h_F,
          if_pos hfinal] at hafterF hafterH
        have hparentPos : 0 < (derive_named E cfg parent).h_j := by
          rw [← fold_h_j_deadline]
          rw [hafterH]
          exact hpos
        obtain ⟨J, hJ, hJerase, hJheight, hJtarget⟩ :=
          NamedCheckpointAlgebra.namedJustification_selfTarget
            E cfg parent hparentPos
        refine ⟨J,
          named_preceq_extend_deadline slot root votes support rows proposer hJ,
          ?_, ?_, hJtarget⟩
        · calc
            J.erase = (derive_named E cfg parent).J := hJerase
            _ = folded.J :=
              (fold_J_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).F := hafterF
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).F := rfl
        · calc
            (derive_named E cfg J).h =
                (derive_named E cfg parent).h_j := hJheight
            _ = folded.h_j :=
              (fold_h_j_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).h_F := hafterH
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).h_F := rfl
      · simp only [Protocol.afterFin_F, Protocol.afterFin_h_F,
          if_neg hfinal] at hafterF hafterH
        have hparentPos : 0 < (derive_named E cfg parent).h_F := by
          rw [← fold_h_F_deadline]
          rw [hafterH]
          exact hpos
        obtain ⟨F, hF, hFerase, hFheight, hFtarget⟩ := ih hparentPos
        refine ⟨F,
          named_preceq_extend_deadline slot root votes support rows proposer hF,
          ?_, ?_, hFtarget⟩
        · calc
            F.erase = (derive_named E cfg parent).F := hFerase
            _ = folded.F :=
              (fold_F_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).F := hafterF
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).F := rfl
        · calc
            (derive_named E cfg F).h =
                (derive_named E cfg parent).h_F := hFheight
            _ = folded.h_F :=
              (fold_h_F_deadline (derive_named E cfg parent) B.erase rows).symm
            _ = (derive_named E cfg B).h_F := hafterH
            _ = (derive_named E cfg
                (.node parent slot root votes support rows proposer)).h_F := rfl

/-- Two run-scoped named entry witnesses at the same height are equal when
their erasures are compatible. -/
private theorem namedEntries_eq_of_compatible_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hArun : RunBlock S rho A)
    (hBrun : RunBlock S rho B)
    (hAself : (derive_named S.E S.cfg A).T_h = A.erase)
    (hBself : (derive_named S.E S.cfg B).T_h = B.erase)
    (hh : (derive_named S.E S.cfg A).h =
      (derive_named S.E S.cfg B).h)
    (hcompat : Block.compatible A.erase B.erase = true) : A = B := by
  have hlinear : Block.Preceq A.erase B.erase ∨
      Block.Preceq B.erase A.erase := by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompat
  rcases hlinear with hAB | hBA
  · have hABn := Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hArun hBrun hAB
    have hentry := Proofs.NamedEntryHeight.entry_eq_on_plateau
      S.E S.cfg hABn hh
    have herase : A.erase = B.erase := hAself.symm.trans (hentry.trans hBself)
    exact adm.toNamedRootCollisionFree.root_injective A B hArun hBrun A B
      (Or.inl (named_preceq_self_deadline A))
      (Or.inr (named_preceq_self_deadline B))
      (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])
  · have hBAn := Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hBrun hArun hBA
    have hentry := Proofs.NamedEntryHeight.entry_eq_on_plateau
      S.E S.cfg hBAn hh.symm
    have herase : B.erase = A.erase := hBself.symm.trans (hentry.trans hAself)
    exact (adm.toNamedRootCollisionFree.root_injective B A hBrun hArun B A
      (Or.inl (named_preceq_self_deadline B))
      (Or.inr (named_preceq_self_deadline A))
      (by rw [← Proofs.NamedWire.erase_root B, ← Proofs.NamedWire.erase_root A,
        herase])).symm

/-- A named justification at a globally finalized height is that finalized
entry. -/
private theorem namedJustified_eq_finalized_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {C BF F : NamedBlock V} (hCrun : RunBlock S rho C)
    (hBFrun : RunBlock S rho BF) (hFrun : RunBlock S rho F)
    (hFpre : NamedBlock.Preceq F BF)
    (hFerase : F.erase = (derive_named S.E S.cfg BF).F)
    (hFheight : (derive_named S.E S.cfg F).h =
      (derive_named S.E S.cfg BF).h_F)
    (hFself : (derive_named S.E S.cfg F).T_h = F.erase)
    (hJheight : (derive_named S.E S.cfg C).h_j =
      (derive_named S.E S.cfg BF).h_F) :
    (derive_named S.E S.cfg C).J = F.erase := by
  have hJpos : 0 < (derive_named S.E S.cfg C).h_j := by
    rw [hJheight, ← hFheight]
    exact Protocol.one_le_derive_named_h S.E S.cfg F
  obtain ⟨J, hJC, hJerase, hJheight', hJself⟩ :=
    NamedCheckpointAlgebra.namedJustification_selfTarget
      S.E S.cfg C hJpos
  have hJrun : RunBlock S rho J :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hJC
  have hlt : (derive_named S.E S.cfg BF).h_F <
      (derive_named S.E S.cfg C).h := by
    rw [← hJheight]
    exact (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg C).justified_below_height
  have hFCraw : Block.Preceq F.erase C.erase := by
    simpa only [hFerase] using
      (NamedFinalizationBridge.finalized_preceq_of_height_lt
        S rho C BF hsb adm.toNamedRootCollisionFree hCrun hBFrun hlt)
  have hFC : NamedBlock.Preceq F C :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hFrun hCrun hFCraw
  rcases named_preceq_or_preceq_common_deadline hJC hFC with hJF | hFJ
  · have hentry := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hJF
      (hJheight'.trans (hFheight.trans hJheight.symm).symm)
    have herase : J.erase = F.erase := hJself.symm.trans (hentry.trans hFself)
    exact hJerase.symm.trans herase
  · have hentry := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hFJ
      (hFheight.trans (hJheight.symm.trans hJheight'.symm))
    have herase : F.erase = J.erase := hFself.symm.trans (hentry.trans hJself)
    exact hJerase.symm.trans herase.symm

/-- A finalized named checkpoint supplies the named frame before the next
crossing. -/
private theorem namedHeightRegimeFrame_of_finalizedRun
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {stop : Nat} {blocked : Height} {c0 : Round}
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {BF F : NamedBlock V} (hBFrun : RunBlock S rho BF)
    (hFpre : NamedBlock.Preceq F BF)
    (hFerase : F.erase = (derive_named S.E S.cfg BF).F)
    (hFheight : (derive_named S.E S.cfg F).h = blocked)
    (hBFheight : (derive_named S.E S.cfg BF).h_F = blocked)
    (hFself : (derive_named S.E S.cfg F).T_h = F.erase) :
    NamedHeightRegimeFrame S rho blocked stop F c0 := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hFrun : RunBlock S rho F :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBFrun hFpre
  have hFT : ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ stop →
      Block.Preceq (rho.stateBefore S n v).st.core.F F.erase := by
    intro v hv n hn
    obtain ⟨C, hCmem, hCF, hCFbelow⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho n v
    have hCrun : RunBlock S rho C :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hCmem
    have hmax : (rho.stateBefore S n v).st.core.h_max ≤ blocked + 1 :=
      (localHMax_le_honestHMaxBeforeIndex S rho n hv).trans
        ((honestHMaxBeforeIndex_mono S rho hn).trans
          (Nat.le_of_lt_succ hfrontier))
    have hCle : (derive_named S.E S.cfg C).h_F ≤ blocked :=
      Nat.le_of_lt_succ (hCFbelow.trans_le hmax)
    by_cases hCzero : (derive_named S.E S.cfg C).h_F = 0
    · have hgen : (rho.stateBefore S n v).st.core.F = Block.genesis := by
        rw [← hCF]
        exact NamedFinalityCertificates.finalized_zero_is_genesis
          S.E S.cfg C hCzero
      rw [hgen]
      exact Protocol.preceq_genesis F.erase
    · obtain ⟨FC, hFC, hFCerase, hFCheight, hFCself⟩ :=
        namedFinalization_selfTarget_deadline S.E S.cfg C
          (Nat.pos_of_ne_zero hCzero)
      have hFCrun : RunBlock S rho FC :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hFC
      have hcompat := NamedFinalityAgreement.finalized_compatible
        S rho C BF hsb adm.toNamedRootCollisionFree hCrun hBFrun
      have hfinalCompat : Block.compatible FC.erase F.erase = true := by
        simpa only [hFCerase, hFerase] using hcompat
      rcases Nat.lt_or_eq_of_le hCle with hClt | hCeq
      · have hpre := NamedFinalizationBridge.finalized_preceq_of_height_lt
          S rho F C hsb adm.toNamedRootCollisionFree hFrun hCrun
          (by rw [hFheight]; exact hClt)
        simpa only [hCF, hFCerase] using hpre
      · have hFCeqF := namedEntries_eq_of_compatible_deadline S adm
          hFCrun hFrun hFCself hFself
          (hFCheight.trans (hCeq.trans hFheight.symm)) hfinalCompat
        rw [← hCF, ← hFCerase, hFCeqF]
        exact Block.preceq_self F.erase
  have hprevBelow : ∀ X : NamedBlock V, RunBlock S rho X →
      (derive_named S.E S.cfg X).h = blocked + 1 →
      NamedBlock.Preceq F X := by
    intro X hXrun hXheight
    have hraw := NamedFinalizationBridge.finalized_preceq_of_height_lt
      S rho X BF hsb adm.toNamedRootCollisionFree hXrun hBFrun
      (by rw [hBFheight, hXheight]; exact Nat.lt_succ_self blocked)
    exact Protocol.namedPreceq_of_runBlock_erase_preceq adm hFrun hXrun
      (by simpa only [hFerase] using hraw)
  refine ⟨?_, hFrun, hFheight.le, ?_, ?_⟩
  · intro v hv n hn X hXrun hXheight hFX
    exact Block.preceq_trans (hFT v hv n hn)
      (Proofs.NamedWire.erase_preceq hFX)
  · intro v hv n hn Q hQmem hQheight hFQ
    have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1
    have hQraw : Q.erase ∈ (rho.stateBefore S n v).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hQmem
    have hview := Proofs.NamedStoreBridge.derivedView_stateBefore S rho n v Q hQmem
    have hQstored : ((rho.stateBefore S n v).st.core.σ Q.erase).h =
        blocked + 1 := by rw [hview, hQheight]
    have hmax : (rho.stateBefore S n v).st.core.h_max = blocked + 1 :=
      localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
        S adm hfrontier hv hn hQraw hQstored
    by_cases hgate : (rho.stateBefore S n v).st.core.h_max =
        (rho.stateBefore S n v).st.core.h_j + 1
    · obtain ⟨C, hCmem, hCJ, hChj⟩ :=
        Proofs.Bridges.storeJustificationOnChain_stateBefore S rho n v
      have hCrun : RunBlock S rho C :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hv hCmem
      have hjeq : (derive_named S.E S.cfg C).h_j = blocked := by
        rw [hChj]
        exact (Nat.add_right_cancel (hmax.symm.trans hgate)).symm
      have hJF := namedJustified_eq_finalized_deadline S adm hsb
        hCrun hBFrun hFrun hFpre hFerase
        (hFheight.trans hBFheight.symm) hFself
        (hjeq.trans hBFheight.symm)
      simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
        if_pos hgate]
      rw [← hCJ, hJF]
      exact Proofs.NamedWire.erase_preceq hFQ
    · simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
        if_neg hgate]
      exact Block.preceq_trans (hFT v hv n hn)
        (Proofs.NamedWire.erase_preceq hFQ)
  · intro p hp r _hr _hhor B hBmem hsource hBheight
    have hBrun : RunBlock S rho B := by
      have hBpre : B ∈ (rho.stateBeforeTime S (S.a r) p).st.bodies := by
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
          NamedRun.stateBeforeTime] using hBmem
      obtain ⟨i, hi, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
        adm.toNamedScheduleWellFormed.sorted (S.a r)
      have hBi : B ∈ (rho.stateBefore S i p).st.bodies := by
        change B ∈ (NamedRun.stateBefore S rho i p).st.bodies
        rw [← hi]
        exact hBpre
      exact Proofs.Bridges.runBlock_of_stateBefore_mem S hp hBi
    have hraw := NamedFinalizationBridge.finalized_preceq_of_height_lt
      S rho B BF hsb adm.toNamedRootCollisionFree hBrun hBFrun
      (by rw [hBFheight, hBheight]; exact Nat.lt_succ_self blocked)
    exact Protocol.namedPreceq_of_runBlock_erase_preceq adm hFrun hBrun
      (by simpa only [hFerase] using hraw)

/-- The run-scoped finalized-height base. -/
private theorem namedHeightRegimeBaseRun_of_finalized
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r0 : Round} {first : Nat} {blocked : Height}
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hstart : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) < blocked)
    {BF F : NamedBlock V} (hBFrun : RunBlock S rho BF)
    (hFpre : NamedBlock.Preceq F BF)
    (hFerase : F.erase = (derive_named S.E S.cfg BF).F)
    (hFheight : (derive_named S.E S.cfg F).h = blocked)
    (hBFheight : (derive_named S.E S.cfg BF).h_F = blocked)
    (hFself : (derive_named S.E S.cfg F).T_h = F.erase) :
    NamedHeightRegimeBaseRun S rho r0 blocked first F := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hFrun : RunBlock S rho F :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBFrun hFpre
  obtain ⟨v, hv⟩ : rho.honest.Nonempty := by
    by_contra hempty
    have hm := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
    simpa [HonestWeightMajority, Finset.not_nonempty_iff_eq_empty.mp hempty,
      Electorate.weightOf] using hm
  let start := inclusiveEventIndex rho (S.a r0)
  have hone : 1 ≤ (rho.stateBefore S start v).st.core.h_max :=
    Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt
      (NamedJustificationBound.justificationBelowMax_stateBefore
        S rho start v))
  have htwo : 2 ≤ blocked := Nat.succ_le_of_lt
    ((hone.trans (localHMax_le_honestHMaxBeforeIndex S rho start hv)).trans_lt
      hstart)
  have hframe : ∀ c : Round,
      NamedHeightRegimeFrame S rho blocked (first - 1) F c := by
    intro c
    exact namedHeightRegimeFrame_of_finalizedRun S adm hbelow
      (Nat.lt_succ_of_le
        (hfirst.before _ (Nat.sub_lt hfirst.positive Nat.one_pos)))
      hBFrun hFpre hFerase hFheight hBFheight hFself
  refine ⟨hfirst, hstart, (by exact (by decide : 1 ≤ 2).trans htwo), ?_, ?_⟩
  · intro c _hminimal
    exact hframe c
  · intro a ta ha hemit hbefore R hRrun hRh hpair hR w hw time
      hfrontier hroot X hXrun hXheight hFX
    obtain ⟨m, hm, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted time
    have hstore : rho.storeBeforeTime S w time =
        (rho.stateBefore S m w).st := by
      unfold Run.storeBeforeTime NamedRun.stateBeforeTime
      exact congrArg NodeState.st (congrFun hm w)
    rw [hstore] at hroot
    by_cases hgate : (rho.stateBefore S m w).st.core.h_max =
        (rho.stateBefore S m w).st.core.h_j + 1
    · obtain ⟨C, hCmem, hCJ, hChj⟩ :=
        Proofs.Bridges.storeJustificationOnChain_stateBefore S rho m w
      have hCrun : RunBlock S rho C :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hw hCmem
      have hRJ : R.erase = (derive_named S.E S.cfg C).J := by
        simpa only [Protocol.get_fg_root, Protocol.Store.toHealing,
          if_pos hgate, hCJ] using hroot.symm
      have hJpos : 0 < (derive_named S.E S.cfg C).h_j := by
        by_contra hz
        have hz' : (derive_named S.E S.cfg C).h_j = 0 := Nat.eq_zero_of_not_pos hz
        have hJgen := NamedJustificationCertificates.justified_zero_is_genesis
          S.E S.cfg C hz'
        have hRgenErase : R.erase = Block.genesis := hRJ.trans hJgen
        have hgenRun : RunBlock S rho (NamedBlock.genesis : NamedBlock V) :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBFrun
            (named_genesis_preceq_deadline BF)
        have hRgen : R = NamedBlock.genesis :=
          adm.toNamedRootCollisionFree.root_injective R .genesis
            hRrun hgenRun R .genesis
            (Or.inl (named_preceq_self_deadline R))
            (Or.inr (named_preceq_self_deadline .genesis))
            (by
              calc
                R.root = R.erase.root := (Proofs.NamedWire.erase_root R).symm
                _ = Block.genesis.root := congrArg Block.root hRgenErase
                _ = (NamedBlock.genesis : NamedBlock V).erase.root := rfl
                _ = (NamedBlock.genesis : NamedBlock V).root :=
                  Proofs.NamedWire.erase_root _)
        subst R
        have honeEq : 1 = blocked := by
          simpa [derive_named, ChainState.initial] using hRh
        rw [← honeEq] at htwo
        norm_num at htwo
      obtain ⟨J, hJC, hJerase, hJheight, hJself⟩ :=
        NamedCheckpointAlgebra.namedJustification_selfTarget
          S.E S.cfg C hJpos
      have hJrun : RunBlock S rho J :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hJC
      have hRJnamed : R = J :=
        adm.toNamedRootCollisionFree.root_injective R J hRrun hJrun R J
          (Or.inl (named_preceq_self_deadline R))
          (Or.inr (named_preceq_self_deadline J))
          (by rw [← Proofs.NamedWire.erase_root R, ← Proofs.NamedWire.erase_root J,
            hRJ, hJerase])
      have hjeq : (derive_named S.E S.cfg C).h_j = blocked := by
        rw [← hJheight, ← hRJnamed]
        exact hRh
      have hJF := namedJustified_eq_finalized_deadline S adm hsb
        hCrun hBFrun hFrun hFpre hFerase
        (hFheight.trans hBFheight.symm) hFself
        (hjeq.trans hBFheight.symm)
      have hRFerase : R.erase = F.erase := hRJ.trans hJF
      have hRF : R = F :=
        adm.toNamedRootCollisionFree.root_injective R F hRrun hFrun R F
          (Or.inl (named_preceq_self_deadline R))
          (Or.inr (named_preceq_self_deadline F))
          (by rw [← Proofs.NamedWire.erase_root R, ← Proofs.NamedWire.erase_root F,
            hRFerase])
      rw [hRF]
      exact hFX
    · obtain ⟨C, hCmem, hCF, hCFbelow⟩ :=
        Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho m w
      have hCrun : RunBlock S rho C :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hw hCmem
      have hRFraw : R.erase = (derive_named S.E S.cfg C).F := by
        simpa only [Protocol.get_fg_root, Protocol.Store.toHealing,
          if_neg hgate, hCF] using hroot.symm
      have hCpos : 0 < (derive_named S.E S.cfg C).h_F := by
        by_contra hz
        have hz' : (derive_named S.E S.cfg C).h_F = 0 := Nat.eq_zero_of_not_pos hz
        have hFgen := NamedFinalityCertificates.finalized_zero_is_genesis
          S.E S.cfg C hz'
        have hRgenErase : R.erase = Block.genesis := hRFraw.trans hFgen
        have hgenRun : RunBlock S rho (NamedBlock.genesis : NamedBlock V) :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBFrun
            (named_genesis_preceq_deadline BF)
        have hRgen : R = NamedBlock.genesis :=
          adm.toNamedRootCollisionFree.root_injective R .genesis
            hRrun hgenRun R .genesis
            (Or.inl (named_preceq_self_deadline R))
            (Or.inr (named_preceq_self_deadline .genesis))
            (by
              calc
                R.root = R.erase.root := (Proofs.NamedWire.erase_root R).symm
                _ = Block.genesis.root := congrArg Block.root hRgenErase
                _ = (NamedBlock.genesis : NamedBlock V).erase.root := rfl
                _ = (NamedBlock.genesis : NamedBlock V).root :=
                  Proofs.NamedWire.erase_root _)
        subst R
        have honeEq : 1 = blocked := by
          simpa [derive_named, ChainState.initial] using hRh
        rw [← honeEq] at htwo
        norm_num at htwo
      obtain ⟨FC, hFC, hFCerase, hFCheight, hFCself⟩ :=
        namedFinalization_selfTarget_deadline S.E S.cfg C hCpos
      have hFCrun : RunBlock S rho FC :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hFC
      have hRFC : R = FC :=
        adm.toNamedRootCollisionFree.root_injective R FC hRrun hFCrun R FC
          (Or.inl (named_preceq_self_deadline R))
          (Or.inr (named_preceq_self_deadline FC))
          (by rw [← Proofs.NamedWire.erase_root R, ← Proofs.NamedWire.erase_root FC,
            hRFraw, hFCerase])
      have hFCblocked : (derive_named S.E S.cfg FC).h = blocked := by
        rw [← hRFC]
        exact hRh
      have hcompat := NamedFinalityAgreement.finalized_compatible
        S rho C BF hsb adm.toNamedRootCollisionFree hCrun hBFrun
      have hentryEq := namedEntries_eq_of_compatible_deadline S adm
        hFCrun hFrun hFCself hFself
        (hFCblocked.trans hFheight.symm)
        (by simpa only [hFCerase, hFerase] using hcompat)
      rw [hRFC, hentryEq]
      exact hFX

#print axioms namedHeightRegimeBaseRun_of_finalized

/-- The honest-store named finality maximum is attained. -/
private theorem exists_named_finalizedAt_recoveryPrefixFinalityHeight
    (S : Setup V) {rho : Run V} (n : Nat)
    (hne : rho.honest.Nonempty) :
    ∃ v ∈ rho.honest, ∃ B ∈ (rho.stateBefore S n v).st.bodies,
      (derive_named S.E S.cfg B).h_F =
        recoveryPrefixFinalityHeight S rho n := by
  classical
  obtain ⟨v, hv, hsup⟩ := Finset.exists_mem_eq_sup rho.honest hne
    (fun w => (rho.stateBefore S n w).st.bodies.sup
      (fun B => (derive_named S.E S.cfg B).h_F))
  have hgen : (NamedBlock.genesis : NamedBlock V) ∈
      (rho.stateBefore S n v).st.bodies :=
    ((Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1.2.2.1).1
  obtain ⟨B, hB, hBsup⟩ := Finset.exists_mem_eq_sup
    (rho.stateBefore S n v).st.bodies ⟨_, hgen⟩
    (fun B => (derive_named S.E S.cfg B).h_F)
  refine ⟨v, hv, B, hB, ?_⟩
  unfold recoveryPrefixFinalityHeight
  rw [hsup, hBsup]

private theorem honestHMaxAt_add_le_of_eventualHeightProgress_namedDeadline
    (S : Setup V) {rho : Run V} {r0 lag : Round}
    (h : EventualHeightProgressFrom S rho r0 lag) (k : Nat)
    (hhor : S.a (r0 + k * lag) ≤ rho.horizon) :
    honestHMaxAt S rho (S.a r0) + k ≤
      honestHMaxAt S rho (S.a (r0 + k * lag)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have e : r0 + (k + 1) * lag = r0 + k * lag + lag := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      have hle : r0 + k * lag ≤ r0 + (k + 1) * lag := by
        rw [e]
        exact Nat.le_add_right _ _
      have hhor' : S.a (r0 + k * lag) ≤ rho.horizon :=
        (Assembly.a_mono S hle).trans hhor
      rw [e] at hhor ⊢
      have hstep := h.2 (r0 + k * lag) (Nat.le_add_right r0 _) hhor
      have hk := ih hhor'
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hk hstep)

private theorem honestHMaxBeforeIndex_ge_of_eventualHeightProgress_namedDeadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r0 lag : Round} (h : EventualHeightProgressFrom S rho r0 lag)
    (k : Nat) (hhor : S.a (r0 + k * lag) ≤ rho.horizon) :
    honestHMaxBeforeIndex S rho (inclusiveEventIndex rho (S.a r0)) + k ≤
      honestHMaxBeforeIndex S rho
        (inclusiveEventIndex rho (S.a (r0 + k * lag))) := by
  have hk := honestHMaxAt_add_le_of_eventualHeightProgress_namedDeadline
    S h k hhor
  rwa [honestHMaxAt_eq_honestHMaxBeforeIndex
      S adm.toNamedScheduleWellFormed,
    honestHMaxAt_eq_honestHMaxBeforeIndex
      S adm.toNamedScheduleWellFormed] at hk

/-- Named run-scoped height progress supplies a base by the stated deadline. -/
private theorem exists_namedHeightRegimeBaseRun_of_eventualHeightProgress
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r0 lag : Round} (hprog : EventualHeightProgressFrom S rho r0 lag)
    {H : Height} (hK : S.cfg.K ∣ H)
    (hH : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) + S.cfg.D + 3 ≤ H)
    {k : Nat}
    (hk : H + 3 ≤ honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) + k)
    (hhor : S.a (r0 + k * lag) ≤ rho.horizon) :
    ∃ (blocked : Height) (first : Nat) (Tprev : NamedBlock V),
      blocked ≤ H + 1 ∧
      first ≤ inclusiveEventIndex rho (S.a (r0 + k * lag)) ∧
      NamedHeightRegimeBaseRun S rho r0 blocked first Tprev := by
  have hreach : H + 3 ≤ honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a (r0 + k * lag))) :=
    hk.trans (honestHMaxBeforeIndex_ge_of_eventualHeightProgress_namedDeadline
      S adm hprog k hhor)
  obtain ⟨first, hstop, hfirst⟩ := exists_firstHeightProgressAt
    S adm.toNamedAdmissibleCore.toNamedDeliveryWellFormed
    (H := H + 1) (Nat.succ_le_succ (Nat.zero_le H))
    ((Nat.add_le_add_left (by decide : 2 ≤ 3) H).trans hreach)
  have hstartH : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) < H :=
    lt_of_lt_of_le (lt_of_lt_of_le
      (Nat.lt_add_of_pos_right (Nat.succ_pos 2))
      (Nat.add_le_add_right (Nat.le_add_right _ S.cfg.D) 3)) hH
  by_cases hrec : NjGap.RecoveryHeight S.cfg
      (recoveryPrefixFinalityHeight S rho first) H
  · have hbase := namedHeightRegimeBase_of_recovery S adm hbelow hfirst
      (honestPrefixFinalityCap_recoveryPrefixFinalityHeight S rho first)
      hrec hstartH
    exact ⟨H, first, .genesis, Nat.le_succ H, hstop,
      NamedHeightRegimeBaseRun.ofNamed hbase⟩
  · have hwithin : H ≤ recoveryPrefixFinalityHeight S rho first + S.cfg.D := by
      have hnot : ¬ S.cfg.D < H - recoveryPrefixFinalityHeight S rho first := by
        intro hgap
        exact hrec ⟨hK, hgap⟩
      have hsub := Nat.sub_le_iff_le_add.mp (Nat.le_of_not_lt hnot)
      rw [Nat.add_comm]
      exact hsub
    obtain ⟨v, hv, B, hB, hBF⟩ :=
      exists_named_finalizedAt_recoveryPrefixFinalityHeight S first
        (honest_nonempty_of_honestCommittees hcom)
    have hBrun : RunBlock S rho B :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hB
    have hheight := Proofs.NamedStoreBridge.heights_le_hMax_stateBefore
      S rho first v B hB
    have hlocal := localHMax_le_honestHMaxBeforeIndex S rho first hv
    rw [hfirst.frontier] at hlocal
    have hstrict :=
      (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg B).finalized_below_height
    have hupper : (derive_named S.E S.cfg B).h_F ≤ H + 1 :=
      Nat.le_of_lt_succ (hstrict.trans_le (hheight.trans hlocal))
    have hstart : honestHMaxBeforeIndex S rho
        (inclusiveEventIndex rho (S.a r0)) <
        (derive_named S.E S.cfg B).h_F :=
      Nat.lt_of_add_lt_add_right
        ((Nat.lt_add_of_pos_right (by decide : 0 < 3)).trans_le
          (hH.trans (by rw [hBF]; exact hwithin)))
    obtain ⟨next, hnext, hcross⟩ := exists_firstHeightProgressAt
      S adm.toNamedAdmissibleCore.toNamedDeliveryWellFormed
      (H := (derive_named S.E S.cfg B).h_F + 1)
      (Nat.succ_le_succ (Nat.zero_le _))
      (((Nat.add_le_add_right hupper 1).trans_lt
        (Nat.lt_succ_self (H + 2))).trans_le hreach)
    have hpos : 0 < (derive_named S.E S.cfg B).h_F :=
      (Nat.zero_le _).trans_lt hstart
    obtain ⟨F, hFB, hFerase, hFheight, hFself⟩ :=
      namedFinalization_selfTarget_deadline S.E S.cfg B hpos
    exact ⟨_, next, F, hupper, hnext,
      namedHeightRegimeBaseRun_of_finalized S adm hbelow hcross hstart
        hBrun hFB hFerase hFheight rfl hFself⟩


/-- The public  deadline producer over the run-scoped base.

The target is the first `K` multiple strictly above `M + D + 2`, where `M`
is the honest frontier at `rGST + 2`. It is between `M + D + 3` and
`M + D + K + 2`, so `D + K + 5` relative height gains reach three heights
past it. -/
theorem exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hhor : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
      rho.horizon) :
    ∃ (blocked : Height) (first : Nat) (Tprev : NamedBlock V),
      first ≤ inclusiveEventIndex rho
        (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ∧
      NamedHeightRegimeBaseRun S rho (rGST + 2) blocked first Tprev := by
  let r0 := rGST + 2
  let L := progressLag' gap delayExtra
  let M := honestHMaxBeforeIndex S rho
    (inclusiveEventIndex rho (S.a r0))
  let k := S.cfg.D + S.cfg.K + 5
  have hpost' : S.E.t_GST ≤ S.a r0 :=
    hpost.trans ((action_strictMono S).monotone (by
      simpa only [r0] using Nat.le_add_right rGST 2))
  have hprog : EventualHeightProgressFrom S rho r0 L :=
    eventualHeightProgressFrom_of_seed S adm hcom hbelow hrec
      (heightProgressSeedFrom_of_canonicity S adm hcom hbelow hdelay hrec hpost'
        (seedPredPromotionInputs_of_public S adm hcom hbelow hdelay hrec))
      hdelay hpost'
      (fixedRootProgress_of_rows S adm hcom hbelow hrec hdelay
        (fixedRoot_sourceHeight_le_nextOpeningParent S adm hcom hbelow))
  obtain ⟨H, hH, hHupper, hrecovery⟩ :=
    exists_recoveryHeight_between S.cfg M (M + 2) (Nat.le_add_right M 2)
  have hK : S.cfg.K ∣ H := hrecovery.1
  have hH' : M + S.cfg.D + 3 ≤ H := by
    calc
      M + S.cfg.D + 3 = M + 2 + S.cfg.D + 1 := by ring
      _ ≤ H := hH
  have hk : H + 3 ≤ M + k := by
    calc
      H + 3 ≤ (M + 2 + S.cfg.D + S.cfg.K) + 3 :=
        Nat.add_le_add_right hHupper 3
      _ = M + k := by dsimp only [k]; ring
  have hdeadline : r0 + k * L =
      fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    dsimp only [r0, k, L, fgSafetyProgressDeadline]
    ring
  obtain ⟨blocked, first, Tprev, -, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_of_eventualHeightProgress
      S adm hcom hbelow hprog hK (by simpa only [M] using hH') hk
        (by simpa only [hdeadline] using hhor)
  exact ⟨blocked, first, Tprev, by simpa only [hdeadline] using hfirst, hbase⟩

#print axioms exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
