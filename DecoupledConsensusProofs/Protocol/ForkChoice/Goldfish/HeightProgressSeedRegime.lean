module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightProgress

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Local named-run helpers

Mechanical copies of the small connective lemmas `FixedHeightRootCoreRun.lean`
keeps `private` (so unavailable to this file): a named body retained at an
honest strict read is a run block, and two run-block witnesses erasing to the
same public block are the same named body. -/

private theorem runBlockOf_of_stateBeforeTime_mem
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time)
    {D : NamedBlock V} (hD : D ∈ (rho.storeBeforeTime S w read).bodies) :
    RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed read
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
  simpa only [Run.storeBeforeTime, hn] using hD

private theorem runBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])


/-- A processed run block at least one height below an exact honest frontier
is active at a gate-off honest read.

design note: the run witness is a named body `Xn` with `Xn.erase = X` (`RunBlock`
lives only over `NamedBlock V`); the height premise reads `derive_named Xn`
in place of the retired `derived_state X` (statement change, ledger row). -/
theorem frontierBlock_filtered_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time} (hread : read ≤ rho.horizon)
    {X : Block V} {Xn : NamedBlock V} {M : Height}
    (hX : X ∈ (rho.storeBeforeTime S w read).T)
    (hXerase : Xn.erase = X) (hXrun : RunBlock S rho Xn)
    (hXh : M - 1 ≤ (Protocol.derive_named S.E S.cfg Xn).h) (hM : 1 ≤ M)
    (hfrontier : (rho.storeBeforeTime S w read).h_max = M)
    (hgateOff : (rho.storeBeforeTime S w read).h_j + 2 ≤ M) :
    X ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG := by
  let st := rho.storeBeforeTime S w read
  have hnoHigh : Internal.NamedNoHighJustifications S.E S.cfg st :=
    NamedJustificationBound.noHighJustifications_stateBeforeTime S rho read w
  obtain ⟨Dst, hDstMem, hDstF, -⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho read w
  have hDrun : RunBlock S rho Dst :=
    runBlockOf_of_stateBeforeTime_mem S adm hw read hDstMem
  have hhjlt : st.h_j < M - 1 := by
    rw [Nat.lt_sub_iff_add_lt]
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
  have hcrossed : (Protocol.derive_named S.E S.cfg Dst).h_F <
      (Protocol.derive_named S.E S.cfg Xn).h := by
    calc
      (Protocol.derive_named S.E S.cfg Dst).h_F ≤
          (Protocol.derive_named S.E S.cfg Dst).h_j :=
        (NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg Dst).heights_ordered
      _ ≤ st.h_j := hnoHigh Dst hDstMem
      _ < M - 1 := hhjlt
      _ ≤ (Protocol.derive_named S.E S.cfg Xn).h := hXh
  have hFX : Block.Preceq st.F X := by
    have hpre := NamedFinalizationBridge.finalized_preceq_of_height_lt
      S rho Xn Dst hsb adm.toNamedRootCollisionFree hXrun hDrun hcrossed
    rw [hXerase] at hpre
    simpa only [hDstF] using hpre
  have hgate : ¬ st.h_max = st.h_j + 1 := by
    apply Nat.ne_of_gt
    rw [hfrontier]
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
  have hroot : Protocol.get_fg_root st.toHealing.toFG = st.F := by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
  have hV : X ∈ Protocol.V_tree st.toHealing.toFG := by
    obtain ⟨D', hD'mem, hD'erase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho read w hX
    have hD'run : RunBlock S rho D' :=
      runBlockOf_of_stateBeforeTime_mem S adm hw read hD'mem
    have hDeq : D' = Xn :=
      runBlock_unique_of_erase_eq adm hD'run hXrun (hD'erase.trans hXerase.symm)
    have hview : (Run.stateBeforeTime S rho read w).st.core.σ D'.erase =
        Protocol.derive_named S.E S.cfg D' :=
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho read w D' hD'mem
    rw [hD'erase, hDeq] at hview
    have hSigmaX : st.core.σ X = Protocol.derive_named S.E S.cfg Xn := hview
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hX, hFX⟩, X, hX, Block.preceq_self _, ?_⟩
    rw [hSigmaX]
    rw [show st.core.h_max = M from hfrontier]
    exact hXh
  have hrootX : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) X := by
    rw [hroot]
    exact hFX
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootX


/-- A low cone prefix remains active when a processed descendant reaches the
frontier window. Unlike `frontierBlock_filtered_of_gateOff`, the protected
block `C` need not itself have height at least `M - 1`. The separate root
ordering is necessary: a processed ancestor strictly below the selected FG
root is not a member of the filtered tree.

design note: `D`'s run-block witness is a named body `Dn` (statement change,
ledger row); `C` stays a bare `Block V` — `ParentClosed` and `Preceq` descent
never needed a run witness for it. -/
theorem frontierAncestor_filtered_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time} (hread : read ≤ rho.horizon)
    {C D : Block V} {Dn : NamedBlock V} {M : Height}
    (hD : D ∈ (rho.storeBeforeTime S w read).T)
    (hDerase : Dn.erase = D) (hDrun : RunBlock S rho Dn)
    (hCD : Block.Preceq C D)
    (hDh : M - 1 ≤ (Protocol.derive_named S.E S.cfg Dn).h) (hM : 1 ≤ M)
    (hfrontier : (rho.storeBeforeTime S w read).h_max = M)
    (hgateOff : (rho.storeBeforeTime S w read).h_j + 2 ≤ M)
    (hrootC : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) C) :
    C ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG := by
  let st := rho.storeBeforeTime S w read
  have hpc : ParentClosed st.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho read w
  have hCT : C ∈ st.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff st.core).mp hpc).2 C D hD hCD
  have hFJ : Block.Preceq st.F st.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho read w
  have hDfiltered : D ∈ Protocol.get_filtered_block_tree
      st.toHealing.toFG :=
    frontierBlock_filtered_of_gateOff S adm hsb hw hread hD hDerase hDrun
      hDh hM hfrontier hgateOff
  exact Proofs.Records.mem_filtered_of_preceq
    (by simpa only [Protocol.Store.toHealing] using hFJ)
    hDfiltered hCT hCD hrootC

/-! ## Root-side read activity

A low protected prefix need not be a member of the finality-filtered tree: the
local FG root can be strictly above it. The weak read interface records the
two sound orientations separately. Its left arm is actual filtered-tree
activity; its right arm is the root-side case consumed by the primed Goldfish
cone inputs.
-/















/-- The gate-off frontier activity fact at an exact action read.

design note: `actionStoreAt` replaces the prior (now private-elsewhere)
`healStoreAt` facade; every field it reads here (`.T`, `.h_max`, `.h_j`,
`.toHealing.toFG`) is definitionally the `storeBeforeTime S rho w (S.a r)`
field (`GradeBootstrapCoreRun.actionStoreAt_fgRoot_eq_storeBeforeTime` is
itself `rfl`), so the wrapper needs no bridging rewrite. The run witness is a
named body (statement change, ledger row). -/
theorem frontierBlock_filtered_at_healStoreAt_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {w : V} (hw : w ∈ rho.honest) {r : Round} (hread : S.a r ≤ rho.horizon)
    {X : Block V} {Xn : NamedBlock V} {M : Height}
    (hX : X ∈ (actionStoreAt S rho w r).T)
    (hXerase : Xn.erase = X) (hXrun : RunBlock S rho Xn)
    (hXh : M - 1 ≤ (Protocol.derive_named S.E S.cfg Xn).h) (hM : 1 ≤ M)
    (hfrontier : (actionStoreAt S rho w r).h_max = M)
    (hgateOff : (actionStoreAt S rho w r).h_j + 2 ≤ M) :
    X ∈ Protocol.get_filtered_block_tree (actionStoreAt S rho w r).toHealing.toFG :=
  frontierBlock_filtered_of_gateOff S adm hsb hw hread hX hXerase hXrun hXh hM
    hfrontier hgateOff

/-! The complete earlier goals for the available frontier-regime pair remain
below. `hexact` is used in both branches of both theorems. -/



/-! ## Named justification carriers and certificates -/

/-- The named justification carrier at an honest strict read. -/
private theorem justificationCarrierAtStrictRead_l1
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time) :
    let st := rho.storeBeforeTime S w read
    ∃ C : NamedBlock V,
      C ∈ st.bodies ∧ RunBlock S rho C ∧
        Internal.NamedJustifiedAt S.E S.cfg C st.J st.h_j := by
  let st := rho.storeBeforeTime S w read
  obtain ⟨C, hC, hJ, hhj⟩ :=
    Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho read w
  have hCrun : RunBlock S rho C :=
    runBlockOf_of_stateBeforeTime_mem S adm hw read hC
  exact ⟨C, hC, hCrun, ⟨hJ, hhj⟩⟩

omit [Fintype V] in
private theorem mem_named_chain_attestations_own_l1
    {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)

/-- A named justified run block yields the erased certificate interface. -/
private theorem certificate_of_justifiedRunBlock_l1
    (S : Setup V) {rho : Run V}
    {C : NamedBlock V} {J : Block V} {h : Height}
    (hCrun : RunBlock S rho C)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg C J h)
    (hne : h ≠ 0) : Certificate S rho h J.root := by
  have hderivedNe : (Protocol.derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hjust.2]
    exact hne
  obtain ⟨J', hJ'D, hJ'earse, Q, hQ, hsign⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg C hderivedNe
  have hJroot : J'.root = J.root := by
    rw [← Proofs.NamedWire.erase_root J', hJ'earse, hjust.1]
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  obtain ⟨carrier, a, hcarrier, ha, hav, hpair⟩ := hsign i hi
  have hcarrierRun : RunBlock S rho carrier :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hcarrier
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun, mem_named_chain_attestations_own_l1 ha⟩,
    hav, ?_⟩
  rw [hpair, hjust.2, hJroot]

/-- The stored justification block has a named run witness. -/
private theorem runBlockOf_justified_atStrictRead_l1
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time) :
    RunBlockOf S rho (rho.storeBeforeTime S w read).J := by
  have hJmem : (rho.storeBeforeTime S w read).J ∈
      (rho.storeBeforeTime S w read).T := by
    exact Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho read w
  obtain ⟨D, hD, hDe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho read w hJmem
  exact ⟨D, hDe, runBlockOf_of_stateBeforeTime_mem S adm hw read hD⟩

/-- One full relay after an exact honest frontier either exposes the unique
fixed-height justification root, or leaves every honest strict store gate off. -/
theorem frontierRegime_after_oneDelay
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) (hsb : SlashableBound S rho)
    {start : Round} {M : Height}
    (hM : honestHMaxAt S rho (S.a start) = M)
    (hpost : S.E.t_GST ≤ S.a start)
    (hcap : honestHMaxAt S rho (S.a (start + 1)) ≤ M)
    (hhor : S.a (start + 1) ≤ rho.horizon) (h2 : 2 ≤ M) :
    (∃ u ∈ rho.honest,
      FixedHeightJustificationRootAtRead S rho M u (S.a (start + 1))) ∨
    (∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a (start + 1))).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (S.a (start + 1))).h_max = M) := by
  let n := inclusiveEventIndex rho (S.a start)
  have hprefix : honestHMaxBeforeIndex S rho n = M := by
    rw [← honestHMaxAt_eq_honestHMaxBeforeIndex
      S adm.toNamedScheduleWellFormed (S.a start)]
    exact hM
  have hpred : M - 1 + 1 = M :=
    Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans h2)
  have hprefixSucc : honestHMaxBeforeIndex S rho n = M - 1 + 1 := by
    rw [hprefix, hpred]
  obtain ⟨holder, hholder, carrier, hcarrierMem, hcarrierRun, hcarrierHeight⟩ :=
    exists_honest_exactHMaxCarrierAtPrefix S adm n (M - 1) hprefixSucc
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.stateBefore S n holder).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n holder).1.1.1
  have hcarrierT : carrier.erase ∈ (rho.stateBefore S n holder).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hcarrierMem
  have hcarrier : HonestHMaxCarrierAt S rho (S.a start) M holder carrier.erase :=
    { holderHonest := hholder
      processed := by
        rw [storeAt_eq_stateBefore_inclusiveEventIndex
          S adm.toNamedScheduleWellFormed holder (S.a start)]
        exact hcarrierT
      namedWitness := ⟨carrier, rfl, hcarrierRun,
        by simpa only [hpred] using hcarrierHeight⟩ }
  have hrelayStep : S.a start + 1 + S.E.Δ ≤ S.a (start + 1) := by
    rw [Proofs.HealingLemmas.a_add_rounds S start 1]
    have hDelta : (1 : Time) ≤ S.E.Δ :=
      Int.add_one_le_iff.mpr S.E.Δ_pos
    have hDnonneg : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
    have hR : (2 : Time) ≤ (S.hc.R : Nat) := by
      exact_mod_cast S.hc.R_ge_two
    have hcoef : (0 : Time) ≤ 4 * S.E.Δ :=
      Int.mul_nonneg (by norm_num) hDnonneg
    have hscale : 4 * S.E.Δ * 2 ≤ 4 * S.E.Δ * (S.hc.R : Nat) :=
      Int.mul_le_mul_of_nonneg_left hR hcoef
    have hsmall : (1 : Time) + S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := by
      calc
        (1 : Time) + S.E.Δ ≤ 2 * S.E.Δ := by
          simpa [two_mul] using Int.add_le_add_right hDelta S.E.Δ
        _ ≤ 4 * S.E.Δ * 2 := by
          have htwo := Int.mul_le_mul_of_nonneg_right
            (show (2 : Time) ≤ 8 by decide) hDnonneg
          simpa only [show (8 : Time) * S.E.Δ = 4 * S.E.Δ * 2 by ring] using htwo
        _ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := hscale
    simpa only [Nat.cast_one, mul_one, Int.add_assoc] using
      Int.add_le_add_left hsmall (S.a start)
  have hexact : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a (start + 1))).h_max = M := by
    intro w hw
    exact (hcarrier.visibleWithExactFrontier_after_oneDelay_of_noRise
      S adm hsb hpost hrelayStep hhor hcap w hw).2
  by_cases hgate : ∃ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (start + 1))).h_j = M - 1
  · rcases hgate with ⟨u, hu, hju⟩
    left
    refine ⟨u, hu, ?_⟩
    obtain ⟨C, hC, hCrun, hjust⟩ :=
      justificationCarrierAtStrictRead_l1 S adm hu (S.a (start + 1))
    have hjust' : Internal.NamedJustifiedAt S.E S.cfg C
        (rho.storeBeforeTime S u (S.a (start + 1))).J (M - 1) := by
      simpa only [hju] using hjust
    have hMsubPos : 0 < M - 1 :=
      Nat.sub_pos_iff_lt.mpr ((by decide : 1 < 2).trans_le h2)
    have hcert : Certificate S rho (M - 1)
        (rho.storeBeforeTime S u (S.a (start + 1))).J.root :=
      certificate_of_justifiedRunBlock_l1 S hCrun hjust'
        (Nat.ne_of_gt hMsubPos)
    refine
      { readerHonest := hu
        readInHorizon := hhor
        carrierExists := ⟨C, hC, hCrun, hjust⟩
        targetHeightPositive := hMsubPos
        fixedTarget :=
          { frontier := hexact u hu
            justificationHeight := hju
            gate := by
              calc
                (rho.storeBeforeTime S u (S.a (start + 1))).h_max = M :=
                  hexact u hu
                _ = M - 1 + 1 := hpred.symm
                _ = (rho.storeBeforeTime S u (S.a (start + 1))).h_j + 1 := by
                  rw [hju]
            certificate := hcert
            uniqueAtHeight := ?_
            targetBlock := runBlockOf_justified_atStrictRead_l1 S adm hu
              (S.a (start + 1)) } }
    intro T hT
    exact certificateTarget_unique S adm hfb (M - 1) T
      (rho.storeBeforeTime S u (S.a (start + 1))).J.root hT hcert
  · right
    intro w hw
    have hbelow : (rho.storeBeforeTime S w (S.a (start + 1))).h_j < M := by
      have hbelow' := NamedJustificationBound.justificationBelowMax_stateBeforeTime
        S rho (S.a (start + 1)) w
      have hbelow'' : (rho.storeBeforeTime S w (S.a (start + 1))).h_j <
          (rho.storeBeforeTime S w (S.a (start + 1))).h_max := by
        simpa only [Internal.JustificationBelowMax, Run.storeBeforeTime] using hbelow'
      simpa only [hexact w hw] using hbelow''
    have hne : (rho.storeBeforeTime S w (S.a (start + 1))).h_j ≠ M - 1 := by
      intro heq
      exact hgate ⟨w, hw, heq⟩
    constructor
    · have hle : (rho.storeBeforeTime S w (S.a (start + 1))).h_j ≤ M - 1 :=
        Nat.le_pred_of_lt hbelow
      have hlt : (rho.storeBeforeTime S w (S.a (start + 1))).h_j < M - 1 :=
        lt_of_le_of_ne hle hne
      have hsucc : (rho.storeBeforeTime S w (S.a (start + 1))).h_j + 1 ≤ M - 1 := by
        simpa only [Nat.succ_eq_add_one] using Nat.succ_le_iff.mpr hlt
      calc
        (rho.storeBeforeTime S w (S.a (start + 1))).h_j + 2 =
            ((rho.storeBeforeTime S w (S.a (start + 1))).h_j + 1) + 1 := by
              exact (Nat.add_assoc _ 1 1).symm
        _ ≤ (M - 1) + 1 := Nat.add_le_add_right hsucc 1
        _ = M := hpred
    · exact hexact w hw

/-- The windowed form of `frontierRegime_after_oneDelay`. -/
theorem frontierRegime_window_after_oneDelay
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) (hsb : SlashableBound S rho)
    {start : Round} {M : Height} {lo hi : Time}
    (hM : honestHMaxAt S rho (S.a start) = M)
    (hpost : S.E.t_GST ≤ S.a start)
    (hrelay : S.a start + 1 + S.E.Δ ≤ lo)
    (hcap : honestHMaxAt S rho hi ≤ M)
    (hhor : hi ≤ rho.horizon) (h2 : 2 ≤ M) :
    (∃ u ∈ rho.honest, ∃ read : Time, lo ≤ read ∧ read ≤ hi ∧
      FixedHeightJustificationRootAtRead S rho M u read) ∨
    (∀ read : Time, lo ≤ read → read ≤ hi → ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w read).h_max = M) := by
  let n := inclusiveEventIndex rho (S.a start)
  have hprefix : honestHMaxBeforeIndex S rho n = M := by
    rw [← honestHMaxAt_eq_honestHMaxBeforeIndex
      S adm.toNamedScheduleWellFormed (S.a start)]
    exact hM
  have hpred : M - 1 + 1 = M :=
    Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans h2)
  have hprefixSucc : honestHMaxBeforeIndex S rho n = M - 1 + 1 := by
    rw [hprefix, hpred]
  obtain ⟨holder, hholder, carrier, hcarrierMem, hcarrierRun, hcarrierHeight⟩ :=
    exists_honest_exactHMaxCarrierAtPrefix S adm n (M - 1) hprefixSucc
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.stateBefore S n holder).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n holder).1.1.1
  have hcarrierT : carrier.erase ∈ (rho.stateBefore S n holder).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hcarrierMem
  have hcarrier : HonestHMaxCarrierAt S rho (S.a start) M holder carrier.erase :=
    { holderHonest := hholder
      processed := by
        rw [storeAt_eq_stateBefore_inclusiveEventIndex
          S adm.toNamedScheduleWellFormed holder (S.a start)]
        exact hcarrierT
      namedWitness := ⟨carrier, rfl, hcarrierRun,
        by simpa only [hpred] using hcarrierHeight⟩ }
  have hexact : ∀ read : Time, lo ≤ read → read ≤ hi → ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w read).h_max = M := by
    intro read hlo hhi w hw
    have hreadHor : read ≤ rho.horizon := hhi.trans hhor
    have hreadCap : honestHMaxAt S rho read ≤ M :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hhi).trans hcap
    exact (hcarrier.visibleWithExactFrontier_after_oneDelay_of_noRise
      S adm hsb hpost (hrelay.trans hlo) hreadHor hreadCap w hw).2
  by_cases hgate : ∃ u ∈ rho.honest, ∃ read : Time, lo ≤ read ∧ read ≤ hi ∧
      (rho.storeBeforeTime S u read).h_j = M - 1
  · rcases hgate with ⟨u, hu, read, hlo, hhi, hju⟩
    left
    refine ⟨u, hu, read, hlo, hhi, ?_⟩
    obtain ⟨C, hC, hCrun, hjust⟩ :=
      justificationCarrierAtStrictRead_l1 S adm hu read
    have hjust' : Internal.NamedJustifiedAt S.E S.cfg C
        (rho.storeBeforeTime S u read).J (M - 1) := by
      simpa only [hju] using hjust
    have hMsubPos : 0 < M - 1 :=
      Nat.sub_pos_iff_lt.mpr ((by decide : 1 < 2).trans_le h2)
    have hcert : Certificate S rho (M - 1)
        (rho.storeBeforeTime S u read).J.root :=
      certificate_of_justifiedRunBlock_l1 S hCrun hjust'
        (Nat.ne_of_gt hMsubPos)
    refine
      { readerHonest := hu
        readInHorizon := hhi.trans hhor
        carrierExists := ⟨C, hC, hCrun, hjust⟩
        targetHeightPositive := hMsubPos
        fixedTarget :=
          { frontier := hexact read hlo hhi u hu
            justificationHeight := hju
            gate := by
              calc
                (rho.storeBeforeTime S u read).h_max = M :=
                  hexact read hlo hhi u hu
                _ = M - 1 + 1 := hpred.symm
                _ = (rho.storeBeforeTime S u read).h_j + 1 := by
                  rw [hju]
            certificate := hcert
            uniqueAtHeight := ?_
            targetBlock := runBlockOf_justified_atStrictRead_l1 S adm hu read } }
    intro T hT
    exact certificateTarget_unique S adm hfb (M - 1) T
      (rho.storeBeforeTime S u read).J.root hT hcert
  · right
    intro read hlo hhi w hw
    have hbelow : (rho.storeBeforeTime S w read).h_j < M := by
      have hbelow' := NamedJustificationBound.justificationBelowMax_stateBeforeTime
        S rho read w
      have hbelow'' : (rho.storeBeforeTime S w read).h_j <
          (rho.storeBeforeTime S w read).h_max := by
        simpa only [Internal.JustificationBelowMax, Run.storeBeforeTime] using hbelow'
      simpa only [hexact read hlo hhi w hw] using hbelow''
    have hne : (rho.storeBeforeTime S w read).h_j ≠ M - 1 := by
      intro heq
      exact hgate ⟨w, hw, read, hlo, hhi, heq⟩
    refine ⟨?_, hexact read hlo hhi w hw⟩
    have hle : (rho.storeBeforeTime S w read).h_j ≤ M - 1 :=
      Nat.le_pred_of_lt hbelow
    have hlt : (rho.storeBeforeTime S w read).h_j < M - 1 :=
      lt_of_le_of_ne hle hne
    have hsucc : (rho.storeBeforeTime S w read).h_j + 1 ≤ M - 1 := by
      simpa only [Nat.succ_eq_add_one] using Nat.succ_le_iff.mpr hlt
    calc
      (rho.storeBeforeTime S w read).h_j + 2 =
          ((rho.storeBeforeTime S w read).h_j + 1) + 1 := by
            exact (Nat.add_assoc _ 1 1).symm
      _ ≤ (M - 1) + 1 := Nat.add_le_add_right hsucc 1
      _ = M := hpred


namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms frontierBlock_filtered_of_gateOff
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
