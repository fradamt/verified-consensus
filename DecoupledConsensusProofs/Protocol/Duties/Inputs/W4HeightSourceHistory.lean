module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBase
public import DecoupledConsensusProofs.Protocol.ChainState.RowFreshness
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalRegimeRound
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PostGainOpeningStableWrite
public import DecoupledConsensusProofs.Execution.HeightFieldAssembly
public import DecoupledConsensusProofs.Execution.HandoverHeight
public import DecoupledConsensusProofs.Protocol.Grades.W4CarrierWindowPin

@[expose] public section

/-!
# The named height-source history at a later honest head ( h1)

`canonicalHeightSourceHistoryAt_laterHead_after_SG_healing`
(`FullFGSourceAfterSafetyRun.lean:127`) is the fact the moving chain's boundary
needs: every honest height row of a post-deadline round has its finality-gadget
source below every sufficiently late honest head. It sits behind
`FGSafetySourceRun`, and its own statement is in the retired erased shapes, so
it is restated here over the named base.

Both source tiers already have clean producers, and this leaf's two consumers
in `W4HandoffBoundaryRun` already use the same two head lemmas:

* the clear tier lands on `genuineConfirmationWith_preceq_laterVoterHeads_after_GST`
  (`SGLifetimeNamedRun.lean:1365`), the lemma that closes the boundary's head
  input;
* the selected-grade-2 tier lands on `G1_preceq_honestPreviousActionCarrier_atRead`
  (`SeedBaseRun.lean:249`) and then `actionSGBlock_preceq_voterHeadAt_after_GST`
  (`SGLifetimeNamedRun.lean:693`), the lemma that closes the boundary's carrier
  ceiling.

The tier split is the live erased `actionFGSource_genuineClear_or_selectedG2`
(`RecoveryFGSelectorCasesRun.lean:32`), whose clear arm already states its
genuine confirmation at the PREPARED contract, so no contract bridge is added.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

-- moved from DecoupledConsensusProofs/HealingSurface/RecoveryFGSelectorCasesRun.lean (C1)

theorem w4PreparedFgSource_preceq_laterVoterHead_of_pin
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round} (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    {d : Slot} (hd : S.hc.opening_slot r + 1 ≤ d)
    (hhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q B : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some B)
    (_of_selectedG2_preceq_honestPreviousCarrier : ∀ (A : Block V),
      PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some A →
      ∃ u ∈ rho.honest, Block.Preceq A (actionSGBlockAt S rho u (r - 1))) :
    Block.Preceq B (voterHeadAt S rho w d) := by
  have hsourceHor : S.a r ≤ rho.horizon := by
    calc
      S.a r = Protocol.vote_time S.E (S.hc.opening_slot r + 1) + S.E.Δ := by
        rw [vote_time_succ_add_delta_eq_confirmation_time,
          opening_confirmation_time_eq_action]
      _ ≤ Protocol.vote_time S.E d + S.E.Δ :=
        Int.add_le_add_right (vote_time_mono_slots S.E hd) _
      _ ≤ rho.horizon := hhor
  have hdhor : Protocol.vote_time S.E d ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
  have hslot : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 + 1) + 1 ≤
      S.hc.opening_slot r :=
    Nat.succ_le_of_lt (Nat.mul_lt_mul_of_pos_right
      (show fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 + 1 < r
        from hr)
      (Nat.zero_lt_of_lt S.hc.R_ge_two))
  rcases actionFGSource_genuineClear_or_selectedG2_named S rho v r hQ hsource
    with ⟨C, hC, _, _, _, hBC⟩ | hBQ
  · exact Block.preceq_trans hBC
      (genuineConfirmationWith_preceq_laterVoterHeads_after_GST S adm hcom
        hbelow hrec hdelay hpost (Nat.le_refl _) hslot
        (by simpa only [opening_confirmation_time_eq_action] using hsourceHor)
        hv hC d hd hdhor w hw)
  · have hr3 : 3 ≤ r := (Nat.le_add_left 3 _).trans hr
    have hrpos : 2 ≤ r := (by decide : 2 ≤ 3).trans hr3
    obtain ⟨u, hu, hAu⟩ :=
      _of_selectedG2_preceq_honestPreviousCarrier Q hQ
    have hprev2 : r - 2 + 1 = r - 1 := by
      change r - (1 + 1) + 1 = r - 1
      rw [← Nat.sub_sub]
      exact Nat.sub_add_cancel (Nat.le_sub_of_add_le hrpos)
    have hprevSlot : S.hc.opening_slot (r - 1) + 1 ≤ d :=
      (Nat.add_le_add_right
        (Nat.mul_le_mul_right S.hc.R (Nat.sub_le r 1)) 1).trans hd
    rw [hBQ]
    apply Block.preceq_trans hAu
    simpa only [hprev2] using actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost (c := r - 2)
        (Nat.le_sub_of_add_le ((Nat.le_succ (_ + 2)).trans hr))
      (by simpa only [hprev2] using hprevSlot) hhor hu hw

#print axioms w4PreparedFgSource_preceq_laterVoterHead_of_pin

/-- **The named height-source history at a later honest head**, over the same
pin. Named twin of `canonicalHeightSourceHistoryAt_laterHead_after_SG_healing`
(`FullFGSourceAfterSafetyRun.lean:127`), with the endpoint taken as a named
block because the history's own definition asks for one. The caller discharges
`hP` with the head equality at the endpoint's slot. -/
theorem canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q0)
    {d : Slot} (hd : S.hc.opening_slot (r - 1) + 1 ≤ d)
    (hhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    {P : NamedBlock V} (hPrun : RunBlock S rho P)
    (hP : P.erase = voterHeadAt S rho w d)
    (_of_nodeQ2 : ∀ (v : V), v ∈ rho.honest → ∀ (k : Round) (B : Block V),
      actionFGSource S (actionStoreAt S rho v k) = some B →
      ∃ A : Block V, PhaseGrades.nodeQ2 S (actionReadAt S rho v k) k = some A) :
    CanonicalHeightSourceHistoryAt S rho q0 r P := by
  intro k hk hkr v hv height hrow
  have hkd : S.hc.opening_slot k + 1 ≤ d :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R
      (Nat.le_sub_one_of_lt hkr)) 1).trans hd
  obtain ⟨Q, hsource, hmem, hheight⟩ := honestRow_height_le_source S adm hv hrow
  have hQbodyPre : Q ∈ (rho.stateBeforeTime S (S.a k) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hmem
  obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a k)
  have hQrun : RunBlock S rho Q := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N)
    simpa only [hN] using hQbodyPre
  refine ⟨Q, hsource, hQrun, ?_, hheight⟩
  have hsourceStore : actionFGSource S (actionStoreAt S rho v k) =
      some Q.erase := hsource
  obtain ⟨A, hA⟩ := _of_nodeQ2 v hv k Q.erase hsourceStore
  have hkHor : S.a k ≤ rho.horizon := by
    calc
      S.a k = Protocol.vote_time S.E (S.hc.opening_slot k + 1) + S.E.Δ := by
        rw [vote_time_succ_add_delta_eq_confirmation_time,
          opening_confirmation_time_eq_action]
      _ ≤ Protocol.vote_time S.E d + S.E.Δ :=
        Int.add_le_add_right (vote_time_mono_slots S.E hkd) _
      _ ≤ rho.horizon := hhor
  have hselectedG2 : ∀ (A : Block V),
      PhaseGrades.nodeQ2 S (actionReadAt S rho v k) k = some A →
      ∃ u ∈ rho.honest, Block.Preceq A (actionSGBlockAt S rho u (k - 1)) := by
    intro A hA'
    have hk2 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 + 1 ≤ k := by
      have hk3 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ k :=
        hq0.trans hk
      have hk2' : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ k :=
        (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _).trans hk3
      simpa only [Nat.reduceAdd, Nat.add_assoc] using hk2'
    exact w4uSelectedG2_preceq_honestPreviousCarrier_atRound S
      adm hcom hbelow hrec hdelay hpost
      ((Nat.le_add_right _ 1).trans hk2)
      (w4uDomainG2_le_horizon_of_action S hkHor) v hv A hA'
  have herase : Block.Preceq Q.erase P.erase := by
    rw [hP]
    exact w4PreparedFgSource_preceq_laterVoterHead_of_pin S adm hcom hbelow
      hrec hdelay hpost (hq0.trans hk) hkd hhor hv hw hA hsourceStore
      hselectedG2
  exact namedPreceq_of_runBlock_erase_preceq adm hQrun hPrun herase

#print axioms canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named




/-- **Every honest frontier strictly before `t` is at most one above `P0`**,
from the height gates before `t` and `P0` being held there. -/
theorem w4HonestFrontier_le_succ_of_heightGates
    (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hq : HonestQuorum S rho.honest)
    {t : Time} {P0 : NamedBlock V}
    (hgates : Protocol.PastHonestHeightGatesBelow S rho t P0)
    (hheld : ∀ v ∈ rho.honest,
      P0 ∈ (rho.stateBeforeTime S t v).st.bodies) :
    honestHMaxBeforeIndex S rho (strictEventIndex rho t) ≤
      (derive_named S.E S.cfg P0).h + 1 := by
  classical
  unfold honestHMaxBeforeIndex
  apply Finset.sup_le
  intro v hv
  obtain ⟨n, hn, hbefore⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      hadm.toNamedAdmissibleCore.sorted t
  have hnv : NamedRun.stateBeforeTime S rho t v =
      NamedRun.stateBefore S rho n v := congrFun hn v
  let pre := rho.stateBeforeTime S t v
  have hBody : P0 ∈ pre.st.bodies := hheld v hv
  have hagree : pre.st.core.σ P0.erase = derive_named S.E S.cfg P0 :=
    Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v P0 hBody
  obtain ⟨W, hWbody, hmaxW⟩ :=
    Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S rho t v
  have hheight : pre.st.core.h_max - 1 ≤ (pre.st.core.σ P0.erase).h := by
    by_cases hsmall : pre.st.core.h_max ≤ 1
    · have hBpos : 1 ≤ (pre.st.core.σ P0.erase).h := by
        rw [hagree]
        exact one_le_derive_named_h S.E S.cfg P0
      exact le_trans (Nat.sub_le _ _) (le_trans hsmall hBpos)
    · have hlarge : 1 < pre.st.core.h_max := Nat.lt_of_not_ge hsmall
      have hcross : pre.st.core.h_max - 1 < (derive_named S.E S.cfg W).h := by
        rw [hmaxW]
        exact Nat.sub_lt (Nat.zero_lt_of_lt hlarge) (by decide)
      have hgatePos : 1 ≤ pre.st.core.h_max - 1 :=
        Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlarge)
      obtain ⟨X, hXW, -, Q, hQ, hwit⟩ :=
        NamedFinalityCertificates.height_crossing S.E S.cfg W
          (pre.st.core.h_max - 1) hgatePos hcross
      obtain ⟨i, hiQ, hiHon⟩ := exists_honest_member_of_quorum hcom hq hQ
      obtain ⟨carrier, a, hcar, ha, hai, hpair⟩ := hwit i hiQ
      have haHon : a.val_index ∈ rho.honest := by
        rw [hai]
        exact hiHon
      have hWn : W ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
        have hb : (NamedRun.stateBeforeTime S rho t v).st.bodies =
            (NamedRun.stateBefore S rho n v).st.bodies :=
          congrArg (fun x => x.st.bodies) hnv
        rw [← hb]
        exact hWbody
      obtain ⟨j, hj, ta, hacc, hsend, hem⟩ :=
        NamedOutageProvenance.honest_held_ancestor_row_emission S rho
          hadm.toNamedAdmissibleCore.toNamedUnforgeable n v hWn hcar ha haHon
      obtain ⟨e, he, -, het⟩ := hacc.1.2
      have hta : ta < t := by simpa only [het] using hbefore j e hj he
      rw [hagree]
      apply hgates a (S.a a.round) haHon hem (hsend.trans_lt hta)
        (pre.st.core.h_max - 1)
      simp only [NamedHeightPair.matchesEntry] at hpair
      cases hp : a.height_pair with
      | empty => rw [hp] at hpair; exact absurd hpair (by simp)
      | vote h entry timeout =>
          rw [hp] at hpair
          simp only [decide_eq_true_eq] at hpair
          cases timeout <;>
            simp [NamedHeightPair.erase, HeightPair.height?, hpair.1]
  rw [hagree] at hheight
  have hstore := congrArg (fun x => x.h_max)
    (storeBeforeTime_eq_stateBefore_strictEventIndex S
      hadm.toNamedAdmissibleCore.toNamedScheduleWellFormed v t)
  simp only [Run.storeBeforeTime] at hstore
  rw [← hstore]
  exact Nat.sub_le_iff_le_add.mp hheight

#print axioms w4HonestFrontier_le_succ_of_heightGates



/-- Copy of the public `inclusiveEventIndex_le_strictEventIndex_of_lt`
(`W4CarryWindowRun.lean:298`), kept local to avoid a cross-branches leaf import. -/
private theorem w4_inclusive_le_strict_of_lt
    (rho : Run V) {t0 t1 : Time} (hlt : t0 < t1) :
    inclusiveEventIndex rho t0 ≤ strictEventIndex rho t1 := by
  unfold inclusiveEventIndex strictEventIndex
  exact (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_le_of_lt he hlt)).length_le


/-- **The shared cap in the public inclusive form the corresponding branch consumes.** Their
hypothesis is `honestHMaxAt S rho (domain r.g2) ≤ h(Pprev) + 1`; read this at
`u:= domain r.g2` and `t:= S.a r`, whose strict order they discharge in
their own leaf. -/
theorem w4HonestFrontierAt_le_succ_of_heightGates
    (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hq : HonestQuorum S rho.honest)
    {t u : Time} {P0 : NamedBlock V}
    (hgates : Protocol.PastHonestHeightGatesBelow S rho t P0)
    (hheld : ∀ v ∈ rho.honest,
      P0 ∈ (rho.stateBeforeTime S t v).st.bodies)
    (hu : u < t) :
    honestHMaxAt S rho u ≤ (derive_named S.E S.cfg P0).h + 1 := by
  rw [honestHMaxAt_eq_honestHMaxBeforeIndex S
    hadm.toNamedAdmissibleCore.toNamedScheduleWellFormed u]
  exact le_trans
    (honestHMaxBeforeIndex_mono S rho (w4_inclusive_le_strict_of_lt rho hu))
    (w4HonestFrontier_le_succ_of_heightGates S hadm hcom hq hgates hheld)

#print axioms w4HonestFrontierAt_le_succ_of_heightGates








/-- **An action FG source implies a selected grade-2 block at the same read.**

`Protocol.fg_source_with` (`Healing/Action.lean:205`) matches on its `A_G2`
argument and returns `none` on `none`, and `PhaseGrades.nodeFGSource` feeds it
`Protocol.grade2_block_with` at the same contract, store and round. So a
nonempty action FG source forces a nonempty selected grade-2 block. No run
admissibility, honesty, timing or membership premise is used: this is the local
selector's own shape. The only work is the round alignment, because
`actionFGSource` reads the round off the store's own slot. -/
theorem w4NodeQ2_of_actionFGSource
    (S : Setup V) (rho : Run V) (v : V) (r : Round) {B : Block V}
    (hB : actionFGSource S (actionStoreAt S rho v r) = some B) :
    ∃ A : Block V, PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some A := by
  classical
  have hround : S.hc.round_of (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hsource : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r =
      some B := by
    simpa only [actionStoreAt, actionFGSource, PhaseGrades.nodeFGSource, hround]
      using hB
  cases hA : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      exfalso
      have hQ2 : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
          (actionReadAt S rho v r).st.core.toHealing r = none := hA
      rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ2] at hsource
      simp only [reduceCtorEq] at hsource
  | some A => exact ⟨A, rfl⟩

/-- The bundled shape the moving-chain boundary and the carrier record both
pin as `_of_nodeQ2`. -/
theorem w4NodeQ2_of_actionFGSource_all
    (S : Setup V) (rho : Run V) :
    ∀ (v : V), v ∈ rho.honest → ∀ (k : Round) (B : Block V),
      actionFGSource S (actionStoreAt S rho v k) = some B →
      ∃ A : Block V, PhaseGrades.nodeQ2 S (actionReadAt S rho v k) k = some A :=
  fun v _ k _ hB => w4NodeQ2_of_actionFGSource S rho v k hB

#print axioms w4NodeQ2_of_actionFGSource
#print axioms w4NodeQ2_of_actionFGSource_all

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
