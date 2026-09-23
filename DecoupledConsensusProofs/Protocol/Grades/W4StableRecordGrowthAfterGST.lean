module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4StableRecordGrowthFrom
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PostGainOpeningStableWrite
public import DecoupledConsensusProofs.Protocol.Schedule.W4ContinuationV4Package
public import DecoupledConsensusProofs.Generic.W4StableGrowthFast
public import DecoupledConsensusProofs.Protocol.Grades.W4LaterRoundGrade
public import DecoupledConsensusProofs.Execution.W4StableRecordGrowthCompose
public import DecoupledConsensusProofs.Protocol.Grades.W4GSTZeroOpeningLifecycle
public import DecoupledConsensusProofs.Execution.W4CoverGradeInduction
public import DecoupledConsensusProofs.Execution.RecoveryWindowClosure
public import DecoupledConsensusProofs.Execution.StableRecordPreparedV4Closed

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution Statements
open Proofs.HealingSurface Proofs.HealingSurface.Handover

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The branch over the write -/




/-! ## The branch over the shared freeze cover -/






/-! ## The branch over viability and the reader's own grade

The FG arm of the freeze cover is not a separate obligation; it is what the
active arm's failure means. Splitting it leaves two inputs, and only the second
consumes the round's grade-forming participation. -/
















/-! ## The branch over the carrier inputs and the participation premise

`WeakContinuationG2Support` above is the finest-grained form of the grade
input. With the additive `AdmissibleCore` export of earlier's post-gain grade
route (`Proofs.HealingSurface.postGain_storeGrade_g2_core`) the two set inclusions no
longer have to be supplied by hand: the relative carrier window and the
action-carrier cover give them, and neither carries a participation premise. -/








/-! ## The corrected grade round

The G2 grade for a round-`q` proposal cannot form at the duty of round `q + 1`
once the SG expiry window is longer than one round. The ready view keeps every
window vote of a validator, not only its latest (`DecoupledConsensusModel.Protocol.
interpretedInputs` filters the raw inputs by `bodyReady` alone), and
`DecoupledConsensusModel.Protocol.opposing` counts a validator as opposing `B` as soon
as ANY of its window votes fails to cover `B`. The round-`d` window runs from
`d - η_SG` to `d`, so at `d = q + 1` it reaches back before `q`, where honest
validators voted at or below `B`'s parent and therefore oppose `B`.

At `d = q + η_SG` the window is exactly the rounds `q` through `q + η_SG - 1`,
every one at or after the proposal's own round. That is the first duty at which
the grade can form, and the widened public deadline `gap + η_SG - 1` pays for
precisely that lag. -/




/-! ## The tight-deadline branch, and the fast twin

`stableRecordGrowthFrom_of_openingWriteAbove` already concludes at the
recurrence's own gap; the widened public form is its `mono_gap` weakening. The
tight form is therefore available for free, and it is what the separate fast
result needs. -/






















theorem dutyHeadWitnessAll_closed (S : Setup V) : DutyHeadWitnessAll S :=
  fun _rho core _r hr _v hv => Proofs.w4_dutyHeadWitness S core hr hv

#print axioms dutyHeadWitnessAll_closed







/-- The persistence cover at one round: every honest round-`k` SG vote is at or
above the proposal. -/
def W4Cover (S : Setup V) (rho : Run V) (B : NamedBlock V) (k : Round) : Prop :=
  ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k,
    Block.Preceq B.erase (actionSGBlockAt S rho u k)

/-- The reader's own G2 cover at one duty round, at every honest reader. -/
def W4Grade (S : Setup V) (rho : Run V) (B : NamedBlock V) (k : Round) : Prop :=
  ∀ v ∈ rho.honest, LocalG2CoverAtDutyRound S rho k B.erase v










/-- **The delivery content of the round-`d` carrier window**: the honest votes
of the window reached every honest reader's tree by the round-`d` G2 read, and
the reader's ready view is nonempty over the awake window. `B` does not occur,
so no cover and no grade fact is hidden here. -/
def W4WindowDeliveryAt (S : Setup V) (rho : Run V) (d : Round) : Prop :=
  (∀ w ∈ rho.honest, ∀ k : Round, d - S.hc.η_SG ≤ k → k < d →
    ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k,
      Block.find?
          (Internal.PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.T
          (actionSGBlockAt S rho u k).root =
        some (actionSGBlockAt S rho u k))
  ∧ W4WindowReadyAt S rho d

/-- **The carrier window from cover on the window's own rounds plus delivery.** -/
theorem w4WindowCarrierAt_of_cover_and_delivery (S : Setup V) {rho : Run V}
    {d : Round} {B : NamedBlock V}
    (hcover : ∀ j : Round, d - S.hc.η_SG ≤ j → j < d → W4Cover S rho B j)
    (hdel : W4WindowDeliveryAt S rho d) :
    W4WindowCarrierAt S rho d B.erase := by
  intro w hw k hk1 hk2 u hu
  exact ⟨hcover k hk1 hk2 u hu, hdel.1 w hw k hk1 hk2 u hu⟩

#print axioms w4WindowCarrierAt_of_cover_and_delivery

/-- **The reader holds the proposal at the round-`d` G2 read.** The awake window
is nonempty because it carries a majority, its validator voted in a window round
at or above `B` by cover, that vote reached the reader by delivery, and the
reader's tree is parent closed. -/
theorem w4_mem_of_cover_and_delivery (S : Setup V) {rho : Run V}
    (core : AdmissibleCore S rho) {d : Round} {B : NamedBlock V}
    (hahor : S.a (d - 1) ≤ rho.horizon)
    (hmajority : Execution.AwakeWindowMajority S.E
      (fun x => (S.node x).awake) rho.honest S.hc.η_SG d)
    (hdel : W4WindowDeliveryAt S rho d)
    (hcover : ∀ j : Round, d - S.hc.η_SG ≤ j → j < d → W4Cover S rho B j)
    {w : V} (hw : w ∈ rho.honest) :
    B.erase ∈ (Internal.PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.T := by
  classical
  have hne : (Execution.honestAwakeWindow (fun x => (S.node x).awake)
      rho.honest S.hc.η_SG d).Nonempty := by
    rcases Finset.eq_empty_or_nonempty
      (Execution.honestAwakeWindow (fun x => (S.node x).awake)
        rho.honest S.hc.η_SG d) with hempty | hsome
    · exfalso
      have hlt := hmajority
      simp only [Execution.AwakeWindowMajority, hempty,
        Electorate.weightOf, Finset.sum_empty] at hlt
      exact Nat.not_lt_zero _ hlt
    · exact hsome
  obtain ⟨u, hu⟩ := hne
  obtain ⟨huHon, k, hkmem, hawakeu⟩ :=
    Proofs.HealingSurface.WeakSG.mem_honestAwakeWindow_iff.mp hu
  obtain ⟨hklo, hkhi⟩ := NamedOutageClosure.window_bounds hkmem
  have hkhor : S.a k ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_pred_of_lt hkhi)).trans hahor
  have hkvoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k :=
    Proofs.awakeRound_subset_honestRoundVoters S
      core.toNamedScheduleWellFormed hkhor
      (Finset.mem_filter.mpr ⟨huHon, hawakeu⟩)
  have hcov := hcover k hklo hkhi u hkvoter
  have hfind := hdel.1 w hw k hklo hkhi u hkvoter
  have hmemB : actionSGBlockAt S rho u k ∈
      (Internal.PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.T :=
    Proofs.Records.mem_of_bind_find?
      (o := some (actionSGBlockAt S rho u k).root) hfind
  have hpc := (parentClosed_iff (Internal.PhaseGrades.readAt S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core).mp
    (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w)
  exact Proofs.Records.mem_of_preceq hpc.2 B.erase (actionSGBlockAt S rho u k) hmemB hcov

#print axioms w4_mem_of_cover_and_delivery

/-- **The grade step**: the round-`d` G2 cover at every honest node's duty read
follows from cover at the window's rounds, all strictly below `d`, together with
the awake-window majority and the window's delivery. This is the half of
`WeakContinuationSteps` that does not touch the confirmation walk, so it is
independent of the anchor alignment the cover step waits on. -/
theorem w4Grade_of_cover_below (S : Setup V) {rho : Run V}
    (core : AdmissibleCore S rho) {d : Round} (hd : 0 < d) {B : NamedBlock V}
    (hahor : S.a (d - 1) ≤ rho.horizon)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2 ≤ rho.horizon)
    (hmajority : Execution.AwakeWindowMajority S.E
      (fun x => (S.node x).awake) rho.honest S.hc.η_SG d)
    (hdel : W4WindowDeliveryAt S rho d)
    (hcover : ∀ j : Round, d - S.hc.η_SG ≤ j → j < d → W4Cover S rho B j) :
    W4Grade S rho B d := by
  intro w hw
  exact w4_localG2CoverAtDutyRound_of_windowCarrier S core hd hhor hmajority
    (w4WindowCarrierAt_of_cover_and_delivery S hcover hdel) hdel.2 hw
    (w4_mem_of_cover_and_delivery S core hahor hmajority hdel hcover hw)

#print axioms w4Grade_of_cover_below


/-- **The window's delivery after GST.** The unwindowed
`NamedHealthyPrefixDelivery` that `w4WindowDeliveryAt_of_delivery` needs is not
available after GST; what admissibility gives is the windowed
`NamedHealthyWindowDelivery` from `S.E.t_GST` on
(`NamedOutageClosure.healthyWindowDelivery_after_gst`). The carrier-window
producer has a windowed twin, so the continuation can use it directly and the
 boundary does not bite here. -/
theorem w4WindowDeliveryAt_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {base d : Round} {D : Block V} (hd : 0 < d)
    (hspan : base ≤ d - S.hc.η_SG)
    (hsendLo : ∀ k, base ≤ k → k < d → S.E.t_GST ≤ S.a k)
    (hawake : Execution.AwakeWindowMajority S.E
      (fun v => (S.node v).awake) rho.honest S.hc.η_SG d)
    (hsg : ∀ k, base ≤ k → k < d → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) D)
    (hroots : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w d).st.core.toHealing.toFG) D)
    (hcap : DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2 ≤ rho.horizon) :
    W4WindowDeliveryAt S rho d := by
  classical
  have hwin :=
    Proofs.HealingSurface.WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_w
      S adm (NamedOutageClosure.healthyWindowDelivery_after_gst S rho adm)
      (le_refl _) (le_refl _) hd hspan hsendLo hawake hsg hroots .g2 hcap
  constructor
  · intro w hw k hklo hkhi u hu
    obtain ⟨huHon, a, hval, haround, hemit⟩ :=
      (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mp hu
    have hawakeu : (S.node u).awake k = true := by
      simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
    obtain ⟨y, -, -, -, hfind⟩ := hwin w hw u huHon k
      (NamedOutageClosure.mem_latest_window hklo hkhi) hawakeu
    exact hfind
  · intro w hw u hu
    obtain ⟨huHon, k, hkmem, hawakeu⟩ :=
      Proofs.HealingSurface.WeakSG.mem_honestAwakeWindow_iff.mp hu
    obtain ⟨y, hy, -, -, -⟩ := hwin w hw u huHon k hkmem hawakeu
    exact ⟨DecoupledConsensusModel.Protocol.token y,
      Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hy⟩

#print axioms w4WindowDeliveryAt_after_gst






































end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
