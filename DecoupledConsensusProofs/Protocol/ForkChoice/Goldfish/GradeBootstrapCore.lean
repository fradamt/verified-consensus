module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal
public import DecoupledConsensusInternal.Definitions.ActionSources
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone
public import DecoupledConsensusProofs.Protocol.Grades.HonestMajority
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGRepresentation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Grades.Anchor
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Store.RawSource
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

/-!
# A finalized-floor seed for the first common recovery grade

The final Section 7 SG selector never moves behind its current FG root. This
file proves that fact for all three selector branches and lifts it to the exact
round-action store.

At run level, the weakest order premise is one common block below every honest
action-store FG root. The existing finalized-prefix theorem produces that
premise when every honest store had already finalized the common block before
the action. With next-read activity, the existing carrier-concentration
theorem then forms the first common G2 in the next round.

The activity premise is substantive. A historical finalized block need not
itself remain in the filtered tree after the local finalized or FG root moves
above it. Finality monotonicity therefore supplies the common carrier floor,
but does not supply next-read activity. The final theorem removes that premise
with the exact alternative: common G2 at the next read, or strict FG-root and
actual `get_head_hc` progress from the historical floor at one honest store.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Reflexivity of named ancestry, the shape `NamedRootCollisionFree
.root_injective` takes. `Availability/BlockAdmissionRun.lean` keeps an identical
file-private copy. -/
private theorem named_preceq_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

/-! ## 2. A clean grade read forms a common active G2 -/

/-- A strict honest-weight majority has at least the absolute grade threshold
`m = floor(W/2) + 1`. -/
theorem honestWeight_ge_m
    {S : Setup V} {H : Finset V} (hmajority : HonestWeightMajority S H) :
    S.E.m ≤ S.E.electorate.weightOf H := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold HonestWeightMajority at hmajority
  unfold Env.m Electorate.strictMajorityThreshold
  omega



/-! ## 1. The exact store and value used by the Section 7 action -/

/-- The exact SG projection emitted by validator `v` in round `r`. -/
def actionSGVoteAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.SGVote V :=
  ⟨v, r, some (actionSGBlockAt S rho v r).root⟩


/-- At a round action the store is the named confirmation write on the
support-cutoff read, with the action read's own cache contract.

Statement change (ledger row C): `actionStoreAt` is a
`NamedNodeState`, and `NamedActionReads.actionReadFrom` applies
`Protocol.NamedDuties.update_confirmation_with` unconditionally, so the prior
`if_pos` branch selection is definitional and the prior
`Proofs.Optimistic.attestStore`/`tickStore` pair no longer appears. -/
theorem actionStoreAt_eq_update_confirmation
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).st =
      Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract (actionStoreAt S rho v r).cache) S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (rho.stateBeforeTime S (S.a r) v) (S.a r)).st
        (S.E.slotOf (S.a r) - 1) := rfl


/-- The SG projection has the exact Section 7 value. -/
theorem actionSGVoteAt_shape
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionSGVoteAt S rho v r).val_index = v ∧
      (actionSGVoteAt S rho v r).round = r ∧
      (actionSGVoteAt S rho v r).confirmed =
        some (actionSGBlockAt S rho v r).root := by
  exact ⟨rfl, rfl, rfl⟩


/-- Every awake scheduled honest action emits an attestation whose SG projection is
the exact post-confirmation action value above. -/
theorem sgVote_actionAttestationAt
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.sgVote (actionAttestationAt S rho v r).erase =
      actionSGVoteAt S rho v r := by
  obtain ⟨hval, hround, hconf⟩ := actionAttestationAt_shape S rho v r
  have hsplit : Protocol.sgVote (actionAttestationAt S rho v r).erase =
      ⟨(actionAttestationAt S rho v r).val_index,
        (actionAttestationAt S rho v r).round,
        (actionAttestationAt S rho v r).confirmed⟩ := rfl
  rw [hsplit, hval, hround, hconf]
  rfl

theorem honest_emits_actionAttestationAt_of_awake
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    (hhor : S.a r ≤ rho.horizon) (hA : (S.node v).awake r = true) :
    ∃ a : NamedAttestation V,
      rho.emits S v (Object.attest a) (S.a r) ∧
        Protocol.sgVote a.erase = actionSGVoteAt S rho v r :=
  ⟨actionAttestationAt S rho v r,
    honest_emits_exact_actionAttestationAt_of_awake S sch hv r hA hhor,
    sgVote_actionAttestationAt S rho v r⟩

/-- The full-participation form. Its admissibility premise supplies awake
participation; the core schedule alone does not imply an emission. -/
theorem honest_emits_actionAttestationAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    (hhor : S.a r ≤ rho.horizon) (hpost : S.E.t_GST ≤ S.a r) :
    ∃ a : NamedAttestation V,
      rho.emits S v (Object.attest a) (S.a r) ∧
        Protocol.sgVote a.erase = actionSGVoteAt S rho v r :=
  honest_emits_actionAttestationAt_of_awake S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv r hhor
    (adm.all_awake v hv r hpost hhor)



/-- One delay after `a_r` fits by the next round's earliest grade cutoff.
This is tight when `R = 2`. -/
theorem action_add_delta_le_next_Γ_neg1
    (S : Setup V) (r : Round) :
    S.a r + S.E.Δ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) := by
  have hR : (2 : Time) ≤ (S.hc.R : Nat) := by
    exact_mod_cast S.hc.R_ge_two
  change S.hc.a S.E.Δ r + S.E.Δ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1)
  unfold Protocol.HealConfig.a Protocol.HealConfig.Γ_neg1
    Protocol.HealConfig.opening_slot slotStart
  push_cast
  have hfour : (8 : Time) ≤ 4 * (S.hc.R : Time) := by
    have hm := Int.mul_le_mul_of_nonneg_left hR (by norm_num : (0 : Time) ≤ 4)
    norm_num at hm ⊢
    exact hm
  have hfactor : (0 : Time) ≤ 4 * (S.hc.R : Time) - 8 :=
    sub_nonneg.mpr hfour
  have hprod : (0 : Time) ≤ S.E.Δ * (4 * (S.hc.R : Time) - 8) :=
    Int.mul_nonneg (le_of_lt S.E.Δ_pos) hfactor
  calc
    4 * S.E.Δ * (r * S.hc.R) + 6 * S.E.Δ + S.E.Δ =
        4 * S.E.Δ * (r * S.hc.R) + 7 * S.E.Δ := by ring
    _ ≤ 4 * S.E.Δ * (r * S.hc.R) + 7 * S.E.Δ +
        S.E.Δ * (4 * S.hc.R - 8) := Int.le_add_of_nonneg_right hprod
    _ = 4 * S.E.Δ * ((r + 1) * S.hc.R) - S.E.Δ := by ring

/-- The next grade read is strictly after its earliest cutoff. -/
theorem next_Γ_neg1_lt_action (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ (r + 1) < S.a (r + 1) := by
  exact lt_of_lt_of_le
    (lt_trans
      (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))
      (lt_trans
        (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (r + 1))
        (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos (r + 1))))
    (Γ_2_le_a S.hc S.E.Δ_pos (r + 1))
/-- Section 7 action times strictly increase with the round number. -/
theorem action_strictMono (S : Setup V) : StrictMono S.a := by
  refine strictMono_nat_of_lt_succ fun r => ?_
  rw [Proofs.HealingLemmas.a_add_rounds S r 1]
  have hRnat : 0 < S.hc.R := lt_of_lt_of_le (by omega) S.hc.R_ge_two
  have hR : (0 : Time) < (S.hc.R : Nat) := by
    exact_mod_cast hRnat
  have hinc : (0 : Time) < 4 * S.E.Δ * (S.hc.R : Nat) := by
    exact Int.mul_pos (Int.mul_pos (by norm_num) S.E.Δ_pos) hR
  simpa only [Nat.mul_one] using Int.lt_add_of_pos_right (S.a r) hinc


/-- Post-GST broadcast of one honest action places its exact full named row in
every honest reader's SG rows before one delay.

 repair: the retired `Protocol.sgVote_pooled_of_emission` /
`Proofs.HealingLemmas.sgVote_pooled_of_delivery'` split is gone. `NamedSynchrony
.broadcast` already returns one handling index for every reader, and
`Proofs.NamedSGArrival.honest_row_after_call` turns that call into retention of the
original named row with no side condition. -/
theorem actionAttestationAt_rows_before_delta
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (r : Round) (hpost : S.E.t_GST ≤ S.a r)
    (hhor : S.a r + S.E.Δ ≤ rho.horizon) :
    ∃ j : Nat, ∃ e : Event V,
      rho.events[j]? = some e ∧ e.time < S.a r + S.E.Δ ∧
        actionAttestationAt S rho v r ∈
          (rho.stateBefore S (j + 1) w).st.sg_rows r := by
  have haHor : S.a r ≤ rho.horizon :=
    le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hhor
  obtain ⟨hval, haround, -⟩ := actionAttestationAt_shape S rho v r
  have hemit : rho.emits S v (Object.attest (actionAttestationAt S rho v r)) (S.a r) :=
    honest_emits_exact_actionAttestationAt S adm hv r haHor (by assumption)
  have hvalHon : (actionAttestationAt S rho v r).val_index ∈ rho.honest := by
    rw [hval]; exact hv
  have hemit' : NamedRun.emits S rho (actionAttestationAt S rho v r).val_index
      (.attest (actionAttestationAt S rho v r))
      (S.a (actionAttestationAt S rho v r).round) := by
    rw [hval, haround]; exact hemit
  have hmax : max (S.a r) S.E.t_GST = S.a r := max_eq_left hpost
  obtain ⟨t', hcausal, hlt, j, hcall⟩ :=
    adm.toNamedAdmissibleCore.toNamedSynchrony.broadcast v hv
      (Object.attest (actionAttestationAt S rho v r)) (S.a r) hemit w hw
      (by simpa only [hmax] using hhor) rfl
  have hlt' : t' < S.a r + S.E.Δ := by simpa only [hmax] using hlt
  have hrow := Proofs.NamedSGArrival.honest_row_after_call S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    adm.toNamedAdmissibleCore.toNamedUnforgeable hvalHon hemit' hcall
    (by rw [haround]; exact hcausal) (by rw [haround]; exact hlt')
  obtain ⟨-, e, he, -, het⟩ := hcall
  refine ⟨j, e, he, ?_, by rwa [haround] at hrow⟩
  rw [show Event.time e = t' from het]
  exact hlt'

/-- Post-GST broadcast of one honest action places its exact SG projection in
every honest pool before one delay. -/
theorem actionSGVote_pooled_before_delta
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (r : Round) (hpost : S.E.t_GST ≤ S.a r)
    (hhor : S.a r + S.E.Δ ≤ rho.horizon) :
    ∃ j : Nat, ∃ e : Event V,
      rho.events[j]? = some e ∧ e.time < S.a r + S.E.Δ ∧
        actionSGVoteAt S rho v r ∈
          (rho.stateBefore S (j + 1) w).st.toHealing.sg_votes r := by
  obtain ⟨j, e, he, het, hrow⟩ :=
    actionAttestationAt_rows_before_delta S adm hv hw r hpost hhor
  refine ⟨j, e, he, het, ?_⟩
  have hown : actionAttestationAt S rho v r ∈
      (rho.stateBefore S (j + 1) w).st.sg_rows
        (actionAttestationAt S rho v r).round := by
    rw [(actionAttestationAt_shape S rho v r).2.1]; exact hrow
  have hpool := NamedAdmission.pool_view_mem (rho.stateBefore S (j + 1) w).st
    (Proofs.NamedRuntime.stateBefore_invariants S rho (j + 1) w).1.1.1.2.2.2.1 _ hown
  rw [(actionAttestationAt_shape S rho v r).2.1] at hpool
  have himg := Finset.mem_image_of_mem Protocol.sgVote hpool
  rw [sgVote_actionAttestationAt] at himg
  exact himg


/-- The exact action vote, not an existential representative, belongs to every
honest reader's next grade-batch slice. -/
theorem actionSGVote_mem_next_round_batch
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (r : Round) (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon) :
    actionSGVoteAt S rho v r ∈ Protocol.sg_votes_by
      (Protocol.round_batch (gradeViewAt S rho w (r + 1)) (r + 1)) v := by
  have hdeadline : S.a r + S.E.Δ ≤ rho.horizon :=
    le_trans (action_add_delta_le_next_Γ_neg1 S r) hcut
  obtain ⟨j, e, hj, hjt, hpool⟩ :=
    actionSGVote_pooled_before_delta S adm hv hw r hpost hdeadline
  have hbefore : e.time < S.a (r + 1) :=
    lt_of_lt_of_le hjt (le_trans (action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (next_Γ_neg1_lt_action S r)))
  have hread := Protocol.sgVote_mem_stateBeforeTime_of_post S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hbefore hpool
  have hr1 : r + 1 ≠ 0 := by
    simpa only [Nat.succ_eq_add_one] using Nat.succ_ne_zero r
  apply Finset.mem_filter.mpr
  constructor
  · simpa only [Protocol.round_batch, if_neg hr1,
      Nat.add_sub_cancel, gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView] using hread
  · exact (actionSGVoteAt_shape S rho v r).1

/-! ## 3. Source-exact clean-read residual and common G2 -/

/-- The prepared G2-domain read used by the relative grade surface. -/
def relativeG2Read (S : Setup V) (rho : Run V) (r : Round) (v : V) :
    NamedNodeState V :=
  readAt S rho (domain S.E S.hc r .g2) v


/-- R48b: domain read included,.

Retention at the next round's G2-domain read is the same filtered-tree
membership used by the relative-grade read. The retained-read premise is
written unfolded to preserve the proof-layer import direction. -/
theorem activeDomain_of_retainedAtDomainRead
    (S : Setup V) {rho : Run V} {r : Round} {P : Block V}
    (hretainedAtRead : ∀ w ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.toFG) :
    ∀ w ∈ rho.honest,
      P ∈ filteredTree (relativeG2Read S rho (r + 1) w) := by
  intro w hw
  simpa only [relativeG2Read,
    PhaseGrades.readAt, PhaseGrades.filteredTree] using hretainedAtRead w hw

/-- The remaining producer condition for a clean action round.

Broadcast and pool insertion are theorems above. What remains explicit is the
source condition itself: the exact action vote's named block resolves before
the next `Gamma[-1]` cutoff at every reader and covers one common active prefix.
This is where block admission and resolution, rather than grade delivery, enter.
-/
structure CleanActionReadFor (S : Setup V) (rho : Run V) (r : Round)
    (P : Block V) : Prop where
  post_gst : S.E.t_GST ≤ S.a r
  cutoff_in_horizon : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon
  
  active : ∀ w ∈ rho.honest,
    P ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w (r + 1)).toFG
  
  active_domain : ∀ w ∈ rho.honest,
    P ∈ filteredTree (relativeG2Read S rho (r + 1) w)
  resolved_support : ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
    occurrenceBefore
        (Protocol.sg_resolution_time (gradeViewAt S rho w (r + 1)).T
          (gradeViewAt S rho w (r + 1)).timestamp_block
          (gradeViewAt S rho w (r + 1)).timestamp_sg_vote
          (actionSGVoteAt S rho v r))
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true ∧
      Protocol.head_covers (gradeViewAt S rho w (r + 1)).T P
        (actionSGVoteAt S rho v r).confirmed = true



namespace GradeDeliveryRun


/-- A projected pool member at a prefix state names the original full row that
carries it, in its own bucket. -/
theorem exists_row_of_mem_sg_votes (S : Setup V) (rho : Run V) (i : Nat) (v : V)
    {u : Protocol.SGVote V} {k : Round}
    (hu : u ∈ (rho.stateBefore S i v).st.toHealing.sg_votes k) :
    ∃ a : NamedAttestation V,
      a ∈ (rho.stateBefore S i v).st.sg_rows a.round ∧
        a.round = k ∧ Protocol.sgVote a.erase = u := by
  change u ∈ ((rho.stateBefore S i v).st.core.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨b, hb, hbu⟩ := Finset.mem_image.mp hu
  have hpool := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1.2.2.2.1 k
  change b ∈ ((rho.stateBefore S i v).st.core.sg_votes k).toFinset at hb
  rw [hpool] at hb
  obtain ⟨a, ha, hab⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  have hround : a.round = k :=
    NamedRawSource.row_round_stateBefore S rho i v k a ha
  exact ⟨a, by rw [hround]; exact ha, hround, by rw [hab]; exact hbu⟩

/-- The strict-read twin of `exists_row_of_mem_sg_votes`. -/
theorem exists_row_of_mem_sg_votes_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (read : Time) {u : Protocol.SGVote V} {k : Round}
    (hu : u ∈ (rho.storeBeforeTime S v read).toHealing.sg_votes k) :
    ∃ a : NamedAttestation V,
      a ∈ (rho.storeBeforeTime S v read).sg_rows a.round ∧
        a.round = k ∧ Protocol.sgVote a.erase = u := by
  change u ∈ ((rho.storeBeforeTime S v read).core.sg_pool k).image
    Protocol.sgVote at hu
  obtain ⟨b, hb, hbu⟩ := Finset.mem_image.mp hu
  have hpool :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read v).1.1.1.2.2.2.1 k
  have hb' : b ∈ List.map NamedAttestation.erase
      ((NamedRun.stateBeforeTime S rho read v).st.sg_rows k) := by
    rw [← hpool]
    exact List.mem_toFinset.mp hb
  obtain ⟨a, ha, hab⟩ := List.mem_map.mp hb'
  have hround : a.round = k :=
    NamedRawSource.row_round_stateBeforeTime S rho sch read v k a ha
  refine ⟨a, ?_, hround, by rw [hab]; exact hbu⟩
  show a ∈ (NamedRun.stateBeforeTime S rho read v).st.sg_rows a.round
  rw [hround]
  exact ha

/-- Once a projected SG vote is pooled, its receipt stamp is write-once along
the remainder of the run. -/
theorem stateBefore_timestamp_sg_vote_carry
    (S : Setup V) (rho : Run V) (v : V) {i : Nat} :
    ∀ j : Nat, i ≤ j → ∀ {u : Protocol.SGVote V} {k : Round},
      u ∈ (rho.stateBefore S i v).st.toHealing.sg_votes k →
      (rho.stateBefore S j v).st.timestamp_sg_vote u =
        (rho.stateBefore S i v).st.timestamp_sg_vote u := by
  intro j hij u k hu
  obtain ⟨a, ha, -, hproj⟩ := exists_row_of_mem_sg_votes S rho i v hu
  have hcarry := (Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho v hij ha).2
  rw [← hproj]
  exact hcarry

/-- A projected receipt stamp present after an event strictly before `t`
persists to the store read immediately before `t`. -/
theorem timestamp_sg_vote_stateBeforeTime_of_post
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} {j : Nat} {e : Event V} {t : Time} {k : Round}
    {u : Protocol.SGVote V}
    (hj : rho.events[j]? = some e) (hjt : e.time < t)
    (hu : u ∈ (rho.stateBefore S (j + 1) w).st.toHealing.sg_votes k) :
    (rho.storeBeforeTime S w t).timestamp_sg_vote u =
      (rho.stateBefore S (j + 1) w).st.timestamp_sg_vote u := by
  let N := (rho.events.filter (fun x => decide (x.time < t))).length
  have hjN : j < N := by
    by_contra hnot
    have htle : t ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S sch (t := t) (j := j) (e := e)
        (by simpa [N] using Nat.le_of_not_gt hnot) hj
    exact (not_le_of_gt hjt) htle
  have hcarry := stateBefore_timestamp_sg_vote_carry S rho w
    (i := j + 1) N (Nat.succ_le_of_lt hjN) hu
  have hstore : rho.storeBeforeTime S w t = (rho.stateBeforeTime S t w).st := rfl
  rw [hstore, Proofs.Optimistic.stateBeforeTime_eq_take S sch t]
  exact hcarry

/-! ## 3. The accepting event writes the receipt stamp -/


/-- A projected vote and its receipt stamp in a read store expose one exact
accepted full named row whose acceptance precedes the same public cutoff.

Statement change (ledger row C): the witness is the retained
`NamedAttestation`, not a bare `CombinedAttestation`, and its projection is read
through `NamedAttestation.erase`. `Object.attest` now takes a named row. -/
theorem accepted_attestation_of_projected_stamp_before
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p : V} (_hp : p ∈ rho.honest) {read Gamma : Time} {k : Round}
    {u : Protocol.SGVote V}
    (hpub : PublicTime S Gamma)
    (hu : u ∈ (rho.storeBeforeTime S p read).toHealing.sg_votes k)
    (hstamp : occurrenceBefore
      ((rho.storeBeforeTime S p read).timestamp_sg_vote u) Gamma = true) :
    ∃ (a : NamedAttestation V) (i : Nat) (ta : Time),
      Protocol.sgVote a.erase = u ∧
      NamedRun.acceptsAt S rho i p (Object.attest a) ta ∧ ta < Gamma := by
  have sch : ScheduleWellFormed S rho :=
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  obtain ⟨a, ha, -, hproj⟩ :=
    exists_row_of_mem_sg_votes_storeBeforeTime S sch p read hu
  have ha' : a ∈ (NamedRun.stateBeforeTime S rho read p).st.sg_rows a.round := ha
  have hstamp' : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho read p).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) Gamma = true := by
    show occurrenceBefore
      ((rho.storeBeforeTime S p read).timestamp_sg_vote
        (Protocol.sgVote a.erase)) Gamma = true
    rw [hproj]
    exact hstamp
  obtain ⟨i, ta, hlt, hacc⟩ :=
    NamedPublicCutSG.sg_row_accepted_before_public_cut S rho sch hpub ha' hstamp'
  exact ⟨a, i, ta, hproj, hacc, hlt⟩

/-- Any exact row already held after event `i` has a receipt stamp below every
later strict cutoff. -/
theorem timestamp_sg_vote_before_of_mem_post_event
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} {i : Nat} {e : Event V} {a : NamedAttestation V}
    {Gamma : Time} (hi : rho.events[i]? = some e)
    (ha : a ∈ (rho.stateBefore S (i + 1) v).st.sg_rows a.round)
    (heGamma : e.time < Gamma) :
    occurrenceBefore
      ((rho.stateBefore S (i + 1) v).st.timestamp_sg_vote
        (Protocol.sgVote a.erase)) Gamma = true := by
  obtain ⟨-, stamp, hle, heq⟩ :=
    Proofs.NamedSGArrival.held_row_own_and_stamp_at_event S rho sch hi v a.round a ha
  have heq' : (rho.stateBefore S (i + 1) v).st.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (stamp : Stamp) := heq
  have hlt : stamp < Gamma := lt_of_le_of_lt hle heGamma
  rw [heq']
  simp only [occurrenceBefore, decide_eq_true_eq]
  exact WithBot.coe_lt_coe.mpr hlt

theorem projected_vote_mem_stamp_at_read
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} {j : Nat} {e : Event V} {read Gamma : Time} {k : Round}
    {u : Protocol.SGVote V}
    (hj : rho.events[j]? = some e) (heGamma : e.time < Gamma)
    (hGammaRead : Gamma ≤ read)
    (hu : u ∈ (rho.stateBefore S (j + 1) w).st.toHealing.sg_votes k)
    (hut : occurrenceBefore
      ((rho.stateBefore S (j + 1) w).st.timestamp_sg_vote u) Gamma = true) :
    u ∈ (rho.storeBeforeTime S w read).toHealing.sg_votes k ∧
      occurrenceBefore
        ((rho.storeBeforeTime S w read).timestamp_sg_vote u) Gamma = true := by
  have heRead : e.time < read := lt_of_lt_of_le heGamma hGammaRead
  constructor
  · exact Protocol.sgVote_mem_stateBeforeTime_of_post S sch hj heRead hu
  · have hcarry := timestamp_sg_vote_stateBeforeTime_of_post S sch hj heRead hu
    rwa [hcarry]

end GradeDeliveryRun

/-! ## Fixed-cutoff transport of the vote and its named block -/

/-- The exact action vote has a receipt stamp before the next earliest grade
cutoff at every honest reader. -/
theorem actionSGVote_stamp_before_next_Γ_neg1
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (r : Round) (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon) :
    occurrenceBefore
      ((gradeViewAt S rho w (r + 1)).timestamp_sg_vote
        (actionSGVoteAt S rho v r))
      (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
  have sch : ScheduleWellFormed S rho :=
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hdeadline : S.a r + S.E.Δ ≤ rho.horizon :=
    le_trans (action_add_delta_le_next_Γ_neg1 S r) hcut
  obtain ⟨j, e, hj, heDelta, hrow⟩ :=
    actionAttestationAt_rows_before_delta S adm hv hw r hpost hdeadline
  obtain ⟨-, haRound, -⟩ := actionAttestationAt_shape S rho v r
  have ha' : actionAttestationAt S rho v r ∈
      (rho.stateBefore S (j + 1) w).st.sg_rows
        (actionAttestationAt S rho v r).round := by
    rw [haRound]; exact hrow
  have heCut : e.time < S.hc.Γ_neg1 S.E.Δ (r + 1) :=
    lt_of_lt_of_le heDelta (action_add_delta_le_next_Γ_neg1 S r)
  have hut := GradeDeliveryRun.timestamp_sg_vote_before_of_mem_post_event
    S sch hj ha' heCut
  rw [sgVote_actionAttestationAt] at hut
  have hu : actionSGVoteAt S rho v r ∈
      (rho.stateBefore S (j + 1) w).st.toHealing.sg_votes r := by
    have hpool := NamedAdmission.pool_view_mem (rho.stateBefore S (j + 1) w).st
      (Proofs.NamedRuntime.stateBefore_invariants S rho (j + 1) w).1.1.1.2.2.2.1 _ ha'
    rw [haRound] at hpool
    have himg := Finset.mem_image_of_mem Protocol.sgVote hpool
    rw [sgVote_actionAttestationAt] at himg
    exact himg
  have hread : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ S.a (r + 1) :=
    le_of_lt (next_Γ_neg1_lt_action S r)
  have hpostRead := GradeDeliveryRun.projected_vote_mem_stamp_at_read
    S sch hj heCut hread hu hut
  simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
    Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hpostRead.2

/-! ## Every actual action carrier has run provenance -/

/-- The action read's own confirmation-membership invariant. The strict read
carries it, clock staging preserves it, and the action's confirmation write is
exactly `invariant_update` at the frame contract. -/
theorem actionRead_invariant (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg (actionStoreAt S rho v r).st := by
  have h0 : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (rho.stateBeforeTime S (S.a r) v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have h1 := Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r) h0
  exact Proofs.NamedConfirmationMembership.invariant_update
    (NamedActionReads.preparedCache S (rho.stateBeforeTime S (S.a r) v) (S.a r))
    S.E S.hc S.cfg _ (S.E.slotOf (S.a r) - 1) h1


/-- The exact Section 7 SG action carrier is a processed block in the action
read's store, with no prior common-grade premise.

 repair: the three selector branches are the frame
contract's own walk, frozen candidate and anchor fallbacks. `NamedConfirmation
Membership.runtime_anchor_mem` and `runtime_Q2_mem` cover the two fallbacks for
the frame mode, and the walk branch stays below `live_confirmed`. The retired
`Proofs.Bridges.depReachable_stateBeforeTime` chain is not resurrected. -/
theorem actionSGBlockAt_mem_actionStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    actionSGBlockAt S rho v r ∈ (actionStoreAt S rho v r).T := by
  set n := actionReadAt S rho v r with hn
  set st := n.st.core.toHealing with hst
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgr
  have hk : S.hc.round_of st.s = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]
    rfl
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    actionRead_invariant S rho v r
  have hpc : ParentClosed n.st.core := by
    have h := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
    rw [parentClosed_iff] at h ⊢
    exact h
  have hlc : st.live_confirmed ∈ n.st.core.T := hinv.2.1
  have hroot : Protocol.get_fg_root st.toFG ∈ n.st.core.T :=
    Proofs.NamedStoreRoots.fg_root_mem n.st hinv.1.2
  have hanchor : grades.anchor ∈ n.st.core.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem n.cache S.E S.hc st r hroot
  have hgoal : (actionStoreAt S rho v r).T = n.st.core.T := rfl
  rw [hgoal, heq]
  unfold Protocol.currentSGVote
  cases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed
      grades.clear with
  | some B =>
      exact Proofs.Records.mem_of_preceq ((parentClosed_iff n.st.core).mp hpc).2 B
        st.live_confirmed hlc (Proofs.Engine.deepest_clear_preceq hdc)
  | none =>
      cases hQ : grades.Q2 with
      | some Q =>
          exact Proofs.NamedConfirmationMembership.runtime_Q2_mem n.cache S.E S.hc
            st r Q hQ
      | none =>
          simp only []
          split
          · exact hroot
          · exact hanchor

/-- The exact action carrier was already present in the strict pre-action
store. The confirmation update changes neither the processed tree nor the
selected carrier's provenance. -/
theorem actionSGBlockAt_mem_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    actionSGBlockAt S rho v r ∈
      (rho.storeBeforeTime S v (S.a r)).T :=
  actionSGBlockAt_mem_actionStore S rho v r



/-! ## The exact remaining concentration condition -/




/-- A common carrier cone plus next-read activity supplies the complete
`CleanActionReadFor` interface. In particular, block relay and both receipt
timestamps follow from admissibility; callers do not assume them. -/
theorem cleanActionReadFor_of_actionCarriersCover_and_next_active
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V}
    (hcover : ActionCarriersCover S rho r P)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hactive : ∀ w ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (r + 1)).toFG)
    (hactive_domain : ∀ w ∈ rho.honest,
      P ∈ filteredTree (relativeG2Read S rho (r + 1) w)) :
    CleanActionReadFor S rho r P := by
  refine ⟨hpost, hcut, hactive, hactive_domain, ?_⟩
  intro w hw v hv
  have sch : ScheduleWellFormed S rho :=
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  let H := actionSGBlockAt S rho v r
  have hHsource : H ∈ (rho.storeBeforeTime S v (S.a r)).T := by
    simpa only [H] using actionSGBlockAt_mem_storeBeforeTime S rho v r
  have hPH : Block.Preceq P H := by
    simpa only [H] using hcover v hv
  have hvisible : H ∈
        (rho.storeBeforeTime S w (S.a (r + 1))).T ∧
      stampedBefore
        (rho.storeBeforeTime S w (S.a (r + 1))).timestamp_block
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) H = true := by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
        S sch v (S.a r) hHsource with
      hgen | ⟨D, i, t, hDerase, hacc, ht⟩
    · simpa only [H, hgen] using
        (Protocol.genesis_mem_and_stamp_storeBeforeTime S
          sch w (S.a (r + 1))
          (S.hc.Γ_neg1 S.E.Δ (r + 1)))
    · have hHpos : 0 < D.slot := by
        have hslot := Protocol.parent_slot_lt_of_acceptsAt_block S hacc
        rw [Proofs.NamedWire.erase_slot] at hslot
        exact Nat.zero_lt_of_lt hslot
      have hrelayRead : S.a r + S.E.Δ ≤ S.a (r + 1) :=
        le_trans (action_add_delta_le_next_Γ_neg1 S r)
          (le_of_lt (next_Γ_neg1_lt_action S r))
      have hPD : Block.Preceq P D.erase := by rw [hDerase]; exact hPH
      have hFhist :=
        finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
          S adm hrelayRead
            (by simpa only [healStoreAt] using hactive w hw) hPD
      have hrelayHor : S.a r + S.E.Δ ≤ rho.horizon :=
        le_trans (action_add_delta_le_next_Γ_neg1 S r) hcut
      have hadmit := Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hv hw hHpos hacc ht hpost rfl hrelayHor hFhist
      obtain ⟨C, hCerase, j, t', hacc', ht'⟩ := hadmit
      have hadmitNext : Protocol.AdmittedBefore S rho w H
          (S.hc.Γ_neg1 S.E.Δ (r + 1)) :=
        ⟨C, by rw [hCerase]; exact hDerase, j, t', hacc',
          lt_of_lt_of_le ht' (action_add_delta_le_next_Γ_neg1 S r)⟩
      exact Protocol.admittedBefore_mem_and_stamp_at S
        sch hadmitNext
        (le_of_lt (next_Γ_neg1_lt_action S r))
  have hvoteStamp := actionSGVote_stamp_before_next_Γ_neg1
    S adm hv hw r hpost hcut
  obtain ⟨Hn, hHnErase, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S sch hw
      (S.a (r + 1)) (by simpa only [Run.storeBeforeTime, H] using hvisible.1)
  have hfind : Block.find?
      (gradeViewAt S rho w (r + 1)).T H.root = some H := by
    apply Proofs.Optimistic.find?_eq_some_of_unique
    · simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hvisible.1
    · intro Y hY hroot
      obtain ⟨Yn, hYnErase, hYrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S sch hw
          (S.a (r + 1))
          (by simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
            Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hY)
      have hrootN : Yn.root = Hn.root :=
        (Proofs.NamedWire.erase_root Yn).symm.trans
          (((congrArg Block.root hYnErase).trans hroot).trans
            (congrArg Block.root hHnErase.symm) |>.trans (Proofs.NamedWire.erase_root Hn))
      have hYH := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
        Yn Hn hYrun hHrun Yn Hn
        (Or.inl (named_preceq_self Yn)) (Or.inr (named_preceq_self Hn)) hrootN
      rw [← hYnErase, hYH]
      exact hHnErase
  have hblockStamp : stampedBefore
      (gradeViewAt S rho w (r + 1)).timestamp_block
      (S.hc.Γ_neg1 S.E.Δ (r + 1)) H = true := by
    simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hvisible.2
  have hblock : occurrenceBefore
      ((gradeViewAt S rho w (r + 1)).timestamp_block H)
      (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
    simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
      stampedBefore_eq_occurrenceBefore, H] using hvisible.2
  have hfindAction : Block.find? (gradeViewAt S rho w (r + 1)).T
      (actionSGBlockAt S rho v r).root =
        some (actionSGBlockAt S rho v r) := by
    simpa only [H] using hfind
  constructor
  · simp only [Protocol.sg_resolution_time, actionSGVoteAt, hfindAction]
    exact occurrenceBefore_max hvoteStamp hblock
  · simp only [Protocol.head_covers, actionSGVoteAt, hfindAction]
    exact hcover v hv


end HealingSurface

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `Σ.F ∈ viable_tree(Σ)` read at the cumulative store, through the row-21
adapter — the same projection the fork-choice readers use. -/
def FinalizedViable (st : Protocol.Store V) : Prop :=
  st.F ∈ Protocol.V_tree st.toHealing.toFG

omit [Fintype V] in
/-- Membership unfolded at the adapter: the tree reads exactly four fields. -/
theorem finalizedViable_iff (st : Protocol.Store V) :
    FinalizedViable st ↔
      st.F ∈ st.T ∧ ∃ W ∈ st.T, Block.preceq st.F W = true ∧
        st.h_max - 1 ≤ (st.σ W).h := by
  simp only [FinalizedViable, Protocol.V_tree, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq, Protocol.Store.toHealing]
  constructor
  · rintro ⟨⟨hT, -⟩, W, hW, hFW, hh⟩
    exact ⟨hT, W, hW, hFW, hh⟩
  · rintro ⟨hT, W, hW, hFW, hh⟩
    exact ⟨⟨hT, Block.preceq_self _⟩, W, hW, hFW, hh⟩

omit [Fintype V] in
/-- Transport along a handler that writes none of the four fields. -/
theorem finalizedViable_of_eq {st st' : Protocol.Store V} (hT : st'.T = st.T)
    (hσ : st'.σ = st.σ) (hF : st'.F = st.F) (hmax : st'.h_max = st.h_max)
    (h : FinalizedViable st) : FinalizedViable st' := by
  rw [finalizedViable_iff, hT, hσ, hF, hmax]
  exact (finalizedViable_iff st).mp h

omit [Fintype V] in
/-- **`update_finality` keeps `Σ.F` viable** (PROTOCOL.md#the-complete-protocol). The three
premises are exactly what `on_block`'s admitted branch supplies: the incoming
state is the just-written entry of a processed block `B`, and `B` descends
`Σ.F` — the admission guard. The max branch's witness is the previous one or `B`;
the F-advance's own guard is the new root's viability, and it transfers
verbatim because the deleted recompute leaves `Σ.h_max` alone. -/
theorem finalizedViable_update_finality (st : Protocol.Store V) (σ : ChainState V)
    {B : Block V} (hB : B ∈ st.T) (hσB : st.σ B = σ)
    (hFB : Block.preceq st.F B = true)
    (h : FinalizedViable st) :
    FinalizedViable (Protocol.update_finality st σ) := by
  obtain ⟨hFT, W, hW, hFW, hh⟩ := (finalizedViable_iff st).mp h
  rw [finalizedViable_iff]
  have hwit : ∃ W' ∈ st.T, Block.preceq st.F W' = true ∧
      max st.h_max σ.h - 1 ≤ (st.σ W').h := by
    -- routed through plain-`Nat` helpers: `omega` does not look through the
    -- `Height` abbreviation at projections (row H2.1's standing note)
    have hstep1 : ∀ a b x : Nat, a - 1 ≤ x → b - 1 ≤ x → max a b - 1 ≤ x := by
      intro a b x h1 h2
      omega
    have hstep2 : ∀ a b c : Nat, a ≤ b → b - 1 ≤ c → a - 1 ≤ c := by
      intro a b c h1 h2
      omega
    have hBh : (st.σ B).h = σ.h := by rw [hσB]
    rcases Nat.le_total σ.h st.h_max with hle | hle
    · exact ⟨W, hW, hFW, hstep1 _ _ _ hh (hstep2 _ _ _ hle hh)⟩
    · refine ⟨B, hB, hFB, hstep1 _ _ _ ?_ ?_⟩
      · rw [hBh]
        exact hstep2 _ _ _ hle (Nat.sub_le _ _)
      · rw [hBh]
        exact Nat.sub_le _ _
  simp only [Protocol.update_finality]
  split_ifs with h₁ h₂ h₃
  · -- justified, finalized: the guard carries the new root's own viability
    simp only [Bool.and_eq_true, decide_eq_true_eq, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
      decide_eq_true_eq] at h₂
    exact ⟨h₂.2.1.1, h₂.2.2⟩
  · exact ⟨hFT, hwit⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
      decide_eq_true_eq] at h₃
    exact ⟨h₃.2.1.1, h₃.2.2⟩
  · exact ⟨hFT, hwit⟩


/-- **The discharge corollary.** At any store whose FG root is the finalized
block — every non-cascade store, `Σ.h_max ≠ Σ.h_j + 1` — a viable `Σ.F` is a
candidate-tree member, so the candidate tree is **nonempty** and the walk's
anchor cannot sit outside it. F5.5's "the anchor may sit outside the tree" has
exactly one surviving case now: the cascade root `Σ.J`, whose viability the
design leaves genuinely open (F5.6). -/
theorem finalizedViable_mem_filtered {st : Protocol.Store V}
    (hroot : Protocol.get_fg_root st.toHealing.toFG = st.F)
    (h : FinalizedViable st) :
    st.F ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
  refine Proofs.Records.mem_filtered_of_mem_V_tree h ?_
  rw [hroot]
  exact Block.preceq_self _
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]



/-! ## The pure final Section 7 selector -/

/-- The integrated SG root descends from the FG root for a plain healing
store. This is the pure-store form of the protocol-store lemma in
`StoreFinalityConsequences`. -/
theorem healing_get_fg_root_preceq_get_sg_root
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (Protocol.get_sg_root E hc st r) := by
  simp only [Protocol.get_sg_root, Protocol.get_sg_root_with,
    Protocol.GradeContract.current, Protocol.currentGradeRead]
  split
  · rename_i A hA
    exact Proofs.Records.fresh_anchor_root_preceq E hc st r hA
  · split
    · exact Block.preceq_self _
    · exact Protocol.ghost_preceq _ _ _ _

/-! ## The exact action store -/

/-- The exact SG block emitted by a Section 7 round action descends from the
FG root that the same action store reads. -/
theorem actionFGRoot_preceq_actionSGBlockAt
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG)
      (actionSGBlockAt S rho v r) := by
  set n := actionReadAt S rho v r with hn
  set st := n.st.core.toHealing with hst
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgr
  have hk : S.hc.round_of st.s = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]
    rfl
  have hanchor : Block.Preceq (Protocol.get_fg_root st.toFG) grades.anchor :=
    fg_root_preceq_get_sg_root_with_frame n.cache S.E S.hc st r
  have hgoal : Protocol.get_fg_root
      (actionStoreAt S rho v r).toHealing.toFG =
    Protocol.get_fg_root st.toFG := rfl
  rw [hgoal, heq]
  unfold Protocol.currentSGVote
  cases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed
      grades.clear with
  | some B =>
      have hmem := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hdc)
      exact Block.preceq_trans hanchor
        (by simpa only [Option.elim_some] using hmem.2.1)
  | none =>
      cases hQ : grades.Q2 with
      | some Q =>
          have hQfiltered : Q ∈ PhaseGrades.filteredTree n :=
            actionQ2_mem_filteredTree S rho v r (by rw [← hQ]; rfl)
          exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hQfiltered
      | none =>
          simp only []
          split
          · exact Block.preceq_self _
          · exact hanchor


/-- A common action-store FG floor is exactly the remaining order premise in
`ActionCarriersCover`. -/
theorem actionCarriersCover_of_fgRootFloor
    (S : Setup V) (rho : Run V) {r : Round} {F : Block V}
    (hfloor : ∀ v ∈ rho.honest,
      Block.Preceq F
        (Protocol.get_fg_root
          (actionStoreAt S rho v r).toHealing.toFG)) :
    ActionCarriersCover S rho r F := by
  intro v hv
  exact Block.preceq_trans (hfloor v hv)
    (actionFGRoot_preceq_actionSGBlockAt S rho v r)




/-! ## Existing finality supplies the common FG floor -/

/-- The action store and its strict pre-action store have the same FG root.
The action tick changes the clock and confirmation fields only. -/
theorem actionStoreAt_fgRoot_eq_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG =
      Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).toHealing.toFG := rfl









end HealingSurface
end Proofs
end DecoupledConsensusModel

end
