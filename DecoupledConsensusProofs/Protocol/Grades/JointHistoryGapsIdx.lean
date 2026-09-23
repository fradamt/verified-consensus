module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryB4B5Idx
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryGaps

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryGaps
open Execution Internal.NamedOutageEntry Internal.NamedJointOutage Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time
open JointHistoryB4B5
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## `ConfirmationAtTick`: the clause-(4) package for one tick index -/

/-- The clause-(4) package for the SINGLE honest tick at index `i`: whatever
`(v, r)` that tick actually is, the Goldfish confirmation recomputed by its
action read is a held run block below `C`. No universal quantification over
indices `< n` (that is `ConfirmationIdx`'s job); this is the one-shot
instance the driver hands to `fg_source_on_history_of` for the very tick
doing the FG-source computation. -/
def ConfirmationAtTick (S : Setup V) (rho : NamedRun V) (i : Nat)
    (C : NamedBlock V) : Prop :=
  ∀ (v : V) (r : Round), v ∈ rho.honest →
    rho.events[i]? = some (.tick v (S.a r)) →
    ∃ L : NamedBlock V,
      NamedRun.blockInRun S rho L ∧
      L ∈ (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.bodies ∧
      L.erase = (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.live_confirmed ∧
      NamedBlock.Preceq L C

/-! ## `GradedRootOnHistoryIdx`: the index form of `GradedRootOnHistory` -/

/-- A G2 root that an honest validator actually froze at a tick of index
`< n` is below `C`. Index form of `JointHistoryGapsTime.GradedRootOnHistory`. -/
def GradedRootOnHistoryIdx (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  ∀ (j : Nat) (v : V) (r : Round) (raw : Block V), v ∈ rho.honest →
    rho.events[j]? = some (.tick v (domain S.E S.hc r .g2)) →
    j < n →
    gradeBool S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) raw = true →
    ∃ K : NamedBlock V,
      NamedRun.blockInRun S rho K ∧ NamedBlock.Preceq K C ∧ Block.Preceq raw K.erase

/-- Index form of `JointHistoryGapsTime.graded_root_on_history`.
`hcapn` replaces the time-based `t ≤ cap`: every event with index `< n` has
time `≤ cap` (holds for free when `n` is a `boundaryIdx rho cap`). -/
theorem graded_root_on_history
    (S : Setup V) (rho : NamedRun V) (cap : Time)
    (core : NamedAdmissibleCore S rho)
    (healthy : NamedHealthyPrefixDelivery S rho cap)
    (committees : HonestCommittees S rho.honest) (hR : 3 ≤ S.hc.R)
    (hcap : cap ≤ rho.horizon)
    (windows : ∀ k, 0 < k → domain S.E S.hc k .g2 ≤ cap →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG k)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (n : Nat) (C : NamedBlock V) (hhistory : LayerAJointHistoryIdx S rho n C)
    (hcapn : ∀ i, i < n → ∀ e : NamedEvent V, rho.events[i]? = some e → e.time ≤ cap) :
    GradedRootOnHistoryIdx S rho n C := by
  intro j v r raw hv hje hjn hgb
  have hearlylt : early S.E S.hc r .g2 < domain S.E S.hc r .g2 := early_g2_lt_domain_g2 S r
  have hcapd : domain S.E S.hc r .g2 ≤ cap := by
    have h := hcapn j hjn (.tick v (domain S.E S.hc r .g2)) hje
    simpa only [NamedEvent.time] using h
  have hwindowTime : ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      S.a k + S.E.Δ ≤ early S.E S.hc r .g2 := fun k hk =>
    action_delta_le_early_g2 S (OutageInputs.window_bounds hk).2 hR
  by_cases hr : 0 < r
  · have hwin := windows r hr hcapd
    have hready : ∀ u ∈ honestAwakeWindow (fun x => (S.node x).awake) rho.honest S.hc.η_SG r,
        (readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
          (early S.E S.hc r .g2) u).Nonempty := by
      intro u hu
      obtain ⟨huHon, huAwake⟩ := Finset.mem_filter.mp hu
      obtain ⟨k, hk, hka⟩ := List.any_eq_true.mp huAwake
      have hdead := hwindowTime k hk
      have hhor : S.a k ≤ rho.horizon :=
        (le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (hdead.trans ((hearlylt.le.trans hcapd).trans hcap))
      obtain ⟨i, a, H, hie, hem, hval, har, hH, hkey⟩ :=
        awake_window_row_head S rho core.toNamedScheduleWellFormed u huHon k hka hhor
      exact JointHistoryB4B5.capture_ready_token S rho core cap healthy hR n C
        hhistory j v hv r hje hjn hcapd u huHon k hk i a H hie hem hval har hH hkey
    obtain ⟨w, hwHon, hpos⟩ := honest_positive_of_gradeBool_ready S rho.honest
      (fun x => (S.node x).awake) r
      (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F raw hgb hwin hready
    refine JointHistoryB4B5.graded_root_below_of_positive S rho core n C
      hhistory.2.1 j v hv (.tick v (domain S.E S.hc r .g2)) hje hjn r raw w hwHon
      (fun k hk => ?_) hpos
    exact ((lt_add_of_pos_right (S.a k) S.E.Δ_pos).trans_le (hwindowTime k hk)).trans hearlylt
  · exfalso
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    subst hr0
    have hempty : ∀ (u : V) (x : DecoupledConsensusModel.Protocol.Token (Option BlockId)),
        x ∉ readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
          (early S.E S.hc 0 .g2) u := by
      intro u x hx
      obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hx
      obtain ⟨hyraw, -⟩ := Finset.mem_filter.mp hy
      obtain ⟨hpool, -⟩ := Finset.mem_filter.mp hyraw
      obtain ⟨k, hk, -⟩ := Finset.mem_biUnion.mp hpool
      exact absurd (OutageInputs.window_bounds (List.mem_toFinset.mp hk)).2
        (Nat.not_lt_zero k)
    have hposfalse : (Finset.univ.filter fun u =>
        positive (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
          (early S.E S.hc 0 .g2) (late S.E S.hc 0 .g2) u raw = true) = (∅ : Finset V) := by
      refine Finset.filter_false_of_mem ?_
      intro u _
      simp only [positive, decide_eq_true_eq]
      rintro ⟨tok, htok, -⟩
      exact hempty u tok htok
    have hltw : S.E.electorate.weightOf
        (Finset.univ.filter fun u =>
          opposing (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
            (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
            (early S.E S.hc 0 .g2) (late S.E S.hc 0 .g2) u raw = true) <
        S.E.electorate.weightOf
          (Finset.univ.filter fun u =>
            positive (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
              (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
              (early S.E S.hc 0 .g2) (late S.E S.hc 0 .g2) u raw = true) := by
      simpa only [gradeBool, decide_eq_true_eq] using hgb
    rw [hposfalse] at hltw
    exact Nat.not_lt_zero _ (by simpa only [Electorate.weightOf, Finset.sum_empty] using hltw)

/-! ## The SG step, index form, conditional on the two gaps -/

/-- Index form of `JointHistoryGapsTime.fg_source_on_history_of`. `hconf`
is a one-shot `ConfirmationAtTick` at the SAME index `i` as the acting
tick (`hs`), and `hgraded` carries the single index bound `n` with `i ≤ n`. -/
theorem fg_source_on_history_of
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (i : Nat) (hconf : ConfirmationAtTick S rho i C) (hi : i ≤ n)
    (hgraded : GradedRootOnHistoryIdx S rho n C)
    (a : NamedAttestation V) (source entry : NamedBlock V)
    (ha : a.val_index ∈ rho.honest) (hs : SignedSourceAt S rho i a source entry) :
    NamedBlock.Preceq source C := by
  obtain ⟨htick, _hem, _hrow, hsource, hsel, _hentry, _herase, _hheight, _timeout, _hp⟩ := hs
  have hsourceBody : source ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := hsource
  have hsourceRun : NamedRun.blockInRun S rho source :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho ha i hsourceBody)
  unfold Protocol.fg_source_with at hsel
  cases hQ : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (actionReadFrom S (NamedRun.stateBefore S rho i a.val_index) a.round).cache)
      S.E S.hc
      (actionReadFrom S (NamedRun.stateBefore S rho i a.val_index) a.round).st.core.toHealing
      a.round with
  | none => simp only [hQ, reduceCtorEq] at hsel
  | some q =>
    simp only [hQ] at hsel
    cases hd : Protocol.deepest_clear (some q)
        (actionReadFrom S (NamedRun.stateBefore S rho i a.val_index)
          a.round).st.core.toHealing.live_confirmed
        ((NamedProfile.gradeContract
            (actionReadFrom S (NamedRun.stateBefore S rho i a.val_index) a.round).cache).read
          S.E S.hc
          (actionReadFrom S (NamedRun.stateBefore S rho i a.val_index)
            a.round).st.core.toHealing a.round).clear with
    | some B =>
      rw [hd] at hsel
      have heB : B = source.erase := Option.some.inj hsel
      have hpre : Block.Preceq source.erase
          (actionReadFrom S (NamedRun.stateBefore S rho i a.val_index)
            a.round).st.core.toHealing.live_confirmed := by
        rw [← heB]; exact Proofs.Engine.deepest_clear_preceq hd
      obtain ⟨L, hLrun, _hLbody, hLe, hLC⟩ := hconf a.val_index a.round ha htick
      refine named_preceq_trans (named_of_erase_preceq S rho core hsourceRun hLrun ?_) hLC
      rw [hLe]; exact hpre
    | none =>
      rw [hd] at hsel
      have heq : q = source.erase := Option.some.inj hsel
      obtain ⟨j, raw, hj, hjev, hfreeze, hqraw⟩ :=
        q2_capture_at_action_read S rho i a.val_index a.round hQ
      have hgb : gradeBool S.E
          (NamedRun.stateBefore S rho j a.val_index).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j a.val_index).st.core.F S.hc.η_SG a.round
          (early S.E S.hc a.round .g2) (late S.E S.hc a.round .g2) raw = true := by
        have hmem := Proofs.Engine.deepest?_mem (by simpa only [freezeRoot] using hfreeze)
        exact (Finset.mem_filter.mp hmem).2
      have hjn : j < n := lt_of_lt_of_le hj hi
      obtain ⟨K, hKrun, hKC, hrawK⟩ := hgraded j a.val_index a.round raw ha hjev hjn hgb
      have hsK : Block.Preceq source.erase K.erase :=
        Block.preceq_trans (heq ▸ hqraw) hrawK
      exact named_preceq_trans (named_of_erase_preceq S rho core hsourceRun hKrun hsK) hKC

end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryGaps

end
