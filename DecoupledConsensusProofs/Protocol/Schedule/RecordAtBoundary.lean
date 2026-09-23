module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.RetentionNamed
public import DecoupledConsensusProofs.Protocol.Grades.Premises
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts

@[expose] public section



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Which ticks write the stable record -/

/-- A named tick either leaves the stable record exactly as it found it, or is a
support-cutoff tick whose record is the confirmation duty's. The proposal, vote
and attestation duties never name the field, and `setClock` does not either. -/
theorem node_tick_stable_cases (S : Setup V) (w : V) (n : NamedNodeState V) (t : Time) :
    (¬ (0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t)) ∧
      (NamedNode.tick S w n t).1.st.core.latest_stable = n.st.core.latest_stable) ∨
    ((0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t)) ∧
      (NamedNode.tick S w n t).1.st.core.latest_stable =
        (Protocol.NamedDuties.update_confirmation_with
            (NamedProfile.gradeContract (confirmationReadFrom S n t).cache) S.E S.hc
            (confirmationReadFrom S n t).st (S.E.slotOf t - 1)).core.latest_stable) := by
  let gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)
  let st0 := Protocol.NamedStore.setClock S.E n.st t
  let st1 := if 0 < S.E.slotOf t ∧ t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = (S.node w).val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node w) st0).1 else st0
  let st2 := if 0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t) then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node w) st1).1 else st1
  let st3 := if 0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t) then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (S.E.slotOf t - 1) else st2
  have hout : (NamedNode.tick S w n t).1.st =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          (S.node w).awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node w) st3 n.record).1 else st3) := by
    show (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1 = _
    rw [Proofs.NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0]
    split_ifs <;> rfl
  have hlast : (NamedNode.tick S w n t).1.st.core.latest_stable =
      st3.core.latest_stable := by
    rw [hout]
    split_ifs
    · exact attest_with_stable gc S.E S.hc (S.node w) st3 n.record
    · rfl
  have h1 : st1.core.latest_stable = n.st.core.latest_stable := by
    dsimp only [st1, st0]
    split_ifs
    · exact propose_block_with_stable gc S.E S.hc S.cfg (S.node w) st0
    · rfl
  have h2 : st2.core.latest_stable = st1.core.latest_stable := by
    dsimp only [st2]
    split_ifs
    · exact named_goldfish_vote_with_stable gc S.E S.hc (S.node w) st1
    · rfl
  by_cases hcut : 0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t)
  · refine Or.inr ⟨hcut, ?_⟩
    have hprop : ¬ (0 < S.E.slotOf t ∧ t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node w).val_index) := by
      rintro ⟨-, hp, -⟩
      exact Proofs.Optimistic.support_cutoff_ne_proposal_time S.E (S.E.slotOf t) (hcut.2 ▸ hp)
    have hvote : ¬ (0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t)) := by
      rintro ⟨-, hp⟩
      exact Proofs.Optimistic.support_cutoff_ne_vote_time S.E (S.E.slotOf t) (hcut.2 ▸ hp)
    have h20 : st2 = st0 := by
      dsimp only [st2, st1]
      rw [if_neg hvote, if_neg hprop]
    have h3 : st3 = Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st0
        (S.E.slotOf t - 1) := by
      dsimp only [st3]
      rw [if_pos hcut, h20]
    rw [hlast, h3]
    rfl
  · refine Or.inl ⟨hcut, ?_⟩
    have h3 : st3 = st2 := by
      dsimp only [st3]
      rw [if_neg hcut]
    rw [hlast, h3, h2, h1]

/-- The support-cutoff form of `node_tick_stable_cases`. -/
theorem node_tick_stable_at_cutoff (S : Setup V) (w : V) (n : NamedNodeState V) (t : Time)
    (hpos : 0 < S.E.slotOf t) (hcut : t = Protocol.support_cutoff S.E (S.E.slotOf t)) :
    (NamedNode.tick S w n t).1.st.core.latest_stable =
      (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract (confirmationReadFrom S n t).cache) S.E S.hc
          (confirmationReadFrom S n t).st (S.E.slotOf t - 1)).core.latest_stable := by
  rcases node_tick_stable_cases S w n t with ⟨hno, -⟩ | ⟨-, heq⟩
  · exact absurd ⟨hpos, hcut⟩ hno
  · exact heq

/-! ## 2. The confirmation duty's stable write -/


/-- The grade root the confirmation duty writes, at one read. Addendum 34
 29: the write takes the CONTRACT's `stableRoot` at the
store's own clock round — the SAME round the anchor and `frameSGCandidate` use.
For the named runtime `stableRoot` is `frameStableRoot`: the round's frozen G2
slot clipped against finality, projected onto the FG-root-filtered tree, or the
FG root when that projection is empty ( 26). -/
abbrev dutyStableRoot (S : Setup V) (n : NamedNodeState V) : Option (Block V) :=
  (NamedProfile.gradeContract n.cache).stableRoot S.E S.hc n.st.core.toHealing
    (S.hc.round_of n.st.core.s)


/-- The write's root is the round's frozen G2 slot projected onto the candidate
tree (addendum 34 26). `frameStableRoot c E hc st r` is
the total projection of `((readFrame c st r).g2.bind id).bind (activePrefix
(get_filtered_block_tree st.toFG))`: a completed, non-empty slot writes the
active prefix, and every other case writes the FG root.

Two consequences run through the rest of this file. Every root the duty can
write is at or above the reader's FG root, which makes the CARRY obligation
hold whenever the FG root already covers the protected prefix. The BASE
obligation now has a root witness even when the projection is empty. -/
theorem dutyStableRoot_of_frame (S : Setup V) (n : NamedNodeState V) {raw : Block V}
    (h : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
      (S.hc.round_of n.st.core.s)).g2 = some (some raw)) :
    dutyStableRoot S n =
      match DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw with
      | some G => some G
      | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG) := by
  change (match ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
    (S.hc.round_of n.st.core.s)).g2.bind id).bind
      (DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) with
    | some G => some G
    | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG)) = _
  rw [h]
  cases hactive : DecoupledConsensusModel.Protocol.activePrefix
      (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw <;>
    simp [Option.bind, hactive]

/-- The projected branch of `dutyStableRoot_of_frame`. -/
theorem dutyStableRoot_of_frame_of_active (S : Setup V) (n : NamedNodeState V)
    {raw G : Block V}
    (hg2 : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
      (S.hc.round_of n.st.core.s)).g2 = some (some raw))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw = some G) :
    dutyStableRoot S n = some G := by
  rw [dutyStableRoot_of_frame S n hg2, hactive]

/-- The stable root is the active G2 candidate when that candidate exists, and
the FG root otherwise. -/
theorem dutyStableRoot_eq_activeG2 (S : Setup V) (n : NamedNodeState V) :
    dutyStableRoot S n =
      match activeG2 S n with
      | some G => some G
      | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG) := by
  rfl


/-- 29 makes the stable write total. -/
theorem dutyStableRoot_some (S : Setup V) (n : NamedNodeState V) :
    ∃ G, dutyStableRoot S n = some G := by
  rw [dutyStableRoot_eq_activeG2]
  cases h : activeG2 S n with
  | some G => exact ⟨G, rfl⟩
  | none => exact ⟨Protocol.get_fg_root n.st.core.toHealing.toFG, rfl⟩

/-- Every root the duty can write is at or above the reader's FG root: the
projection ranges over `get_filtered_block_tree`, whose members all are. -/
theorem fgRoot_preceq_dutyStableRoot (S : Setup V) (n : NamedNodeState V) {G : Block V}
    (h : dutyStableRoot S n = some G) :
    Block.Preceq (Protocol.get_fg_root n.st.core.toHealing.toFG) G := by
  change (match ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
    (S.hc.round_of n.st.core.s)).g2.bind id).bind
      (DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) with
    | some Q => some Q
    | none => some (Protocol.get_fg_root n.st.core.toHealing.toFG)) = some G at h
  cases hslot : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
      (S.hc.round_of n.st.core.s)).g2.bind id with
  | none =>
      simp only [hslot] at h
      exact Option.some_inj.mp h ▸ Block.preceq_self _
  | some raw =>
    rw [hslot] at h
    cases hactive : DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw with
    | none =>
        simp [Option.bind, hactive] at h
        exact h ▸ Block.preceq_self _
    | some Q =>
        simp [Option.bind, hactive] at h
        have hQG : Q = G := h
        subst G
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
          (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1



/-- **The CARRY obligation at one read.** Either the reader's finalized block
already covers the protected prefix — and then the record is not needed, since
`Protocol.get_stable` falls back to `F` and the finalized prefix only grows — or
every root the duty could write covers it. This is what a duty must satisfy for
the record to keep `P`; it says nothing about the write firing, and a duty that
writes nothing satisfies it vacuously.

 29 makes the duty root total. 26 
puts both the projected branch and the fallback at or above the reader's FG
root (`fgRoot_preceq_dutyStableRoot`), so a reader whose FG root already covers
`P` discharges the arm with no viability input. -/
def StableWriteAt (S : Setup V) (n : NamedNodeState V) (P : Block V) : Prop :=
  Block.Preceq P n.st.core.F ∨ ∀ G, dutyStableRoot S n = some G → Block.Preceq P G

/-- **The BASE obligation at one read.** The write has to FIRE: the duty's total
root EXISTS and covers the protected prefix. This is asked at exactly one read,
round `s + 1`'s formation confirmation, where `P` has to enter a record that
does not hold it yet. The FG-root fallback supplies the root witness when the
projection is empty. -/
def StableWriteFiresAt (S : Setup V) (n : NamedNodeState V) (P : Block V) : Prop :=
  Block.Preceq P n.st.core.F ∨ ∃ G, dutyStableRoot S n = some G ∧ Block.Preceq P G

/-- An existing covering root bounds every root the duty could write. -/
theorem stableWrite_covers (S : Setup V) (m : NamedNodeState V) {P : Block V}
    (h : ∃ G, dutyStableRoot S m = some G ∧ Block.Preceq P G) :
    ∀ G, dutyStableRoot S m = some G → Block.Preceq P G := by
  obtain ⟨G0, hG0, hPG0⟩ := h
  intro G hG
  rw [hG0] at hG
  exact Option.some_inj.mp hG ▸ hPG0


/-- **The duty write, in one statement.** `advance_confirmed` absorbs a covering
root whatever the previous record was, and a `none` root leaves the previous record
exactly as it found it. So a covering previous record and a bound on the duty's root
together survive the write, and a covering root alone establishes it.
There is no third branch: the stable write has no Goldfish eligibility test and
does not read `live_confirmed`. -/
theorem confirmation_write_stable (S : Setup V) (m : NamedNodeState V) (sl : Slot)
    {P : Block V} (hold : Block.Preceq P m.st.core.latest_stable)
    (hg2 : ∀ G, dutyStableRoot S m = some G → Block.Preceq P G) :
    Block.Preceq P
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract m.cache) S.E S.hc m.st sl).core.latest_stable := by
  show Block.Preceq P
    (match dutyStableRoot S m with
      | some G => Protocol.advance_confirmed m.st.core.latest_stable G
      | none => m.st.core.latest_stable)
  cases hq : dutyStableRoot S m with
  | none => exact hold
  | some G => exact Proofs.ConfirmationPolicy.prefix_preceq_advance_of_candidate (hg2 G hq)

/-- **The duty write that FIRES.** A root above the protected prefix is absorbed
by `advance_confirmed` whatever the previous record was, so this needs no input about
The previous record at all. -/
theorem confirmation_write_stable_establishes (S : Setup V) (m : NamedNodeState V)
    (sl : Slot) {P G : Block V} (hq : dutyStableRoot S m = some G)
    (hPG : Block.Preceq P G) :
    Block.Preceq P
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract m.cache) S.E S.hc m.st sl).core.latest_stable := by
  show Block.Preceq P
    (match dutyStableRoot S m with
      | some G => Protocol.advance_confirmed m.st.core.latest_stable G
      | none => m.st.core.latest_stable)
  rw [hq]
  exact Proofs.ConfirmationPolicy.prefix_preceq_advance_of_candidate hPG

/-! ## 3. Along the run -/

/-- **The carry along the run.** The stable write's disjunction at every
confirmation duty of the same node carries `P ⪯ F ∨ P ⪯ latest_stable` across an
index interval. No compatibility side condition is needed: deliveries and
non-cutoff ticks leave the record exactly as they found it
(`RetentionNamed`'s stable handler chain), a cutoff tick whose duty root covers
`P` keeps the record covering, and a cutoff tick whose reader has already
finalized past `P` moves the carry to the finality arm, which the finalized
prefix's monotonicity keeps forever. -/
theorem stateBefore_stable_covered (S : Setup V) (rho : NamedRun V) (w : V) {P : Block V}
    (i j : Nat) (hij : i ≤ j)
    (hold : Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.F ∨
      Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.latest_stable)
    (hcov : ∀ (k : Nat) (t : Time), i ≤ k → k < j → rho.events[k]? = some (.tick w t) →
      0 < S.E.slotOf t → t = Protocol.support_cutoff S.E (S.E.slotOf t) →
      StableWriteAt S (confirmationReadFrom S (NamedRun.stateBefore S rho k w) t) P) :
    Block.Preceq P (NamedRun.stateBefore S rho j w).st.core.F ∨
    Block.Preceq P (NamedRun.stateBefore S rho j w).st.core.latest_stable := by
  induction j, hij using Nat.le_induction with
  | base => exact hold
  | succ j hij ih =>
      have hstep := ih (fun k t hk hkj => hcov k t hk (Nat.lt_succ_of_lt hkj))
      have hFmono : Block.Preceq (NamedRun.stateBefore S rho j w).st.core.F
          (NamedRun.stateBefore S rho (j + 1) w).st.core.F :=
        Proofs.NamedRuntime.stateBefore_F_mono S rho w (Nat.le_succ j)
      rcases hstep with hF | hlat
      · exact Or.inl (Block.preceq_trans hF hFmono)
      have hgoal : Block.Preceq P (NamedRun.stateBefore S rho j w).st.core.F ∨
          Block.Preceq P (NamedRun.stateBefore S rho (j + 1) w).st.core.latest_stable := by
        cases he : rho.events[j]? with
        | none =>
            refine Or.inr ?_
            rw [Proofs.NamedRuntime.stateBefore_succ]
            simpa only [he, Option.toList_none, List.foldl_nil] using hlat
        | some e =>
            cases e with
            | deliver u o t' =>
                refine Or.inr ?_
                by_cases hu : u = w
                · have he' : rho.events[j]? = some (.deliver w o t') := by
                    rw [← hu]; exact he
                  rw [Proofs.NamedRuntime.stateBefore_deliver S rho he', node_process_stable]
                  exact hlat
                · rw [Proofs.NamedRuntime.stateBefore_other S rho he w (fun h => hu h.symm)]
                  exact hlat
            | tick u t' =>
                by_cases hu : u = w
                · have he' : rho.events[j]? = some (.tick w t') := by
                    rw [← hu]; exact he
                  rcases node_tick_stable_cases S w (NamedRun.stateBefore S rho j w) t' with
                    ⟨-, heq⟩ | ⟨⟨hpos, hcut⟩, heq⟩
                  · refine Or.inr ?_
                    rw [Proofs.NamedRuntime.stateBefore_tick S rho he', heq]
                    exact hlat
                  · rcases hcov j t' hij (Nat.lt_succ_self j) he' hpos hcut with hFr | hex
                    · exact Or.inl hFr
                    · refine Or.inr ?_
                      rw [Proofs.NamedRuntime.stateBefore_tick S rho he', heq]
                      exact confirmation_write_stable S _ _ hlat hex
                · rw [Proofs.NamedRuntime.stateBefore_other S rho he w (fun h => hu h.symm)]
                  exact Or.inr hlat
      rcases hgoal with hF | hlat'
      · exact Or.inl (Block.preceq_trans hF hFmono)
      · exact Or.inr hlat'

/-! ## 4. The boundary statement -/



private theorem rec_int_nonneg_add_two (a d : Int) (ha : 0 ≤ a) (hd : 0 < d) :
    0 ≤ a + 2 * d := by omega

private theorem rec_int_lt_of_add_le (a d b : Int) (hd : 0 < d) (h : a + d ≤ b) :
    a < b := by omega

private theorem rec_int_le_chain (a d b c e : Int) (hd : 0 < d) (h1 : a + d ≤ b) (h2 : b ≤ c)
    (h3 : c ≤ e) : a ≤ e := by omega

/-- The support cutoff of a slot is not before time zero. -/
private theorem rec_support_cutoff_nonneg (E : Env V) (sl : Slot) :
    (0 : Time) ≤ Protocol.support_cutoff E sl := by
  have hp := Proofs.Optimistic.proposal_time_nonneg E sl
  have hd := E.Δ_pos
  simp only [Protocol.support_cutoff, Protocol.proposal_time] at hp ⊢
  exact rec_int_nonneg_add_two _ _ hp hd





/-- The formation cutoff of round `s + 1` is a positive slot's support cutoff.
-/
theorem formation_cutoff_slot (S : Setup V) (s : Round) :
    0 < S.E.slotOf (formationConfirmationTime S (s + 1)) ∧
    formationConfirmationTime S (s + 1) =
      Protocol.support_cutoff S.E (S.E.slotOf (formationConfirmationTime S (s + 1))) := by
  have hslot : S.E.slotOf (formationConfirmationTime S (s + 1))
      = S.hc.opening_slot (s + 1) :=
    Proofs.Optimistic.slotOf_support_cutoff S.E (S.hc.opening_slot (s + 1))
  have hslpos : 0 < S.hc.opening_slot (s + 1) :=
    Nat.mul_pos (Nat.succ_pos s) (lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)
  refine ⟨by rw [hslot]; exact hslpos, ?_⟩
  rw [hslot]
  rfl

/-- The formation cutoff of round `s + 1` is a full delay before the boundary. -/
theorem formation_lt_boundary (S : Setup V) (s : Round) (b0 : Time)
    (hmargin : FormationMargin S s b0) : formationConfirmationTime S (s + 1) < b0 :=
  rec_int_lt_of_add_le _ _ _ S.E.Δ_pos (old_margin_of_new S s b0 hmargin)


/-- **The base obligation.** At round `s + 1`'s formation confirmation the stable
write has to FIRE, unless the reader's finalized block already covers the
protected prefix. 29 makes the contract's `stableRoot`
total: it is the projected frozen G2 root, or the FG root when the projection
is empty. The second arm therefore has an explicit root witness. -/
def FormationStableWrite (S : Setup V) (rho : NamedRun V) (s : Round) (P : Block V) :
    Prop :=
  ∀ w ∈ rho.honest, StableWriteFiresAt S (formationConfirmationRead S rho w (s + 1)) P

/-- The maintenance shape on the pre-outage segment: the stable write's own
disjunction at every honest confirmation duty from round `s + 1`'s formation
cutoff to the boundary. -/
def StableWriteCoverageBefore (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ t : Time,
    formationConfirmationTime S (s + 1) ≤ t → t < b0 →
    0 < S.E.slotOf t → t = Protocol.support_cutoff S.E (S.E.slotOf t) →
    StableWriteAt S (confirmationReadAt S rho w t) P

/-- The same shape inside the outage window. -/
def StableWriteCoverageWindow (S : Setup V) (rho : NamedRun V) (b0 cap : Time)
    (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ u : Time, b0 ≤ u → u ≤ cap → u ≤ rho.horizon →
    0 < S.E.slotOf u → u = Protocol.support_cutoff S.E (S.E.slotOf u) →
    StableWriteAt S (confirmationReadAt S rho w u) P

/-- L10 for the stable record, from the write's own coverage. `FormationMargin`
places round `s + 1`'s formation confirmation a full `Δ` before `b0`,
`tick_total` supplies the tick at that public instant, the confirmation duty
there records `P`, and the run carries it to `b0`. -/
theorem stable_record_at_boundary_of_coverage
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hwrite : FormationStableWrite S rho s P)
    (hcov : StableWriteCoverageBefore S rho b0 s P) :
    ∀ w ∈ rho.honest,
      Block.Preceq P (NamedRun.stateBeforeTime S rho b0 w).st.core.F ∨
      Block.Preceq P (NamedRun.stateBeforeTime S rho b0 w).st.core.latest_stable := by
  intro w hw
  set sl := S.hc.opening_slot (s + 1) with hsl
  set t0 := Protocol.support_cutoff S.E sl with ht0
  have hΔ := S.E.Δ_pos
  have hgap : t0 + S.E.Δ ≤ b0 := old_margin_of_new S s b0 hmargin
  have hlt : t0 < b0 := rec_int_lt_of_add_le _ _ _ hΔ hgap
  have hslot : S.E.slotOf t0 = sl := Proofs.Optimistic.slotOf_support_cutoff S.E sl
  have hslpos : 0 < sl :=
    Nat.mul_pos (Nat.succ_pos s) (lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)
  have hnn : (0 : Time) ≤ t0 := rec_support_cutoff_nonneg S.E sl
  have hhor : t0 ≤ rho.horizon := by
    obtain ⟨-, hb01, hb1⟩ := hexec.interval
    exact rec_int_le_chain _ _ _ _ _ hΔ hgap hb01 hb1
  have hpub : Execution.PublicTime S t0 :=
    (Execution.publicTime_iff S t0).mpr ⟨sl, Or.inr (Or.inr (Or.inl rfl))⟩
  obtain ⟨k, hk⟩ :=
    List.mem_iff_getElem?.mp (hexec.core.tick_total w hw t0 hpub hnn hhor)
  have hcutpos : 0 < S.E.slotOf t0 := by rw [hslot]; exact hslpos
  have hcuteq : t0 = Protocol.support_cutoff S.E (S.E.slotOf t0) := by rw [hslot]
  have hidx : ∀ (m : Nat) (t : Time), rho.events[m]? = some (.tick w t) →
      t0 ≤ t → t < b0 → 0 < S.E.slotOf t →
      t = Protocol.support_cutoff S.E (S.E.slotOf t) →
      StableWriteAt S (confirmationReadFrom S (NamedRun.stateBefore S rho m w) t) P := by
    intro m t hm hge hlt' hpos hcut
    rw [Proofs.NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup hm]
    exact hcov w hw t hge hlt' hpos hcut
  have hpre : NamedRun.stateBefore S rho k w = NamedRun.stateBeforeTime S rho t0 w :=
    Proofs.NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup hk
  have hread : formationConfirmationRead S rho w (s + 1) =
      confirmationReadFrom S (NamedRun.stateBefore S rho k w) t0 := by
    rw [hpre]
    rfl
  have hstep : Block.Preceq P (NamedRun.stateBefore S rho (k + 1) w).st.core.F ∨
      Block.Preceq P (NamedRun.stateBefore S rho (k + 1) w).st.core.latest_stable := by
    have hlat : (NamedRun.stateBefore S rho (k + 1) w).st.core.latest_stable =
        (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract (formationConfirmationRead S rho w (s + 1)).cache)
          S.E S.hc (formationConfirmationRead S rho w (s + 1)).st
          (S.E.slotOf t0 - 1)).core.latest_stable := by
      rw [Proofs.NamedRuntime.stateBefore_tick S rho hk,
        node_tick_stable_at_cutoff S w _ t0 hcutpos hcuteq, hread]
    have hFle : Block.Preceq (formationConfirmationRead S rho w (s + 1)).st.core.F
        (NamedRun.stateBefore S rho (k + 1) w).st.core.F := by
      rw [hread]
      exact Proofs.NamedRuntime.stateBefore_F_mono S rho w (Nat.le_succ k)
    rcases hwrite w hw with hFw | ⟨G, hG, hPG⟩
    · exact Or.inl (Block.preceq_trans hFw hFle)
    · refine Or.inr ?_
      rw [hlat]
      exact confirmation_write_stable_establishes S _ (S.E.slotOf t0 - 1) hG hPG
  obtain ⟨n, hn, hearly, hinside⟩ :=
    stateBeforeTime_prefix_index S rho hexec.core.sorted b0
  have hkn : k + 1 ≤ n := hinside k (.tick w t0) hk hlt
  rw [hn]
  refine stateBefore_stable_covered S rho w (k + 1) n hkn hstep ?_
  intro m t' hm hmn hev hpos hcut
  have htlt : t' < b0 := hearly m (.tick w t') hmn hev
  have htge : t0 ≤ t' := by
    have := time_le_of_index_le rho hexec.core.sorted hk hev (by omega)
    simpa only [NamedEvent.time] using this
  exact hidx m t' hev htge htlt hpos hcut

#print axioms node_tick_stable_cases
#print axioms dutyStableRoot_of_frame
#print axioms confirmation_write_stable
#print axioms confirmation_write_stable_establishes
#print axioms stateBefore_stable_covered
#print axioms stable_record_at_boundary_of_coverage

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
