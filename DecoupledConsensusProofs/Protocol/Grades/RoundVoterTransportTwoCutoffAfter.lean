module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransportTwoCutoff

@[expose] public section

/-!
# Post-GST round-voter transport through the two-cutoff interface

This is the cut-parametric form of the GST-zero transporter. The source action
round is after a caller-supplied post-GST base round.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingSurface (TwoCutoffDelivery)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem carrier_time_le_of_key_le_after {e f : NamedEvent V}
    (h : e.key ≤ f.key) : e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, -⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
private theorem carrier_strict_filter_eq_take_after
    (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take
        (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (carrier_time_le_of_key_le_after hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
private theorem carrier_post_index_le_strict_filter_length_after
    (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (cut : Time) {j : Nat} {e : NamedEvent V}
    (he : rho.events[j]? = some e) (ht : e.time < cut) :
    j + 1 ≤
      (rho.events.filter (fun x => decide (x.time < cut))).length := by
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake :
      (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) =
        rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < j + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hkj | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey :=
        (List.pairwise_iff_getElem.mp hsorted) k j hkLen hjLen hkj
      rw [hkGet, hjGet] at hkey
      exact (carrier_time_le_of_key_le_after hkey).trans_lt ht
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht
  have hsplit : rho.events.filter (fun x => decide (x.time < cut)) =
      (rho.events.take (j + 1)).filter
          (fun x => decide (x.time < cut)) ++
        (rho.events.drop (j + 1)).filter
          (fun x => decide (x.time < cut)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjLen)] at hlength
  omega

private theorem carrier_post_event_body_at_strict_read_after
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cut : Time) (reader : V) {j : Nat} {e : NamedEvent V}
    {H : NamedBlock V} (he : rho.events[j]? = some e)
    (ht : e.time < cut)
    (hheld : H ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies) :
    H ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies := by
  have hindex := carrier_post_index_le_strict_filter_length_after
    rho core.sorted cut he ht
  have hcarry := NamedBodyRetention.stateBefore_bodies_mono
    S rho reader hindex hheld
  unfold NamedRun.stateBeforeTime
  rw [carrier_strict_filter_eq_take_after rho core.sorted cut]
  exact hcarry

private theorem carrier_strict_read_eq_index_after
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (t : Time) :
    NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho
        (rho.events.filter (fun e => decide (e.time < t))).length :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (carrier_strict_filter_eq_take_after rho core.sorted t)

omit [DecidableEq V] [Fintype V] in
private theorem carrier_strict_lengths_mono_after
    (rho : NamedRun V) {early late : Time} (ht : early ≤ late) :
    (rho.events.filter (fun e => decide (e.time < early))).length ≤
      (rho.events.filter (fun e => decide (e.time < late))).length := by
  have hsub := List.Sublist.filter
    (fun e : NamedEvent V => decide (e.time < late))
    (List.filter_sublist
      (p := fun e : NamedEvent V => decide (e.time < early))
      (l := rho.events))
  have hs :
      (rho.events.filter (fun e => decide (e.time < early))).filter
          (fun e => decide (e.time < late)) =
        rho.events.filter (fun e => decide (e.time < early)) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hearly : e.time < early := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hearly.trans_le ht
  rw [hs] at hsub
  exact hsub.length_le

private theorem carrier_strict_body_stamp_carry_after
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (reader : V) {early late : Time} (ht : early ≤ late)
    (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho early reader).st.bodies) :
    H ∈ (NamedRun.stateBeforeTime S rho late reader).st.bodies ∧
      (NamedRun.stateBeforeTime S rho late reader).st.core.timestamp_block
          H.erase =
        (NamedRun.stateBeforeTime S rho early reader).st.core.timestamp_block
          H.erase := by
  rw [carrier_strict_read_eq_index_after S rho core early] at hH
  rw [carrier_strict_read_eq_index_after S rho core late,
    carrier_strict_read_eq_index_after S rho core early]
  exact NamedBlockStamp.stateBefore_body_stamp_mono S rho reader
    (carrier_strict_lengths_mono_after rho ht) hH

private theorem carrier_runBlock_unique_of_erase_eq_after
    {S : Setup V} {rho : NamedRun V}
    (roots : NamedRootCollisionFree S rho)
    {A B : NamedBlock V} (hA : NamedRun.blockInRun S rho A)
    (hB : NamedRun.blockInRun S rho B) (herase : A.erase = B.erase) :
    A = B :=
  roots.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A))
    (Or.inr (Proofs.NamedAncestry.named_self B)) (by
      rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

private theorem carrier_held_find_at_strict_after
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {reader : V} (hreader : reader ∈ rho.honest) (time : Time)
    (B : NamedBlock V)
    (hB : B ∈ (NamedRun.stateBeforeTime S rho time reader).st.bodies) :
    Block.find?
      (NamedRun.stateBeforeTime S rho time reader).st.core.T B.root =
        some B.erase := by
  have hco :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time reader).1.1.1
  have hBraw : B.erase ∈
      (NamedRun.stateBeforeTime S rho time reader).st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hB
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho core.sorted time
  have hBprefix : B ∈ (NamedRun.stateBefore S rho n reader).st.bodies := by
    rw [← hn]
    exact hB
  have hBscope : NamedRun.blockInRun S rho B :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hBprefix
  rw [← Proofs.NamedWire.erase_root B]
  apply Proofs.Optimistic.find?_eq_some_of_unique hBraw
  intro X hX hroot
  obtain ⟨C, hCheld, hCErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho time reader hX
  have hCprefix : C ∈ (NamedRun.stateBefore S rho n reader).st.bodies := by
    rw [← hn]
    exact hCheld
  have hCscope : NamedRun.blockInRun S rho C :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hCprefix
  have hCB : C = B := core.toNamedRootCollisionFree.root_injective
    C B hCscope hBscope C B
      (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self B)) (by
        rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root B,
          hCErase, hroot])
  rw [← hCErase, hCB]

private theorem compatible_carrier_body_at_read_after_gst_after
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (source : V) (hsource : source ∈ rho.honest)
    (reader : V) (hreader : reader ∈ rho.honest) (H : NamedBlock V)
    (sourceCut targetEarly targetRead : Time)
    (hHsource :
      H ∈ (NamedRun.stateBeforeTime S rho sourceCut source).st.bodies)
    (hDeadline : max sourceCut S.E.t_GST + S.E.Δ ≤ targetEarly)
    (hOrder : targetEarly ≤ targetRead)
    (hCut : targetEarly ≤ rho.horizon)
    (hcompat : Block.compatible H.erase
      (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F = true) :
    H ∈ (NamedRun.stateBeforeTime S rho targetRead reader).st.bodies ∧
      stampedBefore
        (NamedRun.stateBeforeTime S rho targetRead reader).st.core.timestamp_block
        targetEarly H.erase = true ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho targetRead reader).st.core.T
        H.erase.root = some H.erase := by
  have hHscope : NamedRun.blockInRun S rho H := by
    obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho core.sorted sourceCut
    rw [hn] at hHsource
    exact Proofs.Bridges.runBlock_of_stateBefore_mem S hsource hHsource
  have hEarly :
      H ∈ (NamedRun.stateBeforeTime S rho targetEarly reader).st.bodies := by
    by_cases hgen : H = NamedBlock.genesis
    · subst H
      exact (Proofs.NamedRuntime.stateBeforeTime_invariants
        S rho targetEarly reader).1.1.1.2.2.1.1
    · obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
        S rho core.sorted sourceCut
      rw [hn] at hHsource
      rcases NamedOutageProvenance.held_block_origin
          S rho n source hHsource with hgen' | ⟨i, hi, ta, hacc⟩
      · exact False.elim (hgen hgen')
      · obtain ⟨eSource, heSource, -, htSource⟩ := hacc.1.2
        have hta : ta < sourceCut := by
          simpa only [htSource] using hbefore i eSource hi heSource
        have hmax : max ta S.E.t_GST ≤ max sourceCut S.E.t_GST :=
          max_le_max hta.le (le_refl _)
        have htaDeadline : max ta S.E.t_GST + S.E.Δ ≤ targetEarly :=
          (add_le_add hmax (le_refl _)).trans hDeadline
        have htaEarly : ta < targetEarly :=
          (le_max_left ta S.E.t_GST).trans_lt
            ((lt_add_of_pos_right _ S.E.Δ_pos).trans_le htaDeadline)
        by_cases hskip :
            H ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.bodies
        · exact carrier_post_event_body_at_strict_read_after
            S rho core targetEarly reader heSource
              (by simpa only [htSource] using htaEarly) hskip
        · have hmissing : NamedReceipt.processed
              (NamedRun.stateBefore S rho (i + 1) reader).st
                (.block H) = false := by
            simpa only [NamedReceipt.processed, decide_eq_false_iff_not]
              using hskip
          have hcompatRead : Block.compatible
              (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F H.erase = true := by
            have h := hcompat
            simp only [Block.compatible, Bool.or_eq_true] at h ⊢
            exact h.symm
          have hguard := not_excludes_of_compatible_later_time S rho core.sorted
            (htaDeadline.trans hOrder) hcompatRead
          obtain ⟨td, hlo, hhi, j, hcall⟩ :=
            core.toNamedSynchrony.relay_block source hsource i H ta hacc
              reader hreader hmissing (htaDeadline.trans hCut) hguard
          obtain ⟨e, he, -, het⟩ := hcall.2
          have htdEarly : td < targetEarly := hhi.trans_le htaDeadline
          have heEarly : e.time < targetEarly := by
            simpa only [het] using htdEarly
          have heRead : e.time < targetRead := heEarly.trans_le hOrder
          have hindex := carrier_post_index_le_strict_filter_length_after
            rho core.sorted targetRead he heRead
          have hFmono := Proofs.NamedRuntime.stateBefore_F_mono S rho reader
            ((Nat.le_succ j).trans hindex)
          by_cases hheldCall :
              H ∈ (NamedRun.stateBefore S rho j reader).st.bodies
          · have hpost := NamedBodyRetention.stateBefore_bodies_mono
              S rho reader (Nat.le_succ j) hheldCall
            exact carrier_post_event_body_at_strict_read_after
              S rho core targetEarly reader he heEarly hpost
          · have hFcall : Block.Preceq
                (NamedRun.stateBefore S rho j reader).st.core.F H.erase := by
              have hfuture : Block.Preceq
                  (NamedRun.stateBefore S rho j reader).st.core.F
                  (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F := by
                simpa only [carrier_strict_read_eq_index_after
                  S rho core targetRead] using hFmono
              simp only [Block.compatible, Bool.or_eq_true] at hcompat
              rcases hcompat with hHF | hFH
              · rcases Block.preceq_linear hfuture hHF with h | h
                · exact h
                · have hFmem := Proofs.NamedStoreBridge.finalizedInTree_stateBefore
                    S rho j reader
                  have hpc := Proofs.NamedStoreBridge.parentClosed_stateBefore
                    S rho j reader
                  have hraw : H.erase ∈
                      (NamedRun.stateBefore S rho j reader).st.core.T :=
                    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
                      H.erase _ hFmem h
                  obtain ⟨K, hK, hKErase⟩ :=
                    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
                      S rho j reader hraw
                  have hKscope : NamedRun.blockInRun S rho K :=
                    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hK
                  have hKH : K = H := carrier_runBlock_unique_of_erase_eq_after
                    core.toNamedRootCollisionFree hKscope hHscope hKErase
                  subst K
                  exact False.elim (hheldCall hK)
              · exact Block.preceq_trans hfuture hFH
            have hpost :=
              NamedRelayGuards.handled_block_held_of_finalized_prefix
                S rho core.toNamedScheduleWellFormed
                  core.toNamedDeliveryWellFormed
                  core.toNamedRootCollisionFree hacc hcall hlo hFcall
            exact carrier_post_event_body_at_strict_read_after
              S rho core targetEarly reader he heEarly hpost
  have hStamp := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
    S rho core.toNamedScheduleWellFormed reader targetEarly H hEarly
  obtain ⟨hHeld, hCarry⟩ := carrier_strict_body_stamp_carry_after
    S rho core reader hOrder H hEarly
  refine ⟨hHeld, ?_, ?_⟩
  · unfold stampedBefore at hStamp ⊢
    rw [hCarry]
    exact hStamp
  · simpa only [Proofs.NamedWire.erase_root] using
      (carrier_held_find_at_strict_after S rho core hreader targetRead H hHeld)

/-- An honest action vote from any eligible expiry-window round after `base`
is an exact interpreted carrier at a later phase read. -/
theorem honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible_after
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {base : Round} (hpost : S.E.t_GST ≤ S.a base)
    (_delivery : TwoCutoffDelivery S rho q)
    (q k : Round) (hbase : base ≤ k)
    (p : Phase) (hk : k ∈ Protocol.latest_window S.hc.η_SG q)
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc q p ≤ rho.horizon)
    (hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc q p)
    {u : V} (hu : u ∈ honestRoundVoters S rho k)
    (hcompat : Block.compatible
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q p) w).st.core.F
      (Proofs.HealingSurface.actionSGBlockAt S rho u k) = true) :
    ∃ y ∈ interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q p) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q p) w).st.core.F
        S.hc.η_SG q (early S.E S.hc q p) u,
      y.round = k ∧
      y.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho u k).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q p) w).st.core.T
        (Proofs.HealingSurface.actionSGBlockAt S rho u k).root =
          some (Proofs.HealingSurface.actionSGBlockAt S rho u k) := by
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mp hu).1
  obtain ⟨a, haRound, haVal, hemit⟩ := honestRoundVoter_emits S rho hu
  have hearlyDomain : early S.E S.hc q p ≤ domain S.E S.hc q p := by
    cases p <;>
      simp only [early, domain, Phase.earlyOffset, Phase.domainOffset] <;>
      linarith [S.E.Δ_pos]
  have hactionHor : S.a k ≤ rho.horizon := by
    exact (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hdeadline.trans (hearlyDomain.trans hhor))
  have haConfirmed := honest_emitted_round_confirmed S rho core
    u huHon k hactionHor haRound hemit
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head
    S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho i u).st.bodies at hKstaged
    exact hKstaged
  have hstate := NamedActionSources.action_read_index S rho
    core.toNamedScheduleWellFormed i u k hi
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.bodies := by
    rw [← hstate]
    exact hKindex
  have hKrun : NamedRun.blockInRun S rho K :=
    held_blockInRun S rho core.toNamedScheduleWellFormed
      u huHon (S.a k) hKsource
  let H := Proofs.HealingSurface.actionSGBlockAt S rho u k
  have hHmem : H ∈ (Proofs.HealingSurface.actionStoreAt S rho u k).st.core.T :=
    Proofs.HealingSurface.actionSGBlockAt_mem_actionStore S rho u k
  have htree := (Proofs.HealingSurface.actionRead_invariant S rho u k).1.1.1
  rw [htree] at hHmem
  obtain ⟨D, hD, hDerase⟩ := Finset.mem_image.mp hHmem
  have hDsource : D ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.bodies := by
    change D ∈ (NamedRun.stateBeforeTime S rho (S.a k) u).st.bodies
    exact hD
  have hDrun : NamedRun.blockInRun S rho D :=
    held_blockInRun S rho core.toNamedScheduleWellFormed
      u huHon (S.a k) hDsource
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase,
      ← Option.some.inj (haConfirmed.symm.trans haK)]
  have hDK : D = K :=
    core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hKerased : K.erase = H := by
    rw [← hDK, hDerase]
  let target := NamedRun.stateBeforeTime S rho (domain S.E S.hc q p) w
  have hcompatK : Block.compatible K.erase target.st.core.F = true := by
    rw [hKerased]
    simpa only [target, Block.compatible, Bool.or_eq_true, or_comm]
      using hcompat
  have hgst : S.E.t_GST ≤ S.a k :=
    hpost.trans (Assembly.a_mono S hbase)
  have hmaxDeadline : max (S.a k) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc q p := by
    rw [max_eq_left hgst]
    exact hdeadline
  obtain ⟨_, hstamp, hfind⟩ :=
    compatible_carrier_body_at_read_after_gst_after S rho core
      u huHon w hw K (S.a k) (early S.E S.hc q p)
      (domain S.E S.hc q p) hKsource hmaxDeadline
      hearlyDomain (hearlyDomain.trans hhor) hcompatK
  have hem : NamedRun.emits S rho a.val_index (.attest a)
      (S.a a.round) := by
    simpa only [haVal, haRound] using hemit
  have hvalHon : a.val_index ∈ rho.honest := by
    simpa only [haVal] using huHon
  let healthy := healthyWindowDelivery_after_gst S rho core
  obtain ⟨td, hlo, hhi, j, hcall⟩ := healthy.broadcast
    a.val_index hvalHon (.attest a) (S.a a.round) hem w hw
      (by simpa only [haRound] using hgst)
      (by simpa only [haRound] using
        hdeadline.trans (hearlyDomain.trans hhor)) rfl
  have hrow := Proofs.NamedSGArrival.honest_row_after_call S rho
    core.toNamedScheduleWellFormed core.toNamedUnforgeable
    hvalHon hem hcall hlo hhi
  obtain ⟨e, he, _, het⟩ := hcall.2
  obtain ⟨_, stamp, hstampBound, hstampEvent⟩ :=
    Proofs.NamedSGArrival.held_row_own_and_stamp_at_event S rho
      core.toNamedScheduleWellFormed he w a.round a hrow
  have htdEarly : td < early S.E S.hc q p := by
    exact hhi.trans_le (by simpa only [haRound] using hdeadline)
  have heEarly : e.time < early S.E S.hc q p := by
    simpa only [het] using htdEarly
  have heCut : e.time < domain S.E S.hc q p :=
    heEarly.trans_le hearlyDomain
  let n := (rho.events.filter (fun e => decide
    (e.time < domain S.E S.hc q p))).length
  have hread : NamedRun.stateBeforeTime S rho (domain S.E S.hc q p) =
      NamedRun.stateBefore S rho n :=
    Proofs.Optimistic.stateBeforeTime_eq_take S
      core.toNamedScheduleWellFormed _
  have hjn : j < n := by
    by_contra hnot
    have hnj : n ≤ j := Nat.le_of_not_gt hnot
    have hle := Proofs.Optimistic.le_time_of_index_ge S
      core.toNamedScheduleWellFormed
      (t := domain S.E S.hc q p) (j := j) (e := e) hnj he
    exact (not_le_of_gt heCut) hle
  have hrowN := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho w
    (Nat.succ_le_of_lt hjn) hrow
  have hrowCut : a ∈ target.st.sg_rows a.round := by
    dsimp only [target]
    rw [hread]
    exact hrowN.1
  have hstampCut : target.st.core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (stamp : Stamp) := by
    dsimp only [target]
    rw [hread]
    exact hrowN.2.trans hstampEvent
  have hoccur : occurrenceBefore
      (target.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (early S.E S.hc q p) = true := by
    simp only [hstampCut, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt heEarly)
  have hcoh :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (domain S.E S.hc q p) w).1.1.1
  have hpool := NamedAdmission.pool_view_mem target.st hcoh.2.2.2.1
    a hrowCut
  have hsg : Protocol.sgVote a.erase ∈
      target.st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  have hraw : Protocol.sgVote a.erase ∈ rawInputs
      target.st.core.toHealing.gradeView S.hc.η_SG q
        (early S.E S.hc q p) u := by
    simp only [rawInputs, Finset.mem_filter]
    refine ⟨Finset.mem_biUnion.mpr ⟨a.round, List.mem_toFinset.mpr ?_, hsg⟩,
      ?_, hoccur⟩
    · simpa only [haRound] using hk
    · rw [sgVote_val, haVal]
  have hconf : (Protocol.sgVote a.erase).confirmed = some K.erase.root := by
    rw [sgVote_confirmed, haK, Proofs.NamedWire.erase_root]
  have hready : bodyReady target.st.core.toHealing.gradeView
      target.st.core.F (early S.E S.hc q p)
      (Protocol.sgVote a.erase) = true := by
    simp only [bodyReady, hconf]
    change (match Block.find? target.st.core.T K.erase.root with
      | none => false
      | some head => stampedBefore target.st.core.timestamp_block
          (early S.E S.hc q p) head && Block.compatible head target.st.core.F) = true
    rw [hfind, Bool.and_eq_true]
    exact ⟨hstamp, hcompatK⟩
  refine ⟨Protocol.sgVote a.erase,
    Finset.mem_filter.mpr ⟨hraw, hready⟩, ?_, ?_, ?_⟩
  · simpa only [sgVote_round, haRound]
  · rw [sgVote_confirmed, haConfirmed]
  · simpa only [target, hKerased, Proofs.NamedWire.erase_root] using hfind

#print axioms honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible_after

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
