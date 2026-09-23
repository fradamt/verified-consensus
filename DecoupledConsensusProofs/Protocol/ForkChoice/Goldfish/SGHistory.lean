module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Canonicality
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment

@[expose] public section

/-!
# Run history for SG heads

This file transports past honest attestation emissions into the two SG
compatibility predicates used by GST-zero canonicality. Head compatibility is
a history fact. Honest representation in the relative-SG denominator remains
an explicit delivery premise.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



omit [Fintype V] in
/-- A successful `sole_vote?` selection is a pool member attributed to the
validator selected by the call. -/
theorem sole_vote_mem_and_author
    {votes : Finset (Protocol.SGVote V)} {v : V}
    {u : Protocol.SGVote V}
    (h : Protocol.sole_vote? votes v = some u) :
    u ∈ votes ∧ u.val_index = v := by
  constructor
  · unfold Protocol.sole_vote? at h
    exact Proofs.Engine.pickUnique?_mem h
  · unfold Protocol.sole_vote? pickUnique? at h
    split at h
    · rename_i hex
      have hs := Finset.choose_spec
        (fun vote : Protocol.SGVote V => decide (vote.val_index = v) = true)
        votes hex
      rw [← Option.some.inj h]
      simpa only [decide_eq_true_eq] using hs.2
    · exact absurd h (by simp)





/-- Two projected SG votes by one honest validator in one honest-node pool
round are equal. The pool rows are named, and their bucket round comes from
the named row-bucket invariant. -/
theorem honest_sgVote_unique_stateBeforeTime
    (S : Setup V) {ρ : Run V} (adm : Admissible S ρ)
    {t : Time} {w : V} {k : Round} {v : V} (hv : v ∈ ρ.honest)
    {u z : Protocol.SGVote V}
    (hu : u ∈ (ρ.stateBeforeTime S t w).st.toHealing.sg_votes k)
    (hz : z ∈ (ρ.stateBeforeTime S t w).st.toHealing.sg_votes k)
    (huv : u.val_index = v) (hzv : z.val_index = v) : u = z := by
  change u ∈ ((ρ.stateBeforeTime S t w).st.sg_pool k).image Protocol.sgVote at hu
  change z ∈ ((ρ.stateBeforeTime S t w).st.sg_pool k).image Protocol.sgVote at hz
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hz
  have hav : a.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hau
    have hauv : a.val_index = u.val_index := by
      simpa only [Protocol.sgVote] using h
    exact hauv.trans huv
  have hbv : b.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hbz
    have hbzv : b.val_index = z.val_index := by
      simpa only [Protocol.sgVote] using h
    exact hbzv.trans hzv
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed t
  have ha' : a ∈ (ρ.stateBefore S n w).st.sg_pool k := by
    rw [← hn]
    exact ha
  have hb' : b ∈ (ρ.stateBefore S n w).st.sg_pool k := by
    rw [← hn]
    exact hb
  have hsource : ∀ {x : CombinedAttestation V},
      x ∈ (ρ.stateBefore S n w).st.sg_pool k → x.val_index = v →
        ∃ row : NamedAttestation V, x = row.erase ∧
          ∃ tx : Time,
            NamedRun.emits S ρ row.val_index (Object.attest row) tx := by
    intro x hx hxval
    obtain ⟨j, e, o, hj, hje, hproc, hcarry⟩ :=
      Proofs.Optimistic.processes_attest_of_mem_sg_pool S ρ w n k x hx
    obtain ⟨row, hrowEq, tx, hem⟩ :
        ∃ row : NamedAttestation V, x = row.erase ∧
          ∃ tx : Time, ρ.emits S row.val_index (Object.attest row) tx := by
      cases o with
      | block Bl =>
          obtain ⟨row, hrowMem, hrowEq⟩ := hcarry
          have hrowVal : row.val_index = v := by
            simpa only [hrowEq, NamedAttestation.erase] using hxval
          have hrowHon : row.val_index ∈ ρ.honest := by
            rw [hrowVal]
            exact hv
          obtain ⟨tx, -, hem⟩ :=
            adm.carried_attest w Bl e.time hproc row hrowMem hrowHon
          exact ⟨row, hrowEq, tx, hem⟩
      | gfVote voteObj => simp only [Proofs.Optimistic.CarriesRow] at hcarry
      | attest row =>
          have hrowEq : x = row.erase := hcarry
          have hrowVal : row.val_index = v := by
            simpa only [hrowEq, NamedAttestation.erase] using hxval
          have hrowHon : row.val_index ∈ ρ.honest := by
            rw [hrowVal]
            exact hv
          obtain ⟨tx, -, hem⟩ :=
            adm.unforgeable w (Object.attest row) e.time hproc
              row.val_index hrowHon rfl
          exact ⟨row, hrowEq, tx, hem⟩
    exact ⟨row, hrowEq, tx, hem⟩
  obtain ⟨a', haa, hma⟩ := hsource ha' hav
  obtain ⟨b', hbb, hmb⟩ := hsource hb' hbv
  have haRound : a.round = k :=
    (Proofs.NamedStoreBridge.sgRounds_stateBefore S ρ n w) k a
      (List.mem_toFinset.mp ha')
  have hbRound : b.round = k :=
    (Proofs.NamedStoreBridge.sgRounds_stateBefore S ρ n w) k b
      (List.mem_toFinset.mp hb')
  have ha'Round : a'.round = k := by
    have h : a'.erase.round = k := by
      rw [← haa]
      exact haRound
    simpa only [NamedAttestation.erase] using h
  have hb'Round : b'.round = k := by
    have h : b'.erase.round = k := by
      rw [← hbb]
      exact hbRound
    simpa only [NamedAttestation.erase] using h
  have ha'Val : a'.val_index = v := by
    have h : a'.erase.val_index = v := by
      rw [← haa]
      exact hav
    simpa only [NamedAttestation.erase] using h
  have hb'Val : b'.val_index = v := by
    have h : b'.erase.val_index = v := by
      rw [← hbb]
      exact hbv
    simpa only [NamedAttestation.erase] using h
  rw [ha'Val] at hma
  rw [hb'Val] at hmb
  obtain ⟨ta, hma⟩ := hma
  obtain ⟨tb, hmb⟩ := hmb
  have hab' : a' = b' :=
    Proofs.Optimistic.emits_attest_unique S adm.toNamedScheduleWellFormed hma hmb
      (by rw [ha'Round, hb'Round])
  have hErase : a'.erase = b'.erase :=
    congrArg (fun row : NamedAttestation V => row.erase) hab'
  have hab : a = b :=
    haa.trans (hErase.trans hbb.symm)
  exact hau.symm.trans ((congrArg Protocol.sgVote hab).trans hbz)



/-- Every honest-validator slice of the grade batch has at most one vote. -/
theorem roundBatch_card_le_one_stateBeforeTime
    (S : Setup V) {ρ : Run V} (adm : Admissible S ρ)
    {t : Time} {w : V} {r : Round} {v : V} (hv : v ∈ ρ.honest) :
    (Protocol.sg_votes_by
      (Protocol.round_batch (ρ.stateBeforeTime S t w).st.toHealing.gradeView r)
      v).card ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    simp [Protocol.round_batch, Protocol.sg_votes_by]
  · rw [Finset.card_le_one]
    intro u hu z hz
    obtain ⟨huBatch, huv⟩ := Finset.mem_filter.mp hu
    obtain ⟨hzBatch, hzv⟩ := Finset.mem_filter.mp hz
    apply honest_sgVote_unique_stateBeforeTime S adm hv
    · simpa only [Protocol.round_batch, hr, Protocol.HealingStore.gradeView] using huBatch
    · simpa only [Protocol.round_batch, hr, Protocol.HealingStore.gradeView] using hzBatch
    · exact huv
    · exact hzv







end Protocol
end DecoupledConsensusModel

end
