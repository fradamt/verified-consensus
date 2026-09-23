module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ModelVocabulary.MajoritySG.ForkChoice
public import DecoupledConsensusProofs.Objects.Weights
public import DecoupledConsensusInternal.Execution.Assumptions

@[expose] public section

/-!
# Core honest-weight-majority lemmas

This low-level file contains the arithmetic witnesses of a strict global
honest-weight majority and the raw fact that every relative-SG supporter is
represented. It does not import the availability canonicality layer, so
threshold migrations can use it without an import cycle.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

namespace HonestWeightMajority

/-! ## Threshold and witness consequences -/

/-- A strict honest-weight majority leaves faulty weight below the finality
quorum threshold. -/
theorem faulty_lt_q
    {S : Execution.Setup V} {H : Finset V}
    (hmajority : Execution.HonestWeightMajority S H) :
    S.E.electorate.weightOf (Finset.univ \ H) < S.E.q := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold Execution.HonestWeightMajority at hmajority
  unfold Env.q Electorate.finalityThreshold
  omega


/-- Every finality quorum contains an honest validator. -/
theorem exists_honest_member_of_quorum
    {S : Execution.Setup V} {H Q : Finset V}
    (hmajority : Execution.HonestWeightMajority S H)
    (hQ : S.E.electorate.IsQuorum Q) :
    ∃ v ∈ Q, v ∈ H := by
  by_contra hnone
  push Not at hnone
  have hsub : Q ⊆ Finset.univ \ H := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hnone v hv⟩
  have hle := S.E.electorate.weightOf_mono hsub
  have hlt := faulty_lt_q hmajority
  unfold Electorate.IsQuorum at hQ
  unfold Env.q at hlt
  omega


/-! ## Raw relative-SG representation -/

omit [Fintype V] in
/-- Any validator that supplies SG support is represented in the relative-SG
denominator. Support selects a sole vote from a round in the latest window;
that same vote witnesses raw representation. -/
theorem represented_of_supports
    {pool : Round → Finset (Protocol.SGVote V)} {etaSG : Round}
    {T : Finset (Block V)} {r : Round} {D : Block V} {v : V}
    (hsupport : Protocol.supports pool etaSG T r D v = true) :
    Protocol.represented pool etaSG v r = true := by
  simp only [Protocol.supports] at hsupport
  split at hsupport
  · exact absurd hsupport (by simp)
  · rename_i u hu
    unfold Protocol.latest_support_vote at hu
    split at hu
    · exact absurd hu (by simp)
    · rename_i k hk
      have hkmem : k ∈ Protocol.latest_window etaSG r := by
        unfold Protocol.latest_support_round at hk
        rw [List.getLast?_eq_some_iff] at hk
        obtain ⟨xs, hxs⟩ := hk
        have hkfilter : k ∈ (Protocol.latest_window etaSG r).filter
            (fun round =>
              Protocol.holds_resolved_vote_by T (pool round) v) := by
          rw [hxs]
          simp
        exact (List.mem_filter.mp hkfilter).1
      have huspec : u ∈ pool k ∧ u.val_index = v := by
        unfold Protocol.sole_vote? pickUnique? at hu
        split at hu
        · rename_i hex
          have hs := Finset.choose_spec
            (fun vote : Protocol.SGVote V =>
              decide (vote.val_index = v) = true)
            (pool k) hex
          rw [← Option.some.inj hu]
          exact ⟨hs.1, by simpa only [decide_eq_true_eq] using hs.2⟩
        · exact absurd hu (by simp)
      unfold Protocol.represented
      rw [List.any_eq_true]
      refine ⟨k, hkmem, ?_⟩
      unfold Protocol.holds_vote_by Protocol.sg_votes_by
      simp only [decide_eq_true_eq]
      apply Finset.card_pos.mpr
      exact ⟨u, Finset.mem_filter.mpr huspec⟩
/-- A strict honest-weight majority leaves faulty weight below the absolute
strict-majority threshold. -/
theorem faulty_lt_m
    {S : Execution.Setup V} {H : Finset V}
    (hmajority : Execution.HonestWeightMajority S H) :
    S.E.electorate.weightOf (Finset.univ \ H) < S.E.m := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold Execution.HonestWeightMajority at hmajority
  unfold Env.m Electorate.strictMajorityThreshold
  omega

end HonestWeightMajority

end Protocol
end DecoupledConsensusModel

end
