module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Execution.ReceiptCalls
public import DecoupledConsensusProofs.Execution.NetworkBindings

@[expose] public section

/-! Original full-row provenance. No remote open or source/P
compatibility is claimed. The H0 invariant revision is separate and held for
architecture review. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageProvenance
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem ancestor_body_mem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · exact ih (hpc.2 _ hB) hparent

private theorem block_accepts_processes (S : Setup V) (rho : NamedRun V)
    {i : Nat} {receiver : V} {B : NamedBlock V} {t : Time}
    (h : NamedRun.acceptsAt S rho i receiver (.block B) t) :
    NamedRun.processes S rho receiver (.block B) t := by
  obtain ⟨hcall, e, he, _, het⟩ := h.1
  change NamedRun.processesAtIndex S rho i receiver (.block B) at hcall
  rcases hcall with ⟨time, hi, hem⟩ | ⟨time, hi⟩
  · have heq : NamedEvent.tick receiver time = e := Option.some.inj (hi.symm.trans he)
    have ht : time = t := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
    subst time
    exact Or.inl ⟨i, hi, hem⟩
  · have heq : NamedEvent.deliver receiver (.block B) time = e :=
      Option.some.inj (hi.symm.trans he)
    have ht : time = t := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
    subst time
    exact Or.inr ⟨i, hi⟩

theorem emitted_same_round_unique (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    {v : V} {a b : NamedAttestation V} {ta tb : Time}
    (ha : NamedRun.emits S rho v (.attest a) ta)
    (hb : NamedRun.emits S rho v (.attest b) tb)
    (hr : a.round = b.round) : a = b := by
  obtain ⟨i, hi, _, hrowi, _, _, hti, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho ha
  obtain ⟨j, hj, _, hrowj, _, _, htj, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hb
  have htt : ta = tb := hti.trans ((congrArg S.a hr).trans htj.symm)
  obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
  have hij : i = j := (List.Nodup.getElem_inj_iff sch.nodup).mp
    (by rw [hiGet, hjGet, htt])
  subst j
  rw [hr] at hrowi
  exact hrowi.symm.trans hrowj

theorem held_block_origin (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    {B : NamedBlock V} (hB : B ∈ (NamedRun.stateBefore S rho i v).st.bodies) :
    B = NamedBlock.genesis ∨
      ∃ j : Nat, j < i ∧ ∃ t : Time, NamedRun.acceptsAt S rho j v (.block B) t := by
  revert hB
  induction i with
  | zero =>
    intro hB
    left
    simpa only [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init,
      Execution.NamedNode.initial, Protocol.NamedStore.initial,
      Finset.mem_singleton] using hB
  | succ i ih =>
    intro hB
    by_cases hpre : B ∈ (NamedRun.stateBefore S rho i v).st.bodies
    · rcases ih hpre with hgen | ⟨j, hj, t, hacc⟩
      · exact Or.inl hgen
      · exact Or.inr ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i), t, hacc⟩
    · obtain ⟨t, hacc⟩ := Proofs.NamedReceiptCalls.new_block_accepts S rho i v B hpre hB
      exact Or.inr ⟨i, Nat.lt_succ_self i, t, hacc⟩

theorem held_row_origin (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    {a : NamedAttestation V} (ha : a ∈ (NamedRun.stateBefore S rho i v).st.sg_rows a.round) :
    ∃ j : Nat, j < i ∧ ∃ t : Time, NamedRun.acceptsAt S rho j v (.attest a) t := by
  revert ha
  induction i with
  | zero =>
    intro ha
    simp only [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init,
      Execution.NamedNode.initial, Protocol.NamedStore.initial,
      List.not_mem_nil] at ha
  | succ i ih =>
    intro ha
    by_cases hpre : a ∈ (NamedRun.stateBefore S rho i v).st.sg_rows a.round
    · obtain ⟨j, hj, t, hacc⟩ := ih hpre
      exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i), t, hacc⟩
    · obtain ⟨t, hacc⟩ := Proofs.NamedReceiptCalls.new_attestation_accepts S rho i v a hpre ha
      exact ⟨i, Nat.lt_succ_self i, t, hacc⟩

theorem honest_carried_row_emission (S : Setup V) (rho : NamedRun V)
    (auth : NamedUnforgeable S rho)
    {receiver : V} {B : NamedBlock V} {a : NamedAttestation V} {t : Time}
    (hB : NamedRun.processes S rho receiver (.block B) t)
    (ha : a ∈ B.attestations) (hHon : a.val_index ∈ rho.honest) :
    S.a a.round ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
  obtain ⟨sent, hsend, hem⟩ := auth.carried_attest receiver B t hB a ha hHon
  obtain ⟨_, _, _, _, _, _, htime, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  subst sent
  exact ⟨hsend, hem⟩

theorem honest_held_row_emission (S : Setup V) (rho : NamedRun V)
    (auth : NamedUnforgeable S rho) (i : Nat) (receiver : V)
    {a : NamedAttestation V} (ha : a ∈ (NamedRun.stateBefore S rho i receiver).st.sg_rows a.round)
    (hHon : a.val_index ∈ rho.honest) :
    ∃ j : Nat, j < i ∧ ∃ t : Time,
      NamedRun.acceptsAt S rho j receiver (.attest a) t ∧
      S.a a.round ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
  obtain ⟨j, hj, t, hacc⟩ := held_row_origin S rho i receiver ha
  obtain ⟨sent, hsend, hem⟩ := NamedNetworkBindings.actual_handles_authenticated
    S rho auth hacc.1 hHon rfl
  obtain ⟨_, _, _, _, _, _, htime, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  subst sent
  exact ⟨j, hj, t, hacc, hsend, hem⟩

theorem honest_held_ancestor_row_emission (S : Setup V) (rho : NamedRun V)
    (auth : NamedUnforgeable S rho) (i : Nat) (receiver : V)
    {B A : NamedBlock V} {a : NamedAttestation V}
    (hB : B ∈ (NamedRun.stateBefore S rho i receiver).st.bodies)
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations)
    (hHon : a.val_index ∈ rho.honest) :
    ∃ j : Nat, j < i ∧ ∃ t : Time,
      NamedRun.acceptsAt S rho j receiver (.block A) t ∧
      S.a a.round ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBefore S rho i receiver).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho i receiver).1.1.1
  have hA := ancestor_body_mem hcoh.2.2.1 hB hAB
  rcases held_block_origin S rho i receiver hA with hgen | ⟨j, hj, t, hacc⟩
  · subst A
    simp only [NamedBlock.attestations, List.not_mem_nil] at ha
  · obtain ⟨hsend, hem⟩ := honest_carried_row_emission S rho auth
      (block_accepts_processes S rho hacc) ha hHon
    exact ⟨j, hj, t, hacc, hsend, hem⟩

theorem honest_held_ancestor_row_before_action (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (reader : V) (r : Round) {B A : NamedBlock V} {a : NamedAttestation V}
    (hB : B ∈ (NamedRun.stateBeforeTime S rho (S.a r) reader).st.bodies)
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations)
    (hHon : a.val_index ∈ rho.honest) :
    a.round < r ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
  obtain ⟨i, hread, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted (S.a r)
  rw [hread] at hB
  obtain ⟨j, hj, t, hacc, hsend, hem⟩ :=
    honest_held_ancestor_row_emission S rho auth i reader hB hAB ha hHon
  obtain ⟨e, he, _, het⟩ := hacc.1.2
  have ht : t < S.a r := by simpa only [het] using hbefore j e hj he
  have hlt : S.a a.round < S.a r := lt_of_le_of_lt hsend ht
  refine ⟨?_, hem⟩
  by_contra hnot
  exact (not_le_of_gt hlt) (Assembly.a_mono S (Nat.le_of_not_gt hnot))

#print axioms emitted_same_round_unique
#print axioms held_block_origin
#print axioms held_row_origin
#print axioms honest_carried_row_emission
#print axioms honest_held_row_emission
#print axioms honest_held_ancestor_row_emission
#print axioms honest_held_ancestor_row_before_action
end DecoupledConsensusModel.Proofs.NamedOutageProvenance

end
