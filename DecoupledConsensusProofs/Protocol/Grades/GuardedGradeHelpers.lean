module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.FGProtection
public import DecoupledConsensusProofs.Protocol.Grades.ReadyHeadReturn
public import DecoupledConsensusProofs.Protocol.Handlers.RawRelay
public import DecoupledConsensusProofs.Protocol.Store.RawSource
public import DecoupledConsensusProofs.Protocol.Handlers.HealthyLateRelay
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Protocol.Grades.OppositionGradeTransport
public import DecoupledConsensusInternal.Definitions.PhaseGrades

@[expose] public section

/-! Plumbing for the guarded G2-to-G1 producer.

Three groups: the executable/abstract grade dictionary, cutoff monotonicity of
the two retained input sets, and one root-agreement fact that lets a single
`covers` relation be used on both sides of the cap transport. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers
open Internal Execution Internal.PhaseGrades DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes)
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The grade dictionary -/

theorem weight_mono (w : V → Nat) {s u : Finset V} (hsu : s ⊆ u) :
    DecoupledConsensusModel.Protocol.weight w s ≤ DecoupledConsensusModel.Protocol.weight w u :=
  Finset.sum_le_sum_of_subset hsu

/-- The executable store grade is exactly the abstract weighted grade over the
reader's own retained token sets, with its own local head interpretation. -/
theorem storeGrade_iff (S : Setup V) (st : Protocol.NamedStore V) (r : Round)
    (p : Phase) (B : Block V) :
    storeGrade S.E S.hc st r p B = true ↔
      DecoupledConsensusModel.Protocol.grade S.E.electorate.weight
        (fun key block => localCovers st.core.toHealing.gradeView key block = true)
        (fun v => readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
          (early S.E S.hc r p) v)
        (fun v => readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
          (late S.E S.hc r p) v)
        (fun v => rawView st.core.toHealing.gradeView S.hc.η_SG r
          (late S.E S.hc r p) v) B := by
  have hs : (Finset.univ.filter fun v => positive st.core.toHealing.gradeView st.core.F
        S.hc.η_SG r (early S.E S.hc r p) (late S.E S.hc r p) v B = true) =
      DecoupledConsensusModel.Protocol.coverSupporters
        (fun key block => localCovers st.core.toHealing.gradeView key block = true)
        (fun v => readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
          (early S.E S.hc r p) v)
        (fun v => readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
          (late S.E S.hc r p) v)
        (fun v => rawView st.core.toHealing.gradeView S.hc.η_SG r
          (late S.E S.hc r p) v) B := by
    ext v
    simp only [DecoupledConsensusModel.Protocol.coverSupporters, Finset.mem_filter, Finset.mem_univ,
      true_and, positive, decide_eq_true_eq]
  have ho : (Finset.univ.filter fun v => opposing st.core.toHealing.gradeView st.core.F
        S.hc.η_SG r (early S.E S.hc r p) (late S.E S.hc r p) v B = true) =
      DecoupledConsensusModel.Protocol.opponents
        (fun key block => localCovers st.core.toHealing.gradeView key block = true)
        (fun v => readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
          (early S.E S.hc r p) v)
        (fun v => readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
          (late S.E S.hc r p) v)
        (fun v => rawView st.core.toHealing.gradeView S.hc.η_SG r
          (late S.E S.hc r p) v) B := by
    ext v
    simp only [DecoupledConsensusModel.Protocol.opponents, Finset.mem_filter, Finset.mem_univ,
      true_and, opposing, decide_eq_true_eq]
  show gradeBool S.E st.core.toHealing.gradeView st.core.F S.hc.η_SG r
      (early S.E S.hc r p) (late S.E S.hc r p) B = true ↔ _
  simp only [gradeBool, decide_eq_true_eq, hs, ho, DecoupledConsensusModel.Protocol.grade,
    DecoupledConsensusModel.Protocol.weight, Electorate.weightOf]

/-! ## Changing the head interpretation on one fixed pair of token sets -/

theorem supports_congr {Key Blk : Type*} (c c' : Key → Blk → Prop)
    {e l raw : Finset (Token Key)} {B : Blk}
    (hsub : e ⊆ l) (hiff : ∀ x ∈ l, (c x.key B ↔ c' x.key B))
    (hS : Supports c e l raw B) : Supports c' e l raw B := by
  obtain ⟨u, hu, hmax, hcover, hclean, hsweep⟩ := hS
  exact ⟨u, hu, hmax, (hiff u (hsub hu)).mp hcover, hclean,
    fun x hx hlt => (hiff x hx).mp (hsweep x hx hlt)⟩

theorem opposes_congr {Key Blk : Type*} (c c' : Key → Blk → Prop)
    {e l raw : Finset (Token Key)} {B : Blk}
    (hiff : ∀ x ∈ l, (c x.key B ↔ c' x.key B))
    (hO : Opposes c e l raw B) : Opposes c' e l raw B := by
  rcases hO with ⟨x, hx, hmax, hnot⟩ | hEq
  · exact Or.inl ⟨x, hx, hmax, fun hc => hnot ((hiff x hx).mpr hc)⟩
  · exact Or.inr hEq

/-- The weighted grade does not depend on which of two head interpretations is
used, as long as they agree on every retained late token. -/
theorem grade_congr {Key Blk : Type*} (w : V → Nat) (c c' : Key → Blk → Prop)
    {e l raw : V → Finset (Token Key)} {B : Blk}
    (hsub : ∀ v, e v ⊆ l v) (hiff : ∀ v, ∀ x ∈ l v, (c x.key B ↔ c' x.key B))
    (hg : DecoupledConsensusModel.Protocol.grade w c e l raw B) :
    DecoupledConsensusModel.Protocol.grade w c' e l raw B := by
  classical
  have hp : DecoupledConsensusModel.Protocol.coverSupporters c e l raw B ⊆
      DecoupledConsensusModel.Protocol.coverSupporters c' e l raw B := by
    intro v hv
    simp only [DecoupledConsensusModel.Protocol.coverSupporters, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv ⊢
    exact supports_congr c c' (hsub v) (hiff v) hv
  have hn : DecoupledConsensusModel.Protocol.opponents c' e l raw B ⊆
      DecoupledConsensusModel.Protocol.opponents c e l raw B := by
    intro v hv
    simp only [DecoupledConsensusModel.Protocol.opponents, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv ⊢
    exact opposes_congr c' c (fun x hx => (hiff v x hx).symm) hv
  exact lt_of_le_of_lt (weight_mono w hn) (lt_of_lt_of_le hg (weight_mono w hp))

/-! ## Cutoff monotonicity of the retained input sets -/








/-! ## Two honest readers resolve one signed root to the same body -/

private theorem named_self (H : NamedBlock V) : NamedBlock.Preceq H H := by
  cases H <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

/-- Root collision freedom over the whole run: whichever honest reader resolves
a signed root, and whenever, the resolved head is the same block. -/
theorem find_agree (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (t1 t2 : Time)
    (root : BlockId) {X Y : Block V}
    (hX : Block.find? (NamedRun.stateBeforeTime S rho t1 v).st.core.T root = some X)
    (hY : Block.find? (NamedRun.stateBeforeTime S rho t2 w).st.core.T root = some Y) :
    X = Y := by
  obtain ⟨n1, hn1, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho core.sorted t1
  obtain ⟨n2, hn2, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho core.sorted t2
  rw [hn1] at hX
  rw [hn2] at hY
  have hXroot := Proofs.HealingLemmas.find?_root hX
  have hYroot := Proofs.HealingLemmas.find?_root hY
  have hXmem := Proofs.HealingLemmas.find?_mem hX
  have hYmem := Proofs.HealingLemmas.find?_mem hY
  have hcoh1 : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBefore S rho n1 v).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n1 v).1.1.1
  have hcoh2 : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBefore S rho n2 w).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n2 w).1.1.1
  rw [hcoh1.1] at hXmem
  rw [hcoh2.1] at hYmem
  obtain ⟨Xn, hXn, hXe⟩ := Finset.mem_image.mp hXmem
  obtain ⟨Yn, hYn, hYe⟩ := Finset.mem_image.mp hYmem
  have hXscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv n1 hXn)
  have hYscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hw n2 hYn)
  have hroots : Xn.root = Yn.root := by
    rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Yn, hXe, hYe, hXroot, hYroot]
  have := core.toNamedRootCollisionFree.root_injective Xn Yn hXscope hYscope Xn Yn
    (Or.inl (named_self Xn)) (Or.inr (named_self Yn)) hroots
  rw [← hXe, ← hYe, this]

/-! ## Public phase cutoffs -/

/-- Copied from the checked raw-source module, whose version is private. -/
theorem early_g2_public (S : Setup V) (s : Round) (hs : 0 < s) :
    PublicTime S (early S.E S.hc s .g2) := by
  have hslots : 2 ≤ s * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hs)
  have hcoef : 5 ≤ 4 * (s * S.hc.R) := by
    calc
      5 ≤ 4 * 2 := by decide
      _ ≤ 4 * (s * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (s * S.hc.R) - 5, ?_⟩
  unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

/-! ## Schedule arithmetic for the two hops -/

theorem early_g2_add_delta (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 + S.E.Δ = early S.E S.hc r .g1 := by
  simp only [early, Phase.earlyOffset]
  ring

theorem early_g1_le_domain_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 ≤ domain S.E S.hc r .g1 := by
  simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _

theorem early_g1_le_late_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 ≤ late S.E S.hc r .g1 := by
  simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) S.E.Δ_pos.le) _

theorem early_g2_le_late_g2 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 ≤ late S.E S.hc r .g2 := by
  simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _

theorem domain_g2_le_domain_g1 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 ≤ domain S.E S.hc r .g1 := by
  simp only [domain, Phase.domainOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _

#print axioms storeGrade_iff
#print axioms grade_congr
#print axioms find_agree
#print axioms early_g2_public
end DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers

end
