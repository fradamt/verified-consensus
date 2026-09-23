module
public import DecoupledConsensusStatements.Instantiation
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Bridge.GenericExecution

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

private noncomputable abbrev C (S : Setup V) := Statements.Instantiation.constants S

theorem readAt_eq (S : Setup V) (rho : Run V) (g : Internal.Output V)
    (v : V) (t : Time) :
    Generic.readAt (P S) rho (fun n => g n.st.core) v t =
      Internal.readAt S rho g v t := by
  unfold Generic.readAt Internal.readAt
  change g (Generic.Run.readAt (P S) rho t v).st.core =
    g (NamedRun.readAt S rho t v).st.core
  rw [Execution.readAt_eq S rho]

theorem inBy_iff (S : Setup V) (rho : Run V) (g : Internal.Output V)
    (B : Block V) (t : Time) :
    Generic.InBy (P S) rho (fun n => g n.st.core) B t ↔
      Internal.InBy S rho g B t := by
  unfold Generic.InBy Internal.InBy
  simp only [readAt_eq]

theorem agreeFrom_iff (S : Setup V) (rho : Run V) (g : Internal.Output V)
    (t₀ : Time) :
    Generic.AgreeFrom (P S) rho (fun n => g n.st.core) t₀ ↔
      Internal.AgreeFrom S rho g t₀ := by
  unfold Generic.AgreeFrom Generic.ConsistentFrom Internal.AgreeFrom Internal.ConsistentFrom
  simp only [readAt_eq, Block.Compatible]

theorem monotoneFrom_iff (S : Setup V) (rho : Run V) (g : Internal.Output V)
    (t₀ : Time) :
    Generic.MonotoneFrom (P S) rho (fun n => g n.st.core) t₀ ↔
      Internal.MonotoneFrom S rho g t₀ := by
  unfold Generic.MonotoneFrom Internal.MonotoneFrom
  simp only [readAt_eq]

theorem safeFrom_iff (S : Setup V) (rho : Run V) (g : Internal.Output V)
    (t₀ : Time) :
    Generic.SafeFrom (P S) rho (fun n => g n.st.core) t₀ ↔
      Internal.SafeFrom S rho g t₀ := by
  constructor
  · intro h
    exact ⟨(agreeFrom_iff S rho g t₀).mp h.agree,
      (monotoneFrom_iff S rho g t₀).mp h.monotone⟩
  · intro h
    exact ⟨(agreeFrom_iff S rho g t₀).mpr h.agree,
      (monotoneFrom_iff S rho g t₀).mpr h.monotone⟩

theorem prefix_iff (S : Setup V) (rho : Run V) (g₁ g₂ : Internal.Output V) :
    Generic.Prefix (P S) rho (fun n => g₁ n.st.core) (fun n => g₂ n.st.core) ↔
      Internal.Prefix S rho g₁ g₂ := by
  unfold Generic.Prefix Internal.Prefix
  simp only [readAt_eq]

theorem accountablyConsistentFrom_iff (S : Setup V) (rho : Run V)
    (g₁ g₂ : Internal.Output V) (t₀ : Time) :
    Generic.AccountablyConsistentFrom (P S) (I S) rho
        (fun n => g₁ n.st.core) (fun n => g₂ n.st.core) t₀ ↔
      Internal.AccountablyConsistentFrom S (Statements.«instance» S) rho g₁ g₂ t₀ := by
  unfold Generic.AccountablyConsistentFrom Internal.AccountablyConsistentFrom
  simp only [readAt_eq, Block.Compatible]
  constructor
  · intro h u hu v hv t t' ht hth ht' hth'
    rcases h u hu v hv t t' ht hth ht' hth' with hcompat | hslash
    · exact Or.inl hcompat
    · right
      have hu' := congrFun (congrFun (Execution.readAt_eq S rho) t) u
      have hv' := congrFun (congrFun (Execution.readAt_eq S rho) t') v
      rw [hu', hv'] at hslash
      exact hslash
  · intro h u hu v hv t t' ht hth ht' hth'
    rcases h u hu v hv t t' ht hth ht' hth' with hcompat | hslash
    · exact Or.inl hcompat
    · right
      have hu' := congrFun (congrFun (Execution.readAt_eq S rho) t) u
      have hv' := congrFun (congrFun (Execution.readAt_eq S rho) t') v
      change HasSlashableWeightBetween S.E
        (store_attestations (Generic.Run.readAt (P S) rho t u).st.core)
        (store_attestations (Generic.Run.readAt (P S) rho t' v).st.core)
      rw [hu', hv']
      exact hslash

private theorem namedProposalAt_of_named (S : Setup V) (rho : Run V) (s : Slot)
    (B : NamedBlock V) :
    Internal.HonestProposalAt (Statements.«instance» S) rho s B →
      Generic.HonestProposalAt (I S) rho s B.erase := by
  rintro ⟨hp, hB⟩
  refine ⟨hp, ?_⟩
  change (proposedBlockAt S rho s).map NamedBlock.erase = some B.erase
  change proposedBlockAt S rho s = some B at hB
  simp [hB]

theorem honestProposalAt (S : Setup V) (rho : Run V) (s : Slot)
    (B : NamedBlock V) :
    Internal.HonestProposalAt (Statements.«instance» S) rho s B →
      Generic.HonestProposalAt (I S) rho s B.erase := by
  exact namedProposalAt_of_named S rho s B

theorem included_of_named (S : Setup V) {rho : Run V} {g : Internal.Output V}
    {t₀ d : Time}
    (h : Internal.Included S (Statements.«instance» S) rho g t₀ d) :
    Generic.IncludedFrom (P S) (I S) rho (fun n => g n.st.core) t₀ d := by
  intro s hs hp hhor
  obtain ⟨B, hB, hIn⟩ := h s hs hp hhor
  refine ⟨B.erase, (honestProposalAt S rho s B) hB, ?_⟩
  exact (inBy_iff S rho g B.erase ((I S).proposalTime s + d)).mpr hIn

theorem growth_of_named (S : Setup V) {rho : Run V} {g : Internal.Output V}
    {t₀ d : Time}
    (h : Internal.Growth S rho g t₀ d
      (Internal.honestAfter (Statements.«instance» S) rho)) :
    Generic.LiveFrom (P S) (I S) rho (fun n => g n.st.core) t₀ d := by
  intro t ht hhor
  obtain ⟨B, hprov, hstrict, hIn⟩ := h t ht hhor
  refine ⟨B.erase, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hB⟩ := hprov
    exact ⟨s, hs, (honestProposalAt S rho s B) hB⟩
  · intro v hv
    simpa only [readAt_eq] using hstrict v hv
  · exact (inBy_iff S rho g B.erase (t + d)).mpr hIn

end Proofs
end DecoupledConsensusModel

end
