module
public import DecoupledConsensusModel

@[expose] public section

/-! Pure confirmation observations on the supplied core store and grade contract.
The caller chooses the actual prepared contract; no execution is reconstructed. -/
namespace P1FrameOperations
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

def sgRoot (G : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) : Block V :=
  Protocol.get_sg_root_with G E hc st.toHealing (hc.round_of st.s)

def goldfishChoiceAt (G : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot) : Block V × Bool :=
  let early := beforeCutoff st.tau (Protocol.support_cutoff E s) (st.pool s)
  let late := beforeCutoff st.timestamp_vote (Protocol.confirmation_time E s) (st.pool s)
  let support := early.filter (fun u => Protocol.no_second_vote_in late u = true)
  let count := Protocol.voters_count E late s
  let score := Protocol.goldfish_score E st.T support support s
  let eligible := fun B => decide (count < 2 * score B)
  let H := Protocol.ghost (sgRoot G E hc st)
    (Protocol.get_filtered_block_tree st.toHealing.toFG) score eligible
  (H, eligible H)

def confirmationCandidate (G : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) : Option (Block V) :=
  let choice := goldfishChoiceAt G E hc st s
  match G.confirmationSG with
  | .optional select =>
    if choice.2 then some choice.1 else select E hc st.toHealing s

end P1FrameOperations

end
