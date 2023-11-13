import Lean
import BetterParser
import CheckIfUserIsStillTyping

open Lean Server RequestM

structure InputParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

inductive LegacyStepWrapping :=
  | tacticApp (t : TacticApplication)
  deriving Inhabited, ToJson, FromJson

structure OutputParams where
  steps : List LegacyStepWrapping
  deriving Inhabited, FromJson, ToJson

@[server_rpc_method]
def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    checkIfUserIsStillTyping snap params.pos

    let parsedTree ← BetterParser none snap.infoTree
    -- This happens when we hover over something other than a theorem
    if (parsedTree.steps.length == 0) then
      throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
    return {
      steps := parsedTree.steps.map fun t => .tacticApp t
    }
