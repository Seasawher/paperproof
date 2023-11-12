import Lean
import Models
open Lean

def getHyps : MetaM (List Hypothesis):= do
  (← read).lctx.foldlM (init := []) (fun acc decl => do
    if decl.isAuxDecl || decl.isImplementationDetail then
      return acc
    let type ← Meta.ppExpr decl.type
    let value ← decl.value?.mapM (Meta.ppExpr)
    return ({
      username := decl.userName.toString,
      type := type.pretty,
      value := value.map (·.pretty),
      id := decl.fvarId.name.toString
      } : Hypothesis) ::acc)
