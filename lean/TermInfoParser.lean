import Lean
import Lean.Elab
import Models
import GetHyps

open Lean Elab

def parseTermInfo (ctx : ContextInfo) (tInfo: TermInfo):
    IO (Option TacticApplication) := ctx.runMetaM tInfo.lctx do
  if !(← Meta.isProof tInfo.expr) then
    return none

  -- Interesting elaborations:
  match tInfo.elaborator with
  -- Other elab Q → (P ∧ Q) ∧ Q ∧ P : Prop @ ⟨5, 5⟩-⟨5, 33⟩ @ Lean.Elab.Term.elabDepArrow
  | ``Lean.Elab.Term.elabFun =>
    if let some type := tInfo.expectedType? then
      let username := (← Meta.ppExpr tInfo.expr).pretty
      let e := tInfo.expr
      let goalsBefore :=
        [{
          username,
          type := (← Meta.ppExpr type).pretty,
          hyps := ← getHyps,
          id := username
        }]
      let tacticString := s!"intro {e.bindingName!}"
      let username₂ := (← Meta.ppExpr e.bindingBody!).pretty.replace "#0" e.bindingName!.toString
      let bindingDomain := ← Meta.ppExpr e.bindingDomain!
      let bodyType := ← Meta.inferType e.bindingBody!
      let newHyp := {
                  username := e.bindingName!.toString,
                  type := bindingDomain.pretty,
                  value := none,
                  id := s!"_uniq.{e.bindingName!.toString}"}
      let goalsAfter := [{
        username := username₂,
        type := (← Meta.ppExpr bodyType).pretty,
        -- Add intros
        hyps := newHyp :: (← getHyps),
        id := username₂
      }]
      dbg_trace "Goals after: {toJson goalsAfter}"
      let tacticDependsOn := []

      let tacticApp: TacticApplication :=
        {tacticString, goalsBefore, goalsAfter, tacticDependsOn}

      return some tacticApp
    else
      return none
  | ``Lean.Elab.Term.elabApp =>
    -- For app `(th (arg1 : A₁) (arg2 : A₂)) : R₁` we will create `apply Th` tactic with
    -- goalsBefore = `[R₁]` and goalsAfter = `[A₁, A₂]`
    if let some type := tInfo.expectedType? then
      let fn := tInfo.expr.getAppFn
      let args := tInfo.expr.getAppArgs
      let tacticString := s!"apply {← Meta.ppExpr fn}"
      let username := (← Meta.ppExpr tInfo.expr).pretty
      let goalsBefore :=
        [{
          username,
          type := (← Meta.ppExpr type).pretty,
          hyps := ← getHyps,
          id := username
        }]
      let goalsAfter ← args.toList.filterMapM fun arg => do
        if ← Meta.isProof arg then
          let type ← Meta.inferType arg
          let username := (← Meta.ppExpr arg).pretty
          return some {
            username,
            type := (← Meta.ppExpr type).pretty,
            hyps := ← getHyps,
            id := username
          }
        else
          return none
      let tacticDependsOn := []
      let tacticApp: TacticApplication := {
        tacticString,
        goalsBefore,
        goalsAfter,
        tacticDependsOn
      }

      -- dbg_trace "App: {toJson tacticApp}"
      return some tacticApp
    else
      dbg_trace "No expected type"
      return none
  | _ => return none
