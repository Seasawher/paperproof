import Lean
import Lean.Meta.Basic
open Lean Elab Server

structure Hypothesis where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  deriving Inhabited, ToJson, FromJson

structure GoalInfo where
  username : String
  type : String
  hyps : List Hypothesis
  -- unique identifier for the goal, mvarId
  id : String
  deriving Inhabited, ToJson, FromJson

instance : BEq GoalInfo where
  beq g1 g2 := g1.id == g2.id

instance : Hashable GoalInfo where
  hash g := hash g.id

structure TacticApplication where
  tacticString : String
  goalsBefore : List GoalInfo
  goalsAfter : List GoalInfo
  tacticDependsOn : List String
  deriving Inhabited, ToJson, FromJson

inductive ProofStep :=
  | tacticApp (t : TacticApplication)
  | haveDecl (t: TacticApplication)
    (initialGoals: List GoalInfo)
    (subSteps : List ProofStep)
  deriving Inhabited, ToJson, FromJson

def stepGoalsAfter (step : ProofStep) : List GoalInfo := match step with
  | .tacticApp t => t.goalsAfter
  | .haveDecl t _ _ => t.goalsAfter

def stepGoalsBefore (step : ProofStep) : List GoalInfo := match step with
  | .tacticApp t => t.goalsBefore
  | .haveDecl t _ _ => t.goalsBefore

def noInEdgeGoals (allGoals : HashSet GoalInfo) (steps : List ProofStep) : HashSet GoalInfo :=
  -- Some of the orphaned goals might be matched by tactics in sibling subtrees, e.g. for tacticSeq.
  (steps.bind stepGoalsAfter).foldl HashSet.erase allGoals

/-
  Instead of doing parsing of what user wrote (it wouldn't work for linarith etc),
  let's do the following.
  We have assigned something to our goal in mctxAfter.
  All the fvars used in these assignments are what was actually used instead of what was in syntax.
-/
def findHypsUsedByTactic (goalId: MVarId) (goalDecl : MetavarDecl) (mctxAfter : MetavarContext) : MetaM (List String) := do
  let some expr := mctxAfter.eAssignment.find? goalId
    | return []

  -- Need to instantiate it to get all fvars
  let fullExpr ← instantiateExprMVars expr |>.run
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  let fvars := fvarIds.filterMap goalDecl.lctx.find?
  let proofFvars ← fvars.filterM (Meta.isProof ·.toExpr)
  -- let pretty := proofFvars.map (fun x => x.userName)
  -- dbg_trace s!"Used {pretty}"
  return proofFvars.map (fun x => x.fvarId.name.toString) |>.toList

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

-- Returns GoalInfo about unassigned goals from the provided list of goals
def getGoals (printCtx: ContextInfo) (goals : List MVarId) (mctx : MetavarContext) : RequestM (List GoalInfo) := do
  goals.filterMapM fun id => do
    let some decl := mctx.findDecl? id
      | return none
    if mctx.eAssignment.contains id ||
       mctx.dAssignment.contains id then
      return none
    -- to get tombstones in name ✝ for unreachable hypothesis
    let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
    let ppContext := printCtx.toPPContext lctx
    let hyps ← ppContext.runMetaM getHyps
    return some ⟨ decl.userName.toString, (← ppExprWithInfos ppContext decl.type).fmt.pretty, hyps, id.name.toString ⟩

structure Result where
  steps : List ProofStep
  allGoals : HashSet GoalInfo

def getGoalsChange (ctx : ContextInfo) (tInfo : TacticInfo) : RequestM (List GoalInfo × List GoalInfo) := do
  -- We want to filter out `focus` like tactics which don't do any assignments
  -- therefore we check all goals on whether they were assigned during the tactic
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  -- For printing purposes we always need to use the latest mctx assignments. For example in
  -- have h := by calc
  --  3 ≤ 4 := by trivial
  --  4 ≤ 5 := by trivial
  -- at mctxBefore type of `h` is `?m.260`, but by the time calc is elaborated at mctxAfter
  -- it's known to be `3 ≤ 5`
  let printCtx := {ctx with mctx := tInfo.mctxAfter}
  let goalsBefore ← getGoals printCtx goalMVars tInfo.mctxBefore
  let goalsAfter ← getGoals printCtx goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
  return ⟨ goalsBefore.filter (!commonGoals.contains ·), goalsAfter.filter (!commonGoals.contains ·) ⟩

partial def BetterParser (context: Option ContextInfo) (infoTree : InfoTree) : RequestM Result :=
  match context, infoTree with
  | some (ctx : ContextInfo), .node i cs => do
    let some ctx := i.updateContext? ctx
      | panic! "unexpected context node"
    let res ← cs.toList.mapM (BetterParser ctx)
    let steps := res.map (fun r => r.steps) |>.join
    let allSubGoals := HashSet.empty.insertMany $ res.bind (·.allGoals.toList)
    if let .ofTacticInfo tInfo := i then
      -- shortcut if it's not a tactic user wrote
      -- \n trim to avoid empty lines/comments until next tactic,
      -- especially at the end of theorem it will capture comment for the next one
      let some tacticString := tInfo.stx.getSubstring?.map
             (·.toString |>.splitOn "\n" |>.head!.trim)
        | return {steps, allGoals := allSubGoals}

      let (goalsBefore, goalsAfter) ← getGoalsChange ctx tInfo
      let allGoals := allSubGoals.insertMany $ goalsBefore ++ goalsAfter
      -- Tactic doesn't change any goals, we shouldn't add it as a proof step.
      -- For example a tactic like `done` which ensures there are no unsolved goals,
      -- or `focus` which only leaves one goal, however has no information for the tactic tree
      -- Note: tactic like `have` changes the goal as it adds something to the context
      if goalsBefore.isEmpty then
        return {steps, allGoals}

      let some mainGoalId := tInfo.goalsBefore.head?
        | return {steps, allGoals}
      let some mainGoalDecl := tInfo.mctxBefore.findDecl? mainGoalId
        | return {steps, allGoals}

      let tacticDependsOn ←
        ctx.runMetaM mainGoalDecl.lctx
          (findHypsUsedByTactic mainGoalId mainGoalDecl tInfo.mctxAfter)
      let tacticApp: TacticApplication := {
        tacticString,
        goalsBefore,
        goalsAfter,
        tacticDependsOn
      }

      -- It's a tactic combinator
      match tInfo.stx with
      | `(tactic| have $_:haveDecl) =>
        -- Something like `have p : a = a := rfl`
        if steps.isEmpty then
          return {steps := [.tacticApp tacticApp],
                  allGoals}

        let goals := (goalsBefore ++ goalsAfter).foldl HashSet.erase (noInEdgeGoals allGoals steps)
        -- Important for have := calc for example, e.g. calc 3 < 4 ... 4 < 5 ...
        let sortedGoals := goals.toArray.insertionSort (·.id < ·.id)
        -- TODO: have ⟨ p, q ⟩ : (3 = 3) ∧ (4 = 4) := ⟨ by rfl, by rfl ⟩ isn't supported yet
        return {steps := [.haveDecl tacticApp sortedGoals.toList steps],
                allGoals := HashSet.empty.insertMany (goalsBefore ++ goalsAfter)}
      | `(tactic| rw [$_,*] $(_)?)
      | `(tactic| rewrite [$_,*] $(_)?) =>
        let prettify (tStr : String) :=
          let res := tStr.trim.dropRightWhile (· == ',')
          -- rw puts final rfl on the "]" token
          if res == "]" then "rfl" else res
        return {steps := steps.map fun a =>
                  match a with
                  | .tacticApp a => .tacticApp { a with tacticString := s!"rw [{prettify a.tacticString}]" }
                  | x => x,
                allGoals}
      | _ =>
        -- Don't add anything new if we already handled it in subtree.
        if steps.map stepGoalsBefore |>.elem goalsBefore then
          return {steps, allGoals}
        -- It uses allSubGoals instead of allGoals to make tactics like `.` which focus [1, 2, 3] -> [1] goals work.
        -- TODO: Maybe we should just ignore tactics which goalsAfter is a subset of goalsBefore?
        -- But we will need to find a way to understand if tactic actually closed the goal, like `exact ...` and [1, 2] -> [2],
        -- or just focused it `.` and [1, 2] -> [1].
        let orphanedGoals := goalsBefore.foldl HashSet.erase (noInEdgeGoals allSubGoals steps)
        return {steps := .tacticApp {tacticApp with goalsAfter := goalsAfter ++ orphanedGoals.toList} :: steps,
                allGoals}
    else if let .ofTermInfo tInfo := i then
      -- Interesting elaborations:
      match tInfo.elaborator with
      -- Other elab Q → (P ∧ Q) ∧ Q ∧ P : Prop @ ⟨5, 5⟩-⟨5, 33⟩ @ Lean.Elab.Term.elabDepArrow
      | ``Lean.Elab.Term.elabFun =>
        let newStep? ← ctx.runMetaM tInfo.lctx do
          if !(← Meta.isProof tInfo.expr) then
            return none
          if let some type := tInfo.expectedType? then
            let username := (← Meta.ppExpr tInfo.expr).pretty
            let intros := type.getForallBinderNames
            let tacticString := s!"intros {intros}"
            dbg_trace "Dep arrow {tInfo.expr}"
            let goalsBefore :=
              [{
                username,
                type := (← Meta.ppExpr type).pretty,
                hyps := ← getHyps,
                id := username
              }]
            let bodyType := type.getForallBody
            let username₂ := (← Meta.ppExpr bodyType).pretty
            let goalsAfter := [{
              username := username₂,
              type := (← Meta.ppExpr bodyType).pretty,
              -- Add intros
              hyps := ← getHyps,
              id := username₂
            }]
            let tacticDependsOn := []

            let tacticApp: TacticApplication :=
              {tacticString, goalsBefore, goalsAfter, tacticDependsOn}

            return some tacticApp
          else
            return none

        if let some newStep := newStep? then
          return { steps := .tacticApp newStep :: steps, allGoals := allSubGoals }
        else
          return { steps, allGoals := allSubGoals }

      | ``Lean.Elab.Term.elabApp =>
        -- For app `(th (arg1 : A₁) (arg2 : A₂)) : R₁` we will create `apply Th` tactic with
        -- goalsBefore = `[R₁]` and goalsAfter = `[A₁, A₂]`
        if let some type := tInfo.expectedType? then
          let newStep? ← ctx.runMetaM tInfo.lctx do
            if (← Meta.isProof tInfo.expr) then
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
              return none

          if let some newStep := newStep? then
            return { steps := .tacticApp newStep :: steps, allGoals := allSubGoals }
          else
            return { steps, allGoals := allSubGoals }
        else
          dbg_trace "No expected type"
      | _ =>
        -- dbg_trace "Other elab {← tInfo.format ctx}"
        return { steps, allGoals := allSubGoals}
      --  { left := p, right := q } : P ∧ Q @ ⟨5, 2⟩†-⟨5, 8⟩† @ Lean.Elab.Term.elabApp
      -- Abstraction?
      return { steps, allGoals := allSubGoals}
    else
      return { steps, allGoals := allSubGoals}
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => BetterParser ctx t
  | _, .hole .. => pure {steps := [], allGoals := .empty}
