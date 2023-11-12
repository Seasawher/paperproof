import Lean
open Lean

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

structure Result where
  steps : List ProofStep
  allGoals : HashSet GoalInfo
