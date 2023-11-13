export type LeanHypothesis = {
  value: null | string;
  username: string;
  type: string;
  id: string;
};

export type LeanGoal = {
  username: string;
  type: string;
  id: string;
  hyps: LeanHypothesis[];
};

export type LeanTactic = {
  tacticString: string;
  tacticDependsOn: string[];
  tacticDependsOnGoals?: LeanGoal[];
  goalsBefore: LeanGoal[];
  goalsAfter: LeanGoal[];
};

export type LeanTacticApp = {
  tacticApp: {
    t: LeanTactic;
  }
};

export type LeanHaveDecl = {
  haveDecl: {
    t: LeanTactic;
    subSteps: LeanProofTree;
  } & (
    | { version: undefined; initialGoal: string }
    | {
        version: 2;
        initialGoals: LeanGoal[];
      }
  );
};

export type LeanProofTree = (LeanTacticApp | LeanHaveDecl)[];
