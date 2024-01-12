
import Mathlib.Tactic
import Mathlib.Data.Nat.Parity
import Lean.Elab.Tactic

lemma Even.zero : Even 0 := by decide

lemma  Even.add_two : Even n → Even (n+2) :=
  by
  intro e
  apply Even.add
  exact e
  decide

example : Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
  repeat' apply And.intro
  repeat'
    first
    | apply Even.add_two
    | apply Even.zero
  repeat' sorry


theorem all_goals_try_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
  repeat' apply And.intro
  all_goals try apply Even.add_two
  repeat' sorry


theorem any_goals_solve_repeat_first_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
  repeat' apply And.intro
  any_goals
    solve
      | repeat'
          first
          | apply Even.add_two
          | apply Even.zero


macro "intro_and_even" : tactic =>
`(tactic| (repeat' apply And.intro ; all_goals try apply Even.add_two ; repeat' sorry))

example : Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
  intro_and_even
  sorry

open Lean Elab Lean.Elab.Tactic Meta Expr Parser

elab "trace_goals" : tactic =>
  do
  logInfo m!"Lean version {Lean.versionString}"
  logInfo "All goals:"
  let goals ← getUnsolvedGoals
  logInfo m!"{goals}"
  match goals with
  | [] => return ()
  | _ :: _ =>
    logInfo "First goal’s target:"
    let target ← getMainTarget
    logInfo m!"{target}"
    return ()


example : Even 4 ∧Even 6 :=
  by
  constructor
  decide
  trace_goals
  repeat' sorry


def hypothesis : TacticM Unit :=
  withMainContext
  (do
    let target ← getMainTarget
    let lctx ← getLCtx
    for ldecl in lctx do
      if ! LocalDecl.isImplementationDetail ldecl then
        let eq ← isDefEq (LocalDecl.type ldecl) target
        if eq then
          let goal ← getMainGoal
          MVarId.assign goal (LocalDecl.toExpr ldecl)
          return ()
    failure)

elab "hypothesis" : tactic =>
  hypothesis


example (n : Nat) (h : Even n) : Even n :=
  by
  hypothesis


partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext
    (do
      let target ← getMainTarget
      let P ← inferType hP
      let eq ← isDefEq P target
      if eq
      then
        let goal ← getMainGoal
        MVarId.assign goal hP
        return true
      else
        match Expr.and? P with
        | Option.none => return false
        | Option.some (Q, R) =>
            let hQ ← mkAppM ``And.left #[hP]
            let success ← destructAndExpr hQ
            if success
            then
              return true
            else
              let hR ← mkAppM ``And.right #[hP]
              destructAndExpr hR)


def destructAnd (name : Name) : TacticM Unit :=
  withMainContext
  (do
    let h ← getFVarFromUserName name
    let success ← destructAndExpr h
    if ! success then
      failure)

elab "destruct_and" h:ident : tactic =>
  destructAnd (h.getId)


theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) : a :=
  by destruct_and h



def isTheorem : ConstantInfo → Bool
| ConstantInfo.axiomInfo _ => true
| ConstantInfo.thmInfo _=> true
| _ => false

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal => MVarId.apply goal cst)

-- The next function implements a combinator that behaves like <;> but that can
-- be used from a metaprogram:
def andThenOnSubgoals' (tac1 tac2 : TacticM Unit) : TacticM Unit :=
  do
    let origGoals ← getGoals
    let mainGoal ← getMainGoal
    setGoals [mainGoal]
    tac1
    let subgoals1 ← getUnsolvedGoals
    let mut newGoals := []
    for subgoal in subgoals1 do
      let assigned ← MVarId.isAssigned subgoal
      if ! assigned
      then
        setGoals [subgoal]
        tac2
        let subgoals2 ← getUnsolvedGoals
        newGoals := newGoals ++ subgoals2
    setGoals (newGoals ++ List.tail origGoals)


def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals' (applyConstant name) hypothesis


def proveDirect : TacticM Unit :=
  do
    let origGoals ← getUnsolvedGoals
    let goal ← getMainGoal
    setGoals [goal]
    let env ← getEnv
    for (name, info)
        in SMap.toList (Environment.constants env) do
      if isTheorem info && ! ConstantInfo.isUnsafe info then
        try
          proveUsingTheorem name
          logInfo m!"Proved directly by {name}"
          setGoals (List.tail origGoals)
          return
        catch _ =>
          continue
    failure

elab "prove_direct" : tactic =>
  proveDirect

-- set_option maxHeartbeats 1000000000
-- theorem Nat.symm (x y : ℕ) (h : y = x): x = y :=
--   by prove_direct
