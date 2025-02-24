import Lean.Elab.Tactic.Simp
import Lean.Elab.App

open Lean

def standardAxioms : Array Name :=
  #[`propext, `Quot.sound, `Classical.choice]

structure GradingTargetConfig where
  allowedAxioms : Array Name := standardAxioms
  points : Nat := 0
  deriving Inhabited, BEq, Hashable, Repr

instance : ToString GradingTargetConfig where
  toString := toString ∘ repr

/-- Function elaborating `GradingTargetConfig` -/
declare_command_config_elab elabGradingTargetConfig GradingTargetConfig

structure GradingTarget extends GradingTargetConfig where
  name : Name
  expr : Expr
  deriving BEq, Hashable, Repr

instance : ToString GradingTarget where
  toString := toString ∘ repr

inductive AnalysisResult where
  | fail
  | success (decl : Name)
  /-- A list of candidates with obstructions, for now the only possible obstruction is
  a list of used, but forbidden axioms. -/
  -- TODO: replace `List` by `Array`
  | part (candidates : List (Name × Array Name))

instance : ToString AnalysisResult where
  toString
    | .fail => "Fail: No solution found."
    | .success decl => s!"Success: Solved by {decl}."
    | .part candidates => s!"Partial solutions: {candidates}"

def AnalysisResult.points (res : AnalysisResult) (maxPoints : Float) : Float :=
  match res with
  | .fail => 0
  | .success _ => maxPoints
  | .part _ => maxPoints / 2
