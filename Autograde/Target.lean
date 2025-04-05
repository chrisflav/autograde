import Lean.Elab.Tactic.Simp
import Lean.Elab.App

open Lean

def standardAxioms : Array Name :=
  #[`propext, `Quot.sound, `Classical.choice]

structure GradingTargetConfig where
  allowedAxioms      : Array Name := standardAxioms
  /-- Declarations that this target may use without proof (e.g. axioms used for proving the
  allowed prerequisites are not counted as used axioms). -/
  allowedPrerequisites : Array Name := #[]
  points             : Nat := 0
  deriving Inhabited, BEq, Hashable, Repr

instance : ToString GradingTargetConfig where
  toString := toString ∘ repr

/-- Function elaborating `GradingTargetConfig` -/
declare_command_config_elab elabGradingTargetConfig GradingTargetConfig

structure GradingTarget extends GradingTargetConfig where
  name : Name
  expr : Expr
  allowedPrerequisitesTypes : Array Expr := #[]
  deriving BEq, Hashable, Repr

/-- An exam is simply a list of grading targets. -/
abbrev Exam : Type :=
  Array GradingTarget

instance : ToString GradingTarget where
  toString := toString ∘ repr

inductive AnalysisResult where
  | fail
  | success (decl : Name)
  /-- A list of candidates with obstructions, for now the only possible obstruction is
  a list of used, but forbidden axioms. -/
  -- TODO: replace `List` by `Array`
  | part (candidates : List (Name × Array (Name × List Name)))

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

def renderAnalysisResults (exam : Exam) (results : Array AnalysisResult) : String :=
  let excs := "\n".intercalate
    (Array.zipWith
      (fun exc res ↦ s!"{exc.name}: {res} => {res.points (.ofNat exc.points)} / {Float.ofNat exc.points}")
      exam results).toList
  let totalRes : Float × Float := (Array.zip exam results).foldl (fun acc (exc, res) ↦
    (acc.1 + .ofNat exc.points, acc.2 + res.points (.ofNat exc.points))) (0, 0)
  let footer := s!"total: {totalRes.2} / {totalRes.1}"
  s!"{excs}\n{footer}"
