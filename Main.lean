import Cli.Basic
import Autograde.EnvExtensions.DeclInfo
import Autograde.EnvExtensions.GradeAttr
import Autograde.Target
import Lake.CLI.Main

set_option autoImplicit false

open Lean System.FilePath Elab Command

structure Submission where
  path : System.FilePath
  studentNumber : Nat
  studentName : String
deriving Repr

abbrev Exam : Type :=
  Array GradingTarget

structure GradedSubmission (exam : Exam) extends Submission where
  results : Array AnalysisResult

instance : ToString Submission where
  toString := ToString.toString ∘ repr

def renderAnalysisResults (exam : Exam) (results : Array AnalysisResult) : String :=
  "\n".intercalate (Array.zipWith (fun exc res ↦ s!"{exc.name}: {res}") exam results).toList

def GradedSubmission.render {exam : Exam} (sub : GradedSubmission exam) : String :=
  let res := renderAnalysisResults exam sub.results
  s!"Submission by {sub.studentName} ({sub.studentNumber}):\n{res}"

structure GradingContext where
  toModule : Submission → Name

-- TODO: make this configurable
def Submission.module (s : Submission) : Name :=
  s!"Autograde.Targets.sub{s.studentNumber}".toName

def Submission.buildPath (s : Submission) : System.FilePath :=
  s!"Autograde/Targets/sub{s.studentNumber}.lean"

inductive Mode where
  | single (module : System.FilePath)
  | directory (path : System.FilePath)

structure Args where
  exerciseModule : Name
  mode : Mode
  preprocessOnly : Bool
  workingDirectory : Name

def Args.fromParsed (args : Cli.Parsed) : Option Args := do
  let preprocess : Bool := false
  let exercise : Name ← (← args.flag? "exercises").value.toName
  let workingDir : Name ← (← args.flag? "workingDirectory").value.toName
  let mode : Mode ← match args.flag? "directory", args.flag? "module" with
    | some path, _ => pure <| Mode.directory path.value
    | none, some name => pure <| .single name.value
    | none, none => none
  let args : Args :=
    { exerciseModule := exercise
      mode := mode
      preprocessOnly := preprocess
      workingDirectory := workingDir }
  some args

def Lean.Name.toFilePath (nm : Name) : System.FilePath :=
  s!"{nm.toString.replace "." "/"}.lean"

def preprocessFiles (exerciseModule : Name)
    (inputOutputs : Array (System.FilePath × Name)) : IO UInt32 := do
  let mut args := #["build", exerciseModule.toString]
  for (path, name) in inputOutputs do
    let inp ← IO.FS.readFile path
    let out : String := s!"import Autograde.RecordDeclsElab\n{inp}"
    IO.FS.writeFile name.toFilePath out
    args := args.append #[name.toString]
  let cfg ← IO.Process.spawn { cmd := "lake", args := args }
  IO.Process.Child.wait cfg

def gradeModule (exEnv : Environment) (targets : Array GradingTarget)
    (module : Name) : IO (Array AnalysisResult) := do
  _ ← initSearchPath ""
  let env ← importModules #[module] {} (trustLevel := 1024)
  let decls := declInfoExt.getState env |>.toArray
  let mut results : Array AnalysisResult := #[]
  for target in targets do
    let mut res : AnalysisResult := .fail
    for decl in decls do
      if Kernel.isDefEqGuarded exEnv default target.expr decl.type then
        let bad := decl.axiomsUsed.filter (fun a ↦ a ∉ target.allowedAxioms)
        if bad.isEmpty then res := .success decl.name
          else
            let upd : AnalysisResult → AnalysisResult
              | .part cs => .part <| (decl.name, bad) :: cs
              | .fail => .part [(decl.name, bad)]
              | x => x
            res := upd res
    results := results ++ #[res]
  return results

def gradeSubmission (ctxt : GradingContext) (exEnv : Environment) (exam : Exam) (sub : Submission) :
    IO (GradedSubmission exam) := do
  let res ← gradeModule exEnv exam (ctxt.toModule sub)
  return { sub with results := res }

-- TODO: this should return `Option Submission`
def parseMoodleFileName (entry : IO.FS.DirEntry) : Submission where
  path := entry.path
  studentNumber := (entry.fileName.splitOn "_")[1]!.toNat!
  studentName := (entry.fileName.splitOn "_")[0]!

def parseSubmission (fp : IO.FS.DirEntry) : Option Submission := do
  let name ← (fp.fileName.splitOn ".lean")[0]?
  let stNo ← (← (name.splitOn "_")[1]?).toNat?
  let stName ← (name.splitOn "_")[0]?
  pure { path := fp.path, studentNumber := stNo, studentName := stName }

def Args.defaultContext (args : Args) : GradingContext where
  toModule s := s!"{args.workingDirectory}.sub{s.studentNumber}".toName

def runGrade (args : Args) : IO UInt32 := do
  _ ← initSearchPath ""
  let exEnv ← importModules #[args.exerciseModule] {}
  let exam : Exam := gradingTargetExt.getState exEnv |>.toArray
  let ctxt : GradingContext := args.defaultContext
  match args.mode with
  | .single path =>
      let module : Name := s!"{args.workingDirectory}.sub".toName
      if args.preprocessOnly then
        preprocessFiles args.exerciseModule #[(path, module)]
      else
        let ret ← preprocessFiles args.exerciseModule #[(path, module)]
        if ret != 0 then
          IO.println "Failed during preprocessing. Exiting."
          return ret
        else
          let res ← gradeModule exEnv exam module
          IO.println <| renderAnalysisResults exam res
          return 0
  | .directory path =>
      IO.println s!"Processing directory at {path}."
      let submissions := (← path.readDir).filterMap parseSubmission
      IO.println s!"{submissions}"
      let ret ← preprocessFiles args.exerciseModule <|
        submissions.map fun s ↦ (s.path, ctxt.toModule s)
      if ret != 0 then
        IO.println "Failed during preprocessing. Exiting."
        return ret
      else
        for sub in submissions do
          let res ← gradeSubmission ctxt exEnv exam sub
          IO.println res.render
        return 0

open IO.FS IO.Process Name Cli in
def gradeCLI (parsed : Parsed) : IO UInt32 := do
  let mayArgs := Args.fromParsed parsed
  match mayArgs with
    | some args => runGrade args
    | none => IO.println "Invalid input." return 1

open Cli in
/-- Setting up command line options and help text for `lake exe grade`. -/
def gradeCmd : Cmd := `[Cli|
  grade VIA gradeCLI; ["0.0.1"]
  "Automatically grade a .lean exercise."

  FLAGS:
    preprocess_only : Bool; "Run preprocessing only."
    exercises : String; "The module containing the exercises."
    directory : String; "Directory containing the submissions."
    module : String; "A single module. `directory` and `module` can't both be present."
    workingDirectory : String; ""
]

/-- The entrypoint to the `lake exe grade` command. -/
def main (args : List String) : IO UInt32 := gradeCmd.validate args
