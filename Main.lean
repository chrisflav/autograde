import Cli.Basic
import Autograde.EnvExtensions.DeclInfo
import Autograde.EnvExtensions.GradeAttr
import Autograde.Target
import Autograde.Sources.Moodle
import Autograde.Grade
import Lake.CLI.Main

set_option autoImplicit false

open Lean System.FilePath Elab Command Autograde

structure Submission where
  path : System.FilePath
  studentNumber : Nat
  studentName : String
deriving Repr

structure GradedSubmission (exam : Exam) extends Submission where
  results : Array AnalysisResult

instance : ToString Submission where
  toString := ToString.toString ∘ repr

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
  csvOutput : Option String

def Args.fromParsed (args : Cli.Parsed) : Option Args := do
  let preprocess : Bool := false
  let exercise : Name ← (← args.flag? "exercises").value.toName
  let workingDir : Name ← (← args.flag? "workingDirectory").value.toName
  let mode : Mode ← match args.flag? "directory", args.flag? "module" with
    | some path, _ => pure <| Mode.directory path.value
    | none, some name => pure <| .single name.value
    | none, none => none
  let csv : Option String := args.flag? "csv" |>.map (·.value)
  let args : Args :=
    { exerciseModule := exercise
      mode := mode
      preprocessOnly := preprocess
      workingDirectory := workingDir
      csvOutput := csv }
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

-- The core lean function only allows `loadExts := false` here
unsafe def withImportModulesWithExt {α : Type} (imports : Array Import) (opts : Options)
    (act : Environment → IO α) (trustLevel : UInt32 := 0) : IO α := do
  let env ← importModules (loadExts := true) imports opts trustLevel
  try act env finally env.freeRegions

unsafe def gradeModule (exEnv : Environment) (targets : Array GradingTarget)
    (module : Name) : IO (Array AnalysisResult) := do
  _ ← initSearchPath ""
  withImportModulesWithExt #[{ module := module }] {} (trustLevel := 1024) <| fun env ↦
    return gradeEnv exEnv env targets

unsafe def gradeSubmission (ctxt : GradingContext) (exEnv : Environment) (exam : Exam) (sub : Submission) :
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

private def escapeCsvField (s : String) : String :=
  if s.contains ',' || s.contains '"' || s.contains '\n' then
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else
    s

/-- Format the violations of a partial solution as a human-readable comment.
Each violation shows the forbidden axiom and the declaration chain leading to it. -/
private def analysisResultComment (res : AnalysisResult) : String :=
  match res with
  | .fail | .success _ => ""
  | .part candidates =>
    let parts := candidates.map fun (declName, violations) =>
      let vs := violations.toList.map fun (ax, path) =>
        let chain := " → ".intercalate (path.reverse.map (fun n : Name => n.toString) ++ [ax.toString])
        s!"uses `{ax}` via {chain}"
      s!"`{declName}`: " ++ "; ".intercalate vs
    "; ".intercalate parts

private def csvLine (fields : List String) : String :=
  ",".intercalate (fields.map escapeCsvField)

private def writeCSV (path : String) (exam : Exam)
    (submissions : Array (GradedSubmission exam)) : IO Unit := do
  let header := csvLine <|
    ["Student Name", "Student ID", "Total Points", "Feedback"] ++
    exam.toList.flatMap fun tgt =>
      [s!"{tgt.name} Points", s!"{tgt.name} Comments"]
  let rows := submissions.toList.map fun (sub : GradedSubmission exam) =>
    let total : Float := (Array.zip exam sub.results).foldl
      (fun acc (exc, res) => acc + res.points (.ofNat exc.points)) 0
    let exCols := (Array.zip exam sub.results).toList.flatMap fun (exc, res) =>
      [s!"{res.points (.ofNat exc.points)}", analysisResultComment res]
    csvLine ([sub.studentName, s!"{sub.studentNumber}", s!"{total}", ""] ++ exCols)
  IO.FS.writeFile path ("\n".intercalate (header :: rows) ++ "\n")

unsafe def runGrade (args : Args) : IO UInt32 := do
  _ ← initSearchPath ""
  let exEnv ← importModules (loadExts := true) #[args.exerciseModule] {}
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
      let ret ← preprocessFiles args.exerciseModule <|
        submissions.map fun s ↦ (s.path, ctxt.toModule s)
      if ret != 0 then
        IO.println "Failed during preprocessing. Exiting."
        return ret
      else
        IO.println "Preprocessing completed."
        let mut gradedSubs : Array (GradedSubmission exam) := #[]
        for sub in submissions do
          let res ← gradeSubmission ctxt exEnv exam sub
          IO.println res.render
          gradedSubs := gradedSubs.push res
        if let some csvPath := args.csvOutput then do
          writeCSV csvPath exam gradedSubs
          IO.println s!"CSV results written to {csvPath}."
        return 0

open IO.FS IO.Process Name Cli in
unsafe def gradeCLI (parsed : Parsed) : IO UInt32 := do
  let mayArgs := Args.fromParsed parsed
  match mayArgs with
    | some args => runGrade args
    | none => IO.println "Invalid input." return 1

open IO.FS IO.Process Name Cli in
def sourcesCLI (_ : Parsed) : IO UInt32 := do
  IO.println "hi"
  return 1

def sources := `[Cli|
  sources VIA sourcesCLI; ["0.0.1"]
  "Fetch sources"

  SUBCOMMANDS:
    moodle
]

open Cli in
/-- Setting up command line options and help text for `lake exe grade`. -/
unsafe def gradeCmd : Cmd := `[Cli|
  grade VIA gradeCLI; ["0.0.1"]
  "Automatically grade a .lean exercise."

  FLAGS:
    preprocess_only : Bool; "Run preprocessing only."
    exercises : String; "The module containing the exercises."
    directory : String; "Directory containing the submissions."
    module : String; "A single module. `directory` and `module` can't both be present."
    workingDirectory : String; ""
    csv : String; "Path to write CSV output (directory mode only)."

  SUBCOMMANDS:
    sources
]

/-- The entrypoint to the `lake exe grade` command. -/
unsafe def main (args : List String) : IO UInt32 := gradeCmd.validate args
