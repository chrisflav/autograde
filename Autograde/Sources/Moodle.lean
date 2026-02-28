import Cli.Basic
import Lake.CLI.Main

set_option autoImplicit false

open Cli

namespace Moodle

structure Args where
  inputDir : System.FilePath
  outputDir : System.FilePath

def Args.fromParsed (p : Parsed) : Option Args := do
  let input : System.FilePath := (← p.positionalArg? "input").value
  let output : System.FilePath := (← p.positionalArg? "output").value
  some { inputDir := input, outputDir := output }

structure FillArgs where
  graderCsv : System.FilePath
  targetCsv : System.FilePath
  outputCsv : System.FilePath

def FillArgs.fromParsed (p : Parsed) : Option FillArgs := do
  let g : System.FilePath := (← p.positionalArg? "graderCsv").value
  let t : System.FilePath := (← p.positionalArg? "targetCsv").value
  let o : System.FilePath := (← p.positionalArg? "outputCsv").value
  some { graderCsv := g, targetCsv := t, outputCsv := o }

end Moodle

open Moodle

def parseDirName (name : String) : Option (Nat × String) := do
  let stNo ← (← (name.splitOn "_")[1]?).toNat?
  let stName ← (name.splitOn "_")[0]?
  pure (stNo, stName)

def IO.FS.copyFile (source target : System.FilePath) : IO Unit := do
  _ ← IO.Process.output { cmd := "cp", args := #[source.toString, target.toString] }

def runMoodle (args : Args) : IO UInt32 := do
  let fps ← args.inputDir.readDir
  if !(← args.outputDir.isDir) && !(← args.outputDir.pathExists) then IO.FS.createDir args.outputDir
  if (← args.outputDir.pathExists) && (← args.outputDir.isDir) then
    for fp in fps do
      match ((← fp.path.readDir), parseDirName fp.fileName) with
      | (#[entry], some (stdNo, stdName)) =>
        IO.FS.copyFile entry.path <| args.outputDir / s!"{stdName}_{stdNo}.lean"
      | _ => pure ()
    return 0
  else
    IO.println s!"{args.outputDir} is not a directory. Exiting."
    return 1

/-- Recursive helper for `parseCsvLine`. -/
private partial def parseCsvLineAux :
    List Char → String → Bool → Array String → Array String
  | [], cur, _, acc => acc.push cur
  | '"' :: rest, cur, true, acc =>
    match rest with
    | '"' :: rest' => parseCsvLineAux rest' (cur.push '"') true acc
    | _ => parseCsvLineAux rest cur false acc
  | '"' :: rest, cur, false, acc => parseCsvLineAux rest cur true acc
  | ',' :: rest, cur, true, acc => parseCsvLineAux rest (cur.push ',') true acc
  | ',' :: rest, cur, false, acc => parseCsvLineAux rest "" false (acc.push cur)
  | c :: rest, cur, inQ, acc => parseCsvLineAux rest (cur.push c) inQ acc

/-- Parse a single CSV line into fields, respecting RFC 4180 quoting. -/
private def parseCsvLine (line : String) : Array String :=
  parseCsvLineAux line.toList "" false #[]

private def escapeCsvField (s : String) : String :=
  if s.contains ',' || s.contains '"' || s.contains '\n' then
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else
    s

private def csvLine (fields : List String) : String :=
  ",".intercalate (fields.map escapeCsvField)

/-- Find the index of the first element satisfying `pred`, or `none`. -/
private def findColIdx (arr : Array String) (pred : String → Bool) : Option Nat :=
  (arr.foldl (fun (i, acc) s => (i + 1, if pred s && acc.isNone then some i else acc)) (0, none)).2

def runFillGrades (args : FillArgs) : IO UInt32 := do
  -- Parse grader CSV (trimRight strips \r from Windows CRLF line endings)
  let graderContent ← IO.FS.readFile args.graderCsv
  let graderLines := graderContent.splitOn "\n" |>.filterMap fun s =>
    let s := s.trimRight; if s.isEmpty then none else some s
  if graderLines.isEmpty then
    IO.println "Error: grader CSV is empty."
    return 1
  let gHdr := parseCsvLine graderLines.head!
  let gRows := graderLines.drop 1
  -- Find required columns in grader CSV
  let some idCol := findColIdx gHdr (· == "Student ID") | do
    IO.println "Error: column \"Student ID\" not found in grader CSV."
    return 1
  let some ptCol := findColIdx gHdr (· == "Total Points") | do
    IO.println "Error: column \"Total Points\" not found in grader CSV."
    return 1
  let some fbCol := findColIdx gHdr (· == "Feedback") | do
    IO.println "Error: column \"Feedback\" not found in grader CSV."
    return 1
  -- Build lookup table: student ID string → (total points, feedback)
  let gradeMap : Array (String × String × String) :=
    gRows.toArray.filterMap fun row =>
      let f := parseCsvLine row
      match f[idCol]?, f[ptCol]?, f[fbCol]? with
      | some sid, some pts, some fb => some (sid.trim, pts, fb)
      | _, _, _ => none
  -- Parse target (Moodle gradebook) CSV (trimRight strips \r from Windows CRLF line endings)
  let targetContent ← IO.FS.readFile args.targetCsv
  let targetLines := targetContent.splitOn "\n" |>.filterMap fun s =>
    let s := s.trimRight; if s.isEmpty then none else some s
  if targetLines.isEmpty then
    IO.println "Error: target CSV is empty."
    return 1
  let tHdr := parseCsvLine targetLines.head!
  let tRows := targetLines.drop 1
  -- Find required columns in target CSV
  let some stNoCol := findColIdx tHdr (· == "Student number") | do
    IO.println "Error: column \"Student number\" not found in target CSV."
    return 1
  let some realCol := findColIdx tHdr (fun s => s.endsWith "(Real)") | do
    IO.println "Error: no column ending in \"(Real)\" found in target CSV."
    return 1
  let some fbOutCol := findColIdx tHdr (fun s => s.endsWith "(Feedback)") | do
    IO.println "Error: no column ending in \"(Feedback)\" found in target CSV."
    return 1
  -- DEBUG: show all IDs from each side to diagnose matching issues
  IO.println s!"DEBUG grader IDs: {gradeMap.toList.map (·.1)}"
  let allTargetIds := tRows.map fun row =>
    (parseCsvLine row)[stNoCol]?.getD "(missing)"
  IO.println s!"DEBUG target IDs: {allTargetIds}"
  -- For each target row, fill in grade and feedback if student is found in grader CSV
  let mut matchCount : Nat := 0
  let mut updatedRows : Array String := #[]
  for row in tRows do
    let fields := parseCsvLine row
    let stNo := (fields[stNoCol]?.getD "").trim
    match gradeMap.find? (fun (sid, _, _) => sid == stNo) with
    | none => updatedRows := updatedRows.push (csvLine fields.toList)
    | some (_, pts, fb) =>
      matchCount := matchCount + 1
      let updated := if realCol < fields.size then fields.set! realCol pts else fields
      let updated := if fbOutCol < updated.size then updated.set! fbOutCol fb else updated
      updatedRows := updatedRows.push (csvLine updated.toList)
  let output := "\n".intercalate (csvLine tHdr.toList :: updatedRows.toList) ++ "\n"
  IO.FS.writeFile args.outputCsv output
  IO.println s!"Matched {matchCount} of {gradeMap.size} graded students. Updated grades written to {args.outputCsv}."
  return 0

def moodleCLI (parsed : Parsed) : IO UInt32 := do
  let mayArgs := Args.fromParsed parsed
  match mayArgs with
    | some args => runMoodle args
    | none => IO.println "Invalid input." return 1

def fillGradesCLI (parsed : Parsed) : IO UInt32 := do
  let mayArgs := FillArgs.fromParsed parsed
  match mayArgs with
    | some args => runFillGrades args
    | none => IO.println "Invalid input." return 1

def grades := `[Cli|
  grades VIA fillGradesCLI; ["0.0.1"]
  "Fill total points and feedback from a grader CSV into a Moodle gradebook CSV,
  matching rows by student number."

  ARGS:
    graderCsv : String; "Path to the CSV produced by the grader (--csv output)."
    targetCsv : String; "Path to the Moodle gradebook CSV to update."
    outputCsv : String; "Path to write the updated CSV file."
]

def moodle := `[Cli|
  moodle VIA moodleCLI; ["0.0.1"]
  "Moodle integration."

  ARGS:
    input : String; "Path to directory containing moodle download"
    output : String; "Path to directory to put processed files in"

  SUBCOMMANDS:
    grades
]
