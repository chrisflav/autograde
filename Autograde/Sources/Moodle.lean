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

def moodleCLI (parsed : Parsed) : IO UInt32 := do
  let mayArgs := Args.fromParsed parsed
  match mayArgs with
    | some args => runMoodle args
    | none => IO.println "Invalid input." return 1

def moodle := `[Cli|
  moodle VIA moodleCLI; ["0.0.1"]
  "Fetch moodle"

  ARGS:
    input : String; "Path to directory containing moodle download"
    output : String; "Path to directory to put processed files in"
]
