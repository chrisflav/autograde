import Autograde.Basic
import Autograde.EnvExtensions.DeclInfo
import Autograde.AxiomBlame

open Lean Elab Command

partial
def scanInfoTree : InfoTree → NameSet
  | .context (.parentDeclCtx i) t => (scanInfoTree t).insert i
  | .context _ t => (scanInfoTree t)
  | .node _ ts => ts.toArray.foldl (init := ∅) (·.union <| scanInfoTree ·)
  | .hole .. => ∅

def getAllNames (ts : PersistentArray InfoTree) : NameSet :=
  ts.toArray.map scanInfoTree |>.foldl .union ∅

partial def scanForTactics : InfoTree → NameSet
  | .context _ t => scanForTactics t
  | .node (.ofTacticInfo i) ts =>
    let ns : NameSet := (ts.toArray.foldl (init := ∅) (·.union <| scanForTactics ·))
    ns.insert i.elaborator
  | .node _ ts => ts.toArray.foldl (init := ∅) (·.union <| scanForTactics ·)
  | .hole .. => ∅

def getAllTactics (ts : PersistentArray InfoTree) : NameSet :=
  ts.toArray.map scanForTactics |>.foldl .union ∅

def getCurrDeclInfo : CommandElabM (Option DeclInfo) := do
  let ts ← getInfoTrees
  let declName : Name := (getAllNames ts).toArray[0]!
  let tactics := (getAllTactics ts).toArray
  match (← getConstInfo declName).getConstantVal? with
  | some val =>
    let axs := getAxiomPathsWithTypes (← getEnv) declName
    return some { name := declName, type := val.type, axiomsUsed := axs, tacticsUsed := tactics }
  | none => return none

@[command_elab declaration]
def appendDeclInfo : CommandElab := fun
| `($dms:declModifiers example $sig:optDeclSig $val:declVal) => do
  let baseName := (← getCurrNamespace) ++ `example
  let name := `_root_ ++ (← mkAuxName baseName 1)
  elabDeclaration <| ← `($dms:declModifiers def $(mkIdent name) $sig:optDeclSig $val:declVal)
  match (← getCurrDeclInfo) with
  | some info => addDeclInfo info
  | none => pure ()
| stx => do
  elabDeclaration stx
  match (← getCurrDeclInfo) with
  | some info => addDeclInfo info
  | none => pure ()

macro "stop_recording" : command => do
  `(
    attribute [-command_elab] appendDeclInfo
  )

macro "resume_recording" : command => do
  let declKind := mkIdent `declaration
  `(
    attribute [local command_elab $declKind] appendDeclInfo
  )
