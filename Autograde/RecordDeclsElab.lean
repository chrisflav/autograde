import Autograde.EnvExtensions.DeclInfo

open Lean Elab Command

def Lean.ConstantInfo.getConstantVal? : ConstantInfo → Option ConstantVal
  | .thmInfo val => val.toConstantVal
  | .defnInfo val => val.toConstantVal
  | _ => none

def Lean.Name.isRelevant (name : Name) : Bool :=
  !((Lean.privateToUserName? name).getD name).isInternal

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

def getCurrDeclInfo : CommandElabM DeclInfo := do
  let ts ← getInfoTrees
  let declName : Name := (getAllNames ts).toArray[0]!
  let tactics := (getAllTactics ts).toArray
  let val ← (← getConstInfo declName).getConstantVal?.getDM <| throwError "Unsupported declaration type"
  let axs := ((((CollectAxioms.collect declName).run (← getEnv)).run {}).2).axioms
  pure { name := declName, type := val.type, axiomsUsed := axs, tacticsUsed := tactics }

@[command_elab declaration]
def appendDeclInfo : CommandElab := fun
| `($dms:declModifiers example $sig:optDeclSig $val:declVal) => do
  let name ← mkAuxName `example 1
  elabDeclaration <| ← `($dms:declModifiers def $(mkIdent name) $sig:optDeclSig $val:declVal)
  addDeclInfo (← getCurrDeclInfo)
| stx => do
  elabDeclaration stx
  addDeclInfo (← getCurrDeclInfo)
