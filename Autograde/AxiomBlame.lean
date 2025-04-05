import Autograde.Basic
import Lean

/-!
# Compute axiom path of shame of a declaration

This file provides functions to compute all paths of shame of a declaration, i.e. the sequence of
intermediate declarations ending in the invocation of an axiom.

This is adapted from a code snippet by Kyle Miller on Zulip:
https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Finding.20usages.20of.20.60sorry.60.20in.20external.20code/near/430509619
-/

open Lean Elab Command

namespace CollectAxiomBlame

structure State where
  visited : NameSet      := {}
  dirty   : NameMap (Array (Name × List Name)) := {}
  axioms  : Array (Name × List Name) := {}

abbrev M := ReaderT Environment $ StateM State

partial def collect (src : List Name) (c : Name) : M Unit := do
  let collectExpr (src' : List Name) (e : Expr) : M Unit := e.getUsedConstants.forM (collect src')
  let s ← get
  if ! s.visited.contains c then do
    let env ← read
    let src' := c :: src
    if !(env.find? c).elim false (fun ci ↦ ci.isAxiom) then
      modify fun s => { s with visited := s.visited.insert c }
    if (env.getModuleIdxFor? c).isNone || (env.find? c).elim false (fun ci ↦ ci.isAxiom) then
    match env.find? c with
    | some (ConstantInfo.axiomInfo _)  =>
      let newDirty : NameMap (Array (Name × List Name)) :=
        (src.foldl
          (fun old n ↦ (n :: old.1, .mergeBy
            (fun _ inserting existing ↦ inserting ++ existing)
            (.fromList [(n, #[(c, old.1)])] _) old.2)) (([] : List Name), s.dirty)).2
      modify fun s => { s with axioms := s.axioms.push (c, src), dirty := newDirty }
    | some (ConstantInfo.defnInfo v)   => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.thmInfo v)    => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.quotInfo _)   => pure ()
    | some (ConstantInfo.ctorInfo v)   => collectExpr src' v.type
    | some (ConstantInfo.recInfo v)    => collectExpr src' v.type
    | some (ConstantInfo.inductInfo v) => collectExpr src' v.type *> v.ctors.forM (collect src')
    | none                             => pure ()
  else
    match s.dirty.find? c with
    | none => pure ()
    | some axs =>
      for (ax, path) in axs do
        modify fun s => { s with axioms := s.axioms.push (ax, path ++ c :: src) }

end CollectAxiomBlame

/-- Returns an array of all transitively used axioms with the path of shame. -/
def getAxiomPaths (env : Environment) (decl : Name) : Array (Name × List Name) :=
  (((CollectAxiomBlame.collect [] decl).run env).run {}).2.axioms

/-- Returns an array of all transitively used axioms with the path of shame, as
a list of expressions representing the type of the declaration. -/
def getAxiomPathsWithTypes (env : Environment) (decl : Name) : Array (Name × List ConstantVal) :=
  let axPaths := getAxiomPaths env decl
  let getType (decl : Name) : ConstantVal := match env.find? decl with
    | some (.thmInfo val) => val.toConstantVal
    | some (.defnInfo val) => val.toConstantVal
    | some (.opaqueInfo val) => val.toConstantVal
    | some (.ctorInfo val) => val.toConstantVal
    | some (.recInfo val) => val.toConstantVal
    | some (.inductInfo val) => val.toConstantVal
    | some _ => panic "[getAxiomPathsWithTypes]: unsupported declaration type in axiom path of shame"
    | _ => panic "[getAxiomPathsWithTypes]: constant recorded in axiom path of shame could not be found in the environment"
  axPaths.map $ fun (name, path) => (name, path.map getType)

elab "#axiom_blame " id:ident : command => Elab.Command.liftTermElabM do
  let n ← Elab.realizeGlobalConstNoOverloadWithInfo id
  Elab.addCompletionInfo <| .id id id.getId (danglingDot := false) {} none
  let env ← getEnv
  let axioms := getAxiomPaths env n
  if axioms.isEmpty then
    logInfo m!"'{n}' does not depend on any axioms"
  else
    let mut msgs := #[]
    for (ax, decls) in axioms do
      msgs := msgs.push m!"* {ax}: {MessageData.joinSep ((ax :: decls).reverse.map toMessageData) " → "}"
    logInfo m!"'{n}' depends on axioms:\n\n{MessageData.joinSep msgs.toList "\n\n"}"

section Test

axiom mySorry : False
axiom myAxiom : False

theorem bli : False := mySorry
theorem bla : False := bli
theorem foo : True := myAxiom.elim
theorem bar : False := bla

theorem foobar : True ∧ False :=
  have := mySorry
  ⟨foo, bla⟩

/--
info: 'foobar' depends on axioms:

* mySorry: foobar → mySorry

* myAxiom: foobar → foo → myAxiom

* mySorry: foobar → bla → bli → mySorry
-/
#guard_msgs in
#axiom_blame foobar

end Test
