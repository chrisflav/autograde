import Autograde.Basic
import Autograde.Target

namespace Autograde

open Lean Elab

initialize gradingTargetExt : SimplePersistentEnvExtension GradingTarget (Std.HashSet GradingTarget) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addGradingTarget {m : Type → Type} [MonadEnv m] (cfg : GradingTarget) : m Unit :=
  modifyEnv (gradingTargetExt.addEntry · cfg)

def getGradingTargets {m : Type → Type} [MonadEnv m] [Monad m] : m (Array GradingTarget) := do
  let env ← getEnv
  return (gradingTargetExt.getState env).toArray

open Parser

syntax gradeArgsRest := Tactic.optConfig (ppSpace ident)*

syntax (name := grade) "grade" gradeArgsRest : attr

initialize Lean.registerBuiltinAttribute {
  name := `grade
  descr := "Add grading target."
  add := fun decl stx _attrKind => do
    match stx with
    | `(attr| grade $c:optConfig) =>
      let cfg ← liftCommandElabM <| elabGradingTargetConfig c
      let info ← getConstInfo decl
      let val ← info.getConstantVal?.getDM <| throwError "Unsupported declaration type."
      let prereqTypes : Array Expr ←
        cfg.allowedPrerequisites.filterMapM $ fun decl ↦ do
          return ConstantVal.type <$> (← getConstInfo decl).getConstantVal?
      let target : GradingTarget :=
        { cfg with name := decl, expr := val.type, allowedPrerequisitesTypes := prereqTypes }
      addGradingTarget target
    | _ => throwUnsupportedSyntax
}

elab "#gradingtargets" : command => do
  logInfo s!"{← getGradingTargets}"

end Autograde
