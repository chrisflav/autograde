import Autograde.Declaration

open Lean Elab Command

initialize declInfoExt : SimplePersistentEnvExtension DeclInfo (Std.HashSet DeclInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn as := as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addDeclInfo {m : Type → Type} [MonadEnv m] (info : DeclInfo) : m Unit :=
  modifyEnv (declInfoExt.addEntry · info)

def getDeclInfos {m : Type → Type} [Monad m] [MonadEnv m] : m (Std.HashSet DeclInfo) := do
  return declInfoExt.getState (← getEnv)

elab "#declinfos" : command => do
  let decls ← getDeclInfos
  logInfo s!"{decls.toArray.toList}"
