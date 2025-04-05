import Autograde.EnvExtensions.DeclInfo
import Autograde.EnvExtensions.GradeAttr
import Autograde.Target
import Autograde.AxiomBlame

open Lean Elab Command

namespace Autograde

set_option autoImplicit false

def gradeEnv (exEnv env : Environment) (targets : Array GradingTarget) :
    Array AnalysisResult := Id.run do
  let decls := declInfoExt.getState env |>.toArray
  let mut results : Array AnalysisResult := #[]
  for target in targets do
    let mut res : AnalysisResult := .fail
    for decl in decls do
      if Kernel.isDefEqGuarded exEnv default target.expr decl.type then
        let bad := decl.axiomsUsed.filter
          (fun a ↦ a.1 ∉ target.allowedAxioms ∧
            a.2.all (fun dependency ↦ target.allowedPrerequisitesTypes.all <| fun allowed ↦
              !Kernel.isDefEqGuarded exEnv default dependency.type allowed))
        if bad.isEmpty then res := .success decl.name.toString.toName
          else
            let candidate : Name × Array (Name × List Name) :=
              (decl.name.toString.toName,
                bad.map (fun x ↦ (x.1.toString.toName, x.2.map (fun val ↦ val.name.toString.toName))))
            let upd : AnalysisResult → AnalysisResult
              | .part cs => .part <| candidate :: cs
              | .fail => .part [candidate]
              | x => x
            res := upd res
    results := results ++ #[res]
  return results

elab "#grade" : command => do
  let exam : Exam ← getGradingTargets
  let env ← getEnv
  let res := gradeEnv env env exam
  logInfo (renderAnalysisResults exam res)

end Autograde
